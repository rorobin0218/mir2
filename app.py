from flask import Flask, jsonify, request, send_from_directory, Response
from concurrent.futures import ThreadPoolExecutor, as_completed
import requests
import json
import os
import urllib3
import threading
import time
import queue
from urllib.parse import urlparse
import base64

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

app = Flask(__name__)
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
SITES_FILE = os.path.join(BASE_DIR, 'sites.json')
LAST_FILE = os.path.join(BASE_DIR, 'last_found.json')

DEFAULT_SITES = [
    {"id":1,"name":"짭사이트","prefix":"zzap","suffix":".com","start":1,"end":999,"pad":3}
]

# ⑤ 스레드별 독립 세션 (Thread-local) - 동시성 문제 방지
_thread_local = threading.local()

def get_session():
    if not hasattr(_thread_local, 'session'):
        s = requests.Session()
        s.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
            'Accept-Language': 'ko-KR,ko;q=0.9,en-US;q=0.8',
            'Connection': 'keep-alive',
        })
        _thread_local.session = s
    return _thread_local.session

_prefetch_cache = {}
_prefetch_lock = threading.Lock()
_prefetch_running = set()
_prefetch_cancelled = set()  # 초기화된 사이트 ID - 완료돼도 캐시 저장 안 함
_user_set = {}  # 사용자가 수동 저장한 번호 {site_id: num} - 프리페치가 덮어쓰기 불가

def load_sites():
    if os.path.exists(SITES_FILE):
        with open(SITES_FILE, 'r', encoding='utf-8') as f:
            return json.load(f)
    return DEFAULT_SITES

def save_sites(sites):
    with open(SITES_FILE, 'w', encoding='utf-8') as f:
        json.dump(sites, f, ensure_ascii=False, indent=2)

def load_last():
    if os.path.exists(LAST_FILE):
        try:
            with open(LAST_FILE, 'r', encoding='utf-8') as f:
                content = f.read().strip()
                if content:
                    return json.loads(content)
        except (json.JSONDecodeError, IOError):
            # 파일 깨진 경우 백업에서 복구 시도
            backup = LAST_FILE + '.bak'
            if os.path.exists(backup):
                try:
                    with open(backup, 'r', encoding='utf-8') as f:
                        return json.load(f)
                except:
                    pass
    return {}

def save_last(data):
    tmp = LAST_FILE + '.tmp'
    backup = LAST_FILE + '.bak'
    try:
        # 1. 임시 파일에 먼저 쓰기
        with open(tmp, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
            f.flush()
            os.fsync(f.fileno())
        # 2. 기존 파일을 백업으로 이동
        if os.path.exists(LAST_FILE):
            try:
                os.replace(LAST_FILE, backup)
            except Exception:
                pass
        # 3. 임시 파일을 정식 파일로 교체
        os.replace(tmp, LAST_FILE)
    except Exception as e:
        # fallback: 직접 쓰기
        try:
            with open(LAST_FILE, 'w', encoding='utf-8') as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        except Exception as e2:
            print(f'save_last 오류: {e2}')

def make_url(site, num):
    pad = site.get('pad', 0)
    num_str = str(num).zfill(pad) if pad else str(num)
    return f"https://{site['prefix']}{num_str}{site['suffix']}/"

# ISP/정부 차단 페이지 도메인 목록
# 이 도메인으로 리다이렉트되면 "KT/ISP가 막은 것" → 도메인 자체는 살아있으므로 OK
ISP_BLOCK_HOSTS = {
    'warninge.kcopa.or.kr',
    'warning.kcopa.or.kr',
    'kcopa.or.kr',
    'warning.or.kr',
    'blocked.or.kr',
    'safenet.or.kr',
}

# 완전히 다른 서비스로 넘어가는 경우 → FAIL
UNRELATED_HOSTS = {
    't.me',
    'telegram.me',
    'dnsguide.shop',
    'cf.trekpeak.site',   # 광고/경유 페이지
    'trekpeak.site',
}

# 최종 URL 경로 패턴 → FAIL (경유/광고 페이지)
UNRELATED_PATH_PATTERNS = [
    '/middle.html',
    '/redirect',
    '/go.php',
    '/out.php',
    '/click.php',
]

# 파킹/준비 중 페이지 키워드 → 도메인은 등록됐지만 실제 사이트 없음 → FAIL
PARKED_KEYWORDS = [
    'hostinger.com',
    'hpanel.hostinger.com',
    'Registered at',
    'parked-domain',
    'Start your online journey',
    'This domain is for sale',
    'Buy this domain',
    'domain is parked',
    'GoDaddy',
    'namecheap.com',
    'domain parking',
    'sedo.com',
    'hugedomains.com',
    'dan.com',
    'afternic.com',
    'Manage domain',          # Hostinger 파킹 페이지
    'hpanel.hostinger',
    'Under Construction',
    'article:published_time',   # 무작위 텍스트 파킹 페이지
    'Agifihyb',                 # 파킹 스팸 텍스트 패턴 (랜덤 단어)
]

def is_same_family(original_host, final_host, site=None):
    if final_host == original_host:
        return True
    # www. 붙은 경우 같은 사이트로 허용 (예: mzgtv08.com → www.mzgtv08.com)
    if final_host == 'www.' + original_host or original_host == 'www.' + final_host:
        return True
    if site:
        prefix = site.get('prefix', '')
        suffix = site.get('suffix', '').lstrip('.')
        if final_host.startswith(prefix) and final_host.endswith(suffix):
            return True
        # www. 붙은 계열도 허용
        if final_host.startswith('www.' + prefix) and final_host.endswith(suffix):
            return True
    orig_base = original_host.rsplit('.', 1)[0].rstrip('0123456789')
    final_base = final_host.rsplit('.', 1)[0].rstrip('0123456789')
    if orig_base and orig_base == final_base and original_host.split('.')[-1] == final_host.split('.')[-1]:
        return True
    return False

def _extract_num(host, site):
    """도메인에서 번호 추출. 예: tvwiki26.net → 26"""
    try:
        prefix = site.get('prefix', '')
        suffix = site.get('suffix', '').lstrip('.')
        # host에서 prefix 제거, suffix 제거 후 숫자 추출
        name = host  # tvwiki26.net
        if '.' in name:
            name = name.rsplit('.', 1)[0]  # tvwiki26
        if name.startswith(prefix):
            num_str = name[len(prefix):]  # 26
            if num_str.isdigit():
                return int(num_str)
    except:
        pass
    return None

def check_url(url, timeout=2, site=None):
    """
    반환값: (alive: bool, actual_num: int or None)
    actual_num - 같은 계열 다른 번호로 리다이렉트된 경우 해당 번호, 없으면 None
    """
    original_host = urlparse(url).hostname
    attempts = [
        (url, True, timeout),
        (url, False, 1),
        (url.replace('https://', 'http://'), False, 1),
    ]
    for try_url, verify, t in attempts:
        try:
            resp = get_session().get(try_url, timeout=t, allow_redirects=True, verify=verify)
            if resp.status_code >= 500: return False, None
            if len(resp.content) < 200: return False, None

            # 리다이렉트 체인 전체 확인
            all_hosts = set()
            for r in resp.history:
                h = urlparse(r.url).hostname
                if h: all_hosts.add(h)
            final_host = urlparse(resp.url).hostname
            if final_host: all_hosts.add(final_host)

            # UNRELATED_HOSTS 체크
            bad = all_hosts & UNRELATED_HOSTS
            if bad:
                print(f'  관련없는 외부 서비스로 이동: {original_host} -> {bad} (제외)')
                return False, None

            # 경유/광고 URL 경로 패턴
            final_path = urlparse(resp.url).path
            for pat in UNRELATED_PATH_PATTERNS:
                if final_path.startswith(pat):
                    print(f'  경유 URL 감지 [{pat}]: {original_host} -> {resp.url[:60]} (제외)')
                    return False, None

            # ISP 차단 페이지 → OK (크롬 DoH로 우회 가능)
            # final_host뿐 아니라 리다이렉트 체인 전체에서 차단 도메인 확인
            isp_hit = all_hosts & ISP_BLOCK_HOSTS
            if isp_hit:
                print(f'  ISP 차단(DoH 우회 가능): {original_host} -> {isp_hit} (OK)')
                return True, None

            # 같은 계열 도메인 체크
            if is_same_family(original_host, final_host, site):
                try:
                    text = resp.content.decode('utf-8', errors='ignore')
                except:
                    text = ''
                for kw in PARKED_KEYWORDS:
                    if kw in text:
                        print(f'  파킹 도메인 감지 [{kw}]: {original_host} (제외)')
                        return False, None
                # 무작위 텍스트 파킹 감지: <title>이 랜덤 단어 조합인 경우
                # article:published_time 메타태그 + 짧은 body 조합
                if 'article:published_time' in text and len(text) < 5000:
                    print(f'  무작위 텍스트 파킹 감지: {original_host} (제외)')
                    return False, None
                # 리다이렉트로 다른 번호로 이동했으면 실제 번호 반환
                # ※ 낮은 번호로 리다이렉트된 경우는 무시
                actual_num = None
                if final_host != original_host and site:
                    redirected_num = _extract_num(final_host, site)
                    orig_num = _extract_num(original_host, site)
                    if redirected_num:
                        actual_num = redirected_num
                        print(f'  계열 리다이렉트: {original_host} -> {final_host} (번호:{actual_num})')
                return True, actual_num

            print(f'  외부 리다이렉트: {original_host} -> {final_host} (제외)')
            return False, None
        except Exception as e:
            print(f'  check_url 예외 [{url}]: {type(e).__name__}: {e}')
            continue
    return False, None

class Finder:
    """탐색 클래스 - queue로 진행상황 전달"""
    def __init__(self, site, timeout=2, q=None):
        self.site = site
        self.timeout = timeout
        self.q = q

    def emit(self, data):
        if self.q:
            self.q.put(data)

    def check(self, url):
        alive, actual_num = check_url(url, self.timeout, self.site)
        return alive, actual_num

    def serial(self, start, stop):
        first_alive = last_alive = None
        for n in range(start, stop + 1):
            url = make_url(self.site, n)
            self.emit({'type': 'checking', 'url': url, 'num': n})
            alive, actual_num = self.check(url)
            self.emit({'type': 'result', 'url': url, 'num': n, 'alive': alive})
            if alive:
                if first_alive is None: first_alive = n
                last_alive = actual_num if actual_num and actual_num > n else n
            else:
                # OK 구간을 찾은 후 FAIL → 연속 끊김, 종료
                if first_alive is not None:
                    break
                # 아직 OK 못 찾은 상태 → 계속 진행 (FAIL 한도 없음)
        return first_alive, last_alive

    def parallel(self, start, stop):
        BATCH = 10
        first_alive = None
        num = start
        while num <= stop and first_alive is None:
            batch = list(range(num, min(num + BATCH, stop + 1)))
            self.emit({'type': 'batch', 'nums': batch})
            with ThreadPoolExecutor(max_workers=BATCH) as ex:
                futures = {ex.submit(self.check, make_url(self.site, n)): n for n in batch}
                results = {}
                for f in as_completed(futures):
                    results[futures[f]] = f.result()
            for n in sorted(batch):
                url = make_url(self.site, n)
                alive, actual_num = results[n]
                self.emit({'type': 'result', 'url': url, 'num': n, 'alive': alive})
                if alive and first_alive is None:
                    first_alive = n
            num += BATCH
        if first_alive is None: return None, None
        last_alive = first_alive
        for n in range(first_alive + 1, stop + 1):
            url = make_url(self.site, n)
            self.emit({'type': 'checking', 'url': url, 'num': n})
            alive, actual_num = self.check(url)
            self.emit({'type': 'result', 'url': url, 'num': n, 'alive': alive})
            if alive:
                last_alive = actual_num if actual_num and actual_num > n else n  # ③ actual_num 반영
            else: break
        return first_alive, last_alive

    def run(self):
        site_id = self.site['id']
        site_start = self.site.get('start', 1)
        end = self.site.get('end', 999)
        last_data = load_last()
        last_found = last_data.get(str(site_id))

        first_alive = last_alive = None

        if last_found and last_found >= site_start:
            # 1단계: last_found ~ end 탐색 (병렬로 빠르게)
            self.emit({'type': 'status', 'msg': f'{last_found}번부터 탐색'})
            first_alive, last_alive = self.parallel(last_found, end)  # ⑥ serial→parallel 교체

            if last_alive is None:
                # 2단계: site_start ~ last_found-1 탐색 (번호가 1로 순환된 경우)
                if last_found > site_start:
                    self.emit({'type': 'status', 'msg': f'순환 탐색: {site_start}~{last_found - 1}번'})
                    first_alive, last_alive = self.parallel(site_start, last_found - 1)

            if last_alive is None:
                last_data.pop(str(site_id), None)
                save_last(last_data)
        else:
            # last_found 없으면 전체 탐색
            self.emit({'type': 'status', 'msg': f'처음({site_start}번)부터 탐색'})
            first_alive, last_alive = self.parallel(site_start, end)

        if last_alive is not None:
            last_data[str(site_id)] = last_alive
            save_last(last_data)
            return {'found': True, 'url': make_url(self.site, last_alive), 'first': first_alive, 'last': last_alive}
        return {'found': False, 'url': None}

def run_prefetch(site):
    sid = site['id']
    with _prefetch_lock:
        if sid in _prefetch_running: return
        if sid in _prefetch_cancelled:  # ② 시작 전 취소 여부 먼저 확인
            _prefetch_cancelled.discard(sid)
            return
        _prefetch_running.add(sid)
    try:
        # 현재 알고있는 번호 확인
        with _prefetch_lock:
            current_num = _user_set.get(sid)

        if current_num:
            # [1단계] alive 체크만 (빠름) - 2회 병렬 체크로 오탐 방지
            current_url = make_url(site, current_num)
            with ThreadPoolExecutor(max_workers=2) as ex:
                results = list(ex.map(lambda _: check_url(current_url, timeout=2, site=site), range(2)))
            alive_results = [(ok, num) for ok, num in results if ok]
            if alive_results:
                # 1번이라도 성공 → ON
                # 리다이렉트된 실제 번호 확인 (예: 26→27이면 27로 저장)
                actual_num = next((num for _, num in alive_results if num), None) or current_num
                actual_url = make_url(site, actual_num)
                if actual_num != current_num:
                    print(f'  [{current_num}번] 리다이렉트 → [{actual_num}번] 으로 업데이트')
                else:
                    print(f'  [{current_num}번] ON → 유지')
                with _prefetch_lock:
                    _prefetch_cache[sid] = {'found': True, 'url': actual_url, 'first': actual_num, 'last': actual_num, 'ts': time.time()}
                    _user_set[sid] = actual_num  # 실제 번호로 업데이트
                return
            else:
                # 2번 모두 실패 → OFF → 탐색 시작
                print(f'  [{current_num}번] OFF (2회 확인) → 탐색 시작')
                with _prefetch_lock:
                    _user_set.pop(sid, None)

        # [2단계] 번호 없거나 OFF → 탐색
        with _prefetch_lock:
            if sid in _prefetch_cancelled: return
        result = Finder(site, timeout=2).run()
        if result['found']:
            with _prefetch_lock:
                if sid in _prefetch_cancelled: return
                _prefetch_cache[sid] = {**result, 'ts': time.time()}
                _user_set[sid] = result['last']  # 찾은 번호 보호 등록
                print(f'  [{result["last"]}번] 새로 발견 → 등록')
    finally:
        with _prefetch_lock:
            _prefetch_running.discard(sid)

@app.route('/')
def index():
    return send_from_directory(BASE_DIR, 'index.html')

@app.route('/api/sites', methods=['GET'])
def get_sites():
    sites = load_sites()
    last_data = load_last()
    for s in sites:
        s['last_found'] = last_data.get(str(s['id']))
        with _prefetch_lock:
            cache = _prefetch_cache.get(s['id'])
        s['prefetched'] = cache['url'] if cache else None
    return jsonify(sites)  # ④ 폴링마다 스레드 생성 제거 → 전용 스케줄러가 담당

@app.route('/api/find/<int:site_id>')
def find_best(site_id):
    sites = load_sites()
    site = next((s for s in sites if s['id'] == site_id), None)
    if not site:
        return jsonify({'error': 'not found'}), 404

    # 프리페치 캐시 60초 이내면 즉시
    with _prefetch_lock:
        cache = _prefetch_cache.get(site_id)
    if cache and time.time() - cache['ts'] < 60:
        with _prefetch_lock:
            _prefetch_cache.pop(site_id, None)
        threading.Thread(target=run_prefetch, args=(dict(site),), daemon=True).start()
        result = {'found': True, 'url': cache['url'], 'first': cache.get('first', cache['last']), 'last': cache['last'], 'cached': True}
        def quick_stream():
            yield f"data: {json.dumps({'type':'status','msg':'⚡ 즉시 접속'})}\n\n"
            yield f"data: {json.dumps({'type':'done', **result})}\n\n"
        return Response(quick_stream(), mimetype='text/event-stream',
                        headers={'Cache-Control':'no-cache','X-Accel-Buffering':'no'})

    # 캐시 없어도 저장된 번호 있으면 접속 확인 후 바로 접속
    with _prefetch_lock:
        saved_num = _user_set.get(site_id)
    if not saved_num:
        _ld = load_last()
        saved_num = _ld.get(str(site_id))
    if saved_num:
        saved_url = make_url(site, saved_num)
        ok, actual_num = check_url(saved_url, timeout=2, site=site)
        if ok:
            actual_url = make_url(site, actual_num) if actual_num else saved_url
            threading.Thread(target=run_prefetch, args=(dict(site),), daemon=True).start()
            _sr = {'found': True, 'url': actual_url, 'first': actual_num or saved_num, 'last': actual_num or saved_num, 'cached': True}
            def saved_stream(r=_sr):
                yield 'data: ' + json.dumps({'type':'status','msg':'⚡ 저장된 번호로 즉시 접속'}) + '\n\n'
                yield 'data: ' + json.dumps({'type':'done', **r}) + '\n\n'
            return Response(saved_stream(), mimetype='text/event-stream',
                            headers={'Cache-Control':'no-cache','X-Accel-Buffering':'no'})
        # 저장된 번호 접속 실패 → 탐색으로 넘어감

    # SSE 스트리밍
    q = queue.Queue()

    def worker():
        finder = Finder(site, timeout=2, q=q)
        result = finder.run()
        q.put({'type': 'done', **result})

    threading.Thread(target=worker, daemon=True).start()

    def generate():
        while True:
            try:
                msg = q.get(timeout=60)
                yield f"data: {json.dumps(msg)}\n\n"
                if msg.get('type') == 'done':
                    break
            except queue.Empty:
                yield f"data: {json.dumps({'type':'done','found':False,'url':None})}\n\n"
                break

    return Response(generate(), mimetype='text/event-stream',
                    headers={'Cache-Control':'no-cache','X-Accel-Buffering':'no'})

@app.route('/api/sites', methods=['POST'])
def add_site():
    sites = load_sites()
    data = request.json
    new_id = max((s['id'] for s in sites), default=0) + 1
    data['id'] = new_id
    sites.append(data)
    save_sites(sites)
    return jsonify(data)

@app.route('/api/sites/<int:site_id>', methods=['PUT'])
def update_site(site_id):
    sites = load_sites()
    for i, s in enumerate(sites):
        if s['id'] == site_id:
            request.json['id'] = site_id
            sites[i] = request.json
            save_sites(sites)
            return jsonify(sites[i])
    return jsonify({'error': 'not found'}), 404

@app.route('/api/sites/<int:site_id>', methods=['DELETE'])
def delete_site(site_id):
    sites = load_sites()
    sites = [s for s in sites if s['id'] != site_id]
    save_sites(sites)
    last_data = load_last()
    last_data.pop(str(site_id), None)
    save_last(last_data)
    with _prefetch_lock:
        _prefetch_cache.pop(site_id, None)
    return jsonify({'ok': True})

@app.route('/api/last/<int:site_id>', methods=['DELETE'])
def reset_last(site_id):
    last_data = load_last()
    last_data.pop(str(site_id), None)
    save_last(last_data)
    with _prefetch_lock:
        _prefetch_cache.pop(site_id, None)
        _prefetch_cancelled.add(site_id)
        _user_set.pop(site_id, None)  # 초기화 시 보호 해제
    return jsonify({'ok': True})

@app.route('/api/last/<int:site_id>', methods=['POST'])
def set_last(site_id):
    num = request.json.get('num')
    if not num: return jsonify({'error': 'num required'}), 400
    last_data = load_last()
    last_data[str(site_id)] = int(num)
    save_last(last_data)
    with _prefetch_lock:
        _prefetch_cache.pop(site_id, None)
        _prefetch_cancelled.add(site_id)
        _user_set[site_id] = int(num)  # 사용자 수동 설정 보호
    return jsonify({'ok': True, 'num': int(num)})

@app.route('/api/download/sites')
def download_sites():
    if not os.path.exists(SITES_FILE):
        save_sites(DEFAULT_SITES)
    return send_from_directory(BASE_DIR, 'sites.json', as_attachment=False, mimetype='application/json')

@app.route('/api/download/last')
def download_last():
    data = load_last()
    return Response(json.dumps(data, ensure_ascii=False, indent=2), mimetype='application/json')

@app.route('/api/github/save', methods=['POST'])
def github_save():
    token = os.environ.get('GITHUB_TOKEN')
    repo = os.environ.get('GITHUB_REPO')
    if not token or not repo:
        return jsonify({'error': '환경변수 GITHUB_TOKEN, GITHUB_REPO 설정 필요'}), 500

    results = []
    files = {
        'sites.json': SITES_FILE,
        'last_found.json': LAST_FILE,
    }
    headers = {
        'Authorization': f'token {token}',
        'Accept': 'application/vnd.github.v3+json',
    }

    for filename, filepath in files.items():
        try:
            if not os.path.exists(filepath):
                continue
            with open(filepath, 'r', encoding='utf-8') as f:
                content = f.read()
            encoded = base64.b64encode(content.encode()).decode()

            # 현재 SHA 가져오기
            url = f'https://api.github.com/repos/{repo}/contents/{filename}'
            r = get_session().get(url, headers=headers, timeout=10)
            sha = r.json().get('sha') if r.status_code == 200 else None

            # 파일 업데이트
            body = {'message': f'update {filename}', 'content': encoded}
            if sha: body['sha'] = sha
            r2 = get_session().put(url, headers=headers, json=body, timeout=10)
            if r2.status_code in (200, 201):
                results.append(f'{filename} ✓')
            else:
                results.append(f'{filename} 실패: {r2.status_code}')
        except Exception as e:
            results.append(f'{filename} 오류: {str(e)}')

    return jsonify({'ok': True, 'results': results})

@app.route('/api/import/sites', methods=['POST'])
def import_sites():
    try:
        data = request.json
        if not isinstance(data, list): return jsonify({'error': '배열 형식이어야 해요'}), 400
        save_sites(data)
        return jsonify({'ok': True})
    except Exception as e:
        return jsonify({'error': str(e)}), 400

@app.route('/api/import/last', methods=['POST'])
def import_last():
    try:
        data = request.json
        if not isinstance(data, dict): return jsonify({'error': '객체 형식이어야 해요'}), 400
        save_last(data)
        # _user_set 동기화
        with _prefetch_lock:
            _user_set.clear()
            for sid_str, num in data.items():
                _user_set[int(sid_str)] = num
        return jsonify({'ok': True})
    except Exception as e:
        return jsonify({'error': str(e)}), 400

@app.route('/api/order', methods=['POST'])
def update_order():
    order = request.json.get('order', [])  # [id1, id2, id3, ...]
    if not order: return jsonify({'error': 'order required'}), 400
    sites = load_sites()
    site_map = {s['id']: s for s in sites}
    reordered = [site_map[i] for i in order if i in site_map]
    # order에 없는 사이트는 뒤에 추가
    reordered += [s for s in sites if s['id'] not in order]
    save_sites(reordered)
    return jsonify({'ok': True})

def keep_alive():
    """Render 슬립 방지 - 10분마다 자기 자신에게 HTTP 요청"""
    def loop():
        time.sleep(60)  # 시작 후 1분 뒤부터
        while True:
            try:
                # Render는 PORT 환경변수 자동 설정, 로컬은 5050
                port = os.environ.get('PORT', os.environ.get('SERVER_PORT', '10000'))
                for p in [port, '10000', '8080', '5050']:
                    try:
                        requests.get(f'http://127.0.0.1:{p}/', timeout=5)
                        print(f'  [keep-alive] ping :{p}')
                        break
                    except Exception:
                        continue
            except Exception:
                pass
            time.sleep(600)  # 10분마다
    t = threading.Thread(target=loop, daemon=True)
    t.start()

def start_prefetch_scheduler():
    """전용 스케줄러 - 2시간마다 순차 프리페치 (사이트 많아도 부하 최소화)"""
    def loop():
        time.sleep(10)  # 서버 시작 후 10초 뒤 첫 실행
        while True:
            try:
                sites = load_sites()
                for s in sites:
                    run_prefetch(dict(s))   # 순차 실행 (동시 부하 방지)
                    time.sleep(1)           # 사이트 간 1초 간격
            except Exception as e:
                print(f'스케줄러 오류: {e}')
            time.sleep(7200)  # 2시간마다
    t = threading.Thread(target=loop, daemon=True)
    t.start()

# gunicorn/직접 실행 모두 초기화
if not os.path.exists(SITES_FILE):
    save_sites(DEFAULT_SITES)
with _prefetch_lock:
    for sid_str, num in load_last().items():
        _user_set[int(sid_str)] = num
print(f'  _user_set 복구: {_user_set}')
start_prefetch_scheduler()
keep_alive()

if __name__ == '__main__':
    app.run(debug=False, host='0.0.0.0', port=5050, threaded=True)