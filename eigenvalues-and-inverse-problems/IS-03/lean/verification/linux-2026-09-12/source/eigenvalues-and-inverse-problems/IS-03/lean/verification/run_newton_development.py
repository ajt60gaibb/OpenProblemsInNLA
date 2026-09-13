"""Development checks for the root-owned Newton helper; not a final fresh proof audit."""
from pathlib import Path
import datetime, hashlib, json, os, subprocess, tempfile, time
P = Path(__file__).resolve().parents[1]
D = P / 'verification/newton-development'
D.mkdir(exist_ok=True)
C = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean')
L = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
sha = lambda f: hashlib.sha256(Path(f).read_bytes()).hexdigest()
state = D / 'prefix.json'
if state.exists(): prefix = Path(json.loads(state.read_text())['prefix'])
else:
    prefix = Path(tempfile.mkdtemp(prefix='is03-newton-development-', dir='/tmp/nla-lean-formalization/independent-prefixes'))
    state.write_text(json.dumps({'prefix': str(prefix)}, indent=2) + '\n')
pins = json.loads((P / 'lake-manifest.json').read_text())['packages']
for item in pins:
    dep = C / '.lake/packages' / item['name']
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=dep).decode().strip() == item['rev']
    assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=dep).strip()
order = ['Cli', 'batteries', 'Qq', 'aesop', 'proofwidgets', 'importGraph', 'LeanSearchClient', 'plausible', 'mathlib', 'leancert']
env = dict(os.environ, LEAN_PATH=':'.join(map(str, [prefix, *[C / '.lake/packages' / n / '.lake/build/lib/lean' for n in order], L / 'lib/lean'])))
freeze = json.loads((P / 'reviews/statement-freeze.json').read_text())
assert sha(P / 'NLA/IS03/Definitions.lean') == freeze['files']['NLA/IS03/Definitions.lean']
run = Path(tempfile.mkdtemp(prefix='attempt-', dir=D))
record = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'scope': 'Iterative helper development only; same private prefix can be reused. Exact pinned MI22 dependencies read-only. A complete fresh final build is required later.', 'LEAN_PATH': env['LEAN_PATH'], 'commands': []}
sources = ['NLA/IS03/Newton.lean']
if not (prefix / 'NLA/IS03/Definitions.olean').exists(): sources.insert(0, 'NLA/IS03/Definitions.lean')
for rel in sources:
    src = P / rel; out = prefix / Path(rel).with_suffix('.olean'); out.parent.mkdir(parents=True, exist_ok=True)
    snapshot = run / (Path(rel).name + '.txt'); snapshot.write_bytes(src.read_bytes())
    cmd = [str(L / 'bin/lean'), '-o', str(out), '-i', str(out.with_suffix('.ilean')), str(src)]
    start = time.monotonic(); cp = subprocess.run(cmd, cwd=P, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = run / (Path(rel).stem + '.log'); log.write_bytes(cp.stdout)
    record['commands'].append({'source': rel, 'source_sha256': sha(src), 'command': cmd, 'exit_code': cp.returncode, 'seconds': time.monotonic()-start, 'log': log.name, 'log_sha256': sha(log)})
    (run / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
    print(rel, cp.returncode, round(time.monotonic()-start, 2), flush=True)
    if cp.returncode:
        print(cp.stdout.decode()[:10000], flush=True); raise SystemExit(cp.returncode)
(D / 'latest.json').write_text(json.dumps({'attempt': str(run), 'result_sha256': sha(run / 'result.json')}, indent=2) + '\n')
print('PASS helper development', run, flush=True)
