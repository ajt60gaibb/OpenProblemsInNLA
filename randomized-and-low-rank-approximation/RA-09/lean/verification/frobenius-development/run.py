from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, os, subprocess, sys, tempfile, time

E = Path(__file__).resolve().parent
P = E.parents[1]
R = P.parents[2]
C = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean')
L = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(P / 'verification/proof-start.json') == '1838ba4734f82970700086ef9850cea848ffa7f72b52055e89b94d2a19678b8e'
freeze = json.loads((P / 'reviews/statement-freeze.json').read_text())
for rel, h in freeze['files'].items():
    assert sha(P / rel) == h, rel
pins = []
for package in json.loads((P / 'lake-manifest.json').read_text())['packages']:
    path = C / '.lake/packages' / package['name']
    rev = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD']).decode().strip()
    assert rev == package['rev']
    assert not subprocess.check_output(['git', '-C', str(path), 'status', '--porcelain'])
    pins.append(dict(name=package['name'], rev=rev, read_only_path=str(path), clean=True))
state = E / 'prefix.json'
if state.exists():
    prefix = Path(json.loads(state.read_text())['prefix'])
else:
    prefix = Path(tempfile.mkdtemp(prefix='ra09-root-frobenius-', dir='/tmp/nla-lean-formalization/independent-prefixes'))
    state.write_text(json.dumps(dict(prefix=str(prefix), initially_empty=True, scope='One evolving private direct-source development prefix; dependency objects read-only'), indent=2) + '\n')
order = ['Cli', 'batteries', 'Qq', 'aesop', 'proofwidgets', 'importGraph', 'LeanSearchClient', 'plausible', 'mathlib', 'leancert']
env = dict(os.environ)
env['LEAN_PATH'] = ':'.join(map(str, [prefix, *[C / '.lake/packages' / name / '.lake/build/lib/lean' for name in order], L / 'lib/lean']))
attempt = Path(tempfile.mkdtemp(prefix='attempt-', dir=E))
(attempt / 'run.py').write_bytes(Path(__file__).read_bytes())
sources = sys.argv[1:] or ['NLA/RA09/Frobenius.lean']
if not (prefix / 'NLA/RA09/Definitions.olean').exists():
    sources = ['NLA/RA09/Definitions.lean'] + sources
result = dict(utc=datetime.now(timezone.utc).isoformat(), platform='macOS development, not independent review or Linux verification', prefix=str(prefix), LEAN_PATH=env['LEAN_PATH'], pins=pins, commands=[])
for rel in sources:
    src = P / rel
    (attempt / (rel.replace('/', '-') + '.txt')).write_bytes(src.read_bytes())
    out = prefix / Path(rel).with_suffix('.olean')
    out.parent.mkdir(parents=True, exist_ok=True)
    for suffix in ['.olean', '.ilean']:
        out.with_suffix(suffix).unlink(missing_ok=True)
    cmd = [str(L / 'bin/lean'), '-o', str(out), '-i', str(out.with_suffix('.ilean')), str(src)]
    t = time.monotonic()
    done = subprocess.run(cmd, cwd=P, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = attempt / (rel.replace('/', '-') + '.log')
    log.write_bytes(done.stdout)
    row = dict(source=rel, source_sha256=sha(src), command=cmd, exit_code=done.returncode, seconds=time.monotonic()-t, log=log.name, log_sha256=sha(log))
    if done.returncode == 0:
        row['fresh_objects'] = {str(out.with_suffix(s).relative_to(prefix)): sha(out.with_suffix(s)) for s in ['.olean', '.ilean']}
    result['commands'].append(row)
    (attempt / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(rel, done.returncode, round(row['seconds'], 2), flush=True)
    if done.returncode:
        print(done.stdout.decode(), flush=True)
        raise SystemExit(done.returncode)
    if 'warning:' in done.stdout.decode():
        print(done.stdout.decode(), flush=True)
print('PASS', attempt, flush=True)
