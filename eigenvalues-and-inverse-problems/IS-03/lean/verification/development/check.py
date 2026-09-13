"""Incremental proof development using immutable pinned MI22 dependency artifacts."""
from pathlib import Path
import hashlib, json, os, subprocess, sys, tempfile, time

P = Path(__file__).resolve().parents[2]
E = Path(__file__).resolve().parent
C = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
L = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')
state = E / 'prefix.json'
if state.exists():
    prefix = Path(json.loads(state.read_text())['prefix'])
else:
    prefix = Path(tempfile.mkdtemp(prefix='is03-proof-development-',
        dir='/tmp/nla-lean-formalization/independent-prefixes'))
    state.write_text(json.dumps({'prefix': str(prefix)}) + '\n')
order = ['Cli', 'batteries', 'Qq', 'aesop', 'proofwidgets', 'importGraph',
         'LeanSearchClient', 'plausible', 'mathlib', 'leancert']
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join(map(str, [prefix, *[C / n / '.lake/build/lib/lean' for n in order], L/'lib/lean']))
for source in sys.argv[1:]:
    target = prefix / Path(source).with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    cmd = [str(L/'bin/lean'), '-o', str(target), '-i', str(target.with_suffix('.ilean')), source]
    t = time.monotonic()
    result = subprocess.run(cmd, cwd=P, env=env, capture_output=True)
    rec = {'source': source, 'sha256': hashlib.sha256((P/source).read_bytes()).hexdigest(),
           'command': cmd, 'exit_code': result.returncode, 'seconds': time.monotonic()-t,
           'prefix': str(prefix), 'LEAN_PATH': env['LEAN_PATH']}
    stem = str(time.time_ns()) + '-' + source.replace('/', '-').removesuffix('.lean')
    (E/(stem+'.log')).write_bytes(result.stdout+result.stderr)
    (E/(stem+'.json')).write_text(json.dumps(rec, indent=2)+'\n')
    print(source, result.returncode, round(rec['seconds'], 2), flush=True)
    print((result.stdout+result.stderr).decode(), end='', flush=True)
    if result.returncode: raise SystemExit(result.returncode)
