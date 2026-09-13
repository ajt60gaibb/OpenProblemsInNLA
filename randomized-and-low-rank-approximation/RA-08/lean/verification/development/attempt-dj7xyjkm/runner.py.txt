"""Direct Lean source checks for RA-08; all dependency objects are read-only.

Each invocation begins with an empty RA-08 object prefix. Source snapshots,
commands and raw logs are retained, including failed development attempts.
This is a macOS elaboration diagnostic, not the authoritative Linux checker.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import platform
import shutil
import subprocess
import sys
import tempfile
import time

P = Path(__file__).resolve().parents[2]
E = Path(__file__).resolve().parent
C = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean')
L = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

pins = []
for p in json.loads((P / 'lake-manifest.json').read_text())['packages']:
    dep = C / '.lake/packages' / p['name']
    rev = subprocess.check_output(['git', '-C', str(dep), 'rev-parse', 'HEAD']).decode().strip()
    assert rev == p['rev']
    assert not subprocess.check_output(['git', '-C', str(dep), 'status', '--porcelain=v1'])
    pins.append({'name': p['name'], 'path': str(dep), 'expected': p['rev'], 'actual': rev,
                 'git_clean': True})

run = Path(tempfile.mkdtemp(prefix='attempt-', dir=E))
prefix = Path(tempfile.mkdtemp(prefix='ra08-development-',
                             dir='/tmp/nla-lean-formalization/independent-prefixes'))
order = ['Cli', 'batteries', 'Qq', 'aesop', 'proofwidgets', 'importGraph',
         'LeanSearchClient', 'plausible', 'mathlib', 'leancert']
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join(map(str, [prefix, *[
    C / '.lake/packages' / n / '.lake/build/lib/lean' for n in order], L / 'lib/lean']))
record = {'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'scope': 'Fresh macOS source elaboration; dependency objects read-only; Linux pending.',
          'platform': platform.platform(), 'pins': pins, 'fresh_prefix': str(prefix),
          'LEAN_PATH': env['LEAN_PATH'], 'commands': [], 'runner_sha256': sha(__file__)}
(run / 'runner.py.txt').write_bytes(Path(__file__).read_bytes())
sources = sys.argv[1:] or ['NLA/RA08/Definitions.lean', 'NLA/RA08/Witness.lean',
                           'NLA/RA08/Numerical.lean']
failed = False
for source in sources:
    path = P / source
    (run / (source.replace('/', '-') + '.txt')).write_bytes(path.read_bytes())
    target = prefix / Path(source).with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    cmd = [str(L / 'bin/lean'), '-o', str(target), '-i', str(target.with_suffix('.ilean')),
           str(path)]
    start = time.monotonic()
    r = subprocess.run(cmd, cwd=P, env=env, capture_output=True)
    log = run / source.replace('/', '-').replace('.lean', '.log')
    log.write_bytes(r.stdout + r.stderr)
    record['commands'].append({'source': source, 'source_sha256': sha(path), 'command': cmd,
                               'exit_code': r.returncode, 'seconds': time.monotonic() - start,
                               'log': log.name, 'log_sha256': sha(log)})
    (run / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
    print(source, r.returncode, round(time.monotonic() - start, 2), flush=True)
    if r.returncode:
        print(log.read_text()[:16000], flush=True)
        failed = True
        break
for p in pins:
    assert subprocess.check_output(['git', '-C', p['path'], 'rev-parse', 'HEAD']).decode().strip() == p['actual']
    assert not subprocess.check_output(['git', '-C', p['path'], 'status', '--porcelain=v1'])
record['pins_rechecked_after'] = True
record['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
record['verdict'] = 'FAIL' if failed else 'PASS'
record['disposable_project_objects'] = [
    {'relative_path': str(p.relative_to(prefix)), 'sha256': sha(p), 'bytes': p.stat().st_size}
    for p in sorted(prefix.rglob('*')) if p.is_file()]
shutil.rmtree(prefix)
record['disposable_project_prefix_removed_after_check'] = True
(run / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
(E / 'latest.json').write_text(json.dumps({'attempt': str(run), 'fresh_prefix': str(prefix),
                                         'result_sha256': sha(run / 'result.json')}, indent=2) + '\n')
print(record['verdict'], run, flush=True)
sys.exit(int(failed))
