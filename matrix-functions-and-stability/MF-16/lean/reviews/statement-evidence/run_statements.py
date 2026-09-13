"""MF-16 statement-only checks; matching MI22 dependency objects read-only.
Adapted from the campaign IS-03 statement runner by /root and /root/solved_statement_inventory.
No proof or kernel certificate is implemented by this diagnostic runner.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import platform
import subprocess
import tempfile
import time

P = Path(__file__).resolve().parents[2]
E = Path(__file__).resolve().parent
C = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean')
L = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


manifest = json.loads((P / 'lake-manifest.json').read_text())
pins = []
for package in manifest['packages']:
    dep = C / '.lake/packages' / package['name']
    rev = subprocess.check_output(['git', '-C', str(dep), 'rev-parse', 'HEAD']).decode().strip()
    status = subprocess.check_output(['git', '-C', str(dep), 'status', '--porcelain=v1'])
    assert rev == package['rev'] and not status, (dep, rev, status)
    pins.append({'name': package['name'], 'path': str(dep.resolve()),
                 'expected': package['rev'], 'actual': rev, 'git_clean': True})

run = Path(tempfile.mkdtemp(prefix='attempt-', dir=E))
prefix = Path(tempfile.mkdtemp(prefix='mf16-statements-',
                             dir='/tmp/nla-lean-formalization/independent-prefixes'))
order = ['Cli', 'batteries', 'Qq', 'aesop', 'proofwidgets', 'importGraph',
         'LeanSearchClient', 'plausible', 'mathlib', 'leancert']
paths = [prefix, *[(C / '.lake/packages' / n / '.lake/build/lib/lean').resolve()
                    for n in order], L / 'lib/lean']
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join(map(str, paths))
record = {
    'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'platform': platform.platform(),
    'scope': ('Author statement-only macOS source elaboration and actual definition/API inspection. '
              'Ten clean pinned dependency caches reused read-only; no dependency copy or Lake '
              'rebuild. The empty project prefix excludes every prior MF16 project object. '
              'No proof or Linux Comparator result is claimed.'),
    'toolchain_output': subprocess.check_output([str(L / 'bin/lean'), '--version']).decode().strip(),
    'fresh_prefix': str(prefix), 'LEAN_PATH': env['LEAN_PATH'], 'pins': pins, 'commands': []}

for source in ['NLA/MF16/Definitions.lean', 'Challenge.lean',
               'reviews/statement-evidence/Inspect.lean']:
    sourcefile = P / source
    (run / (source.replace('/', '-') + '.txt')).write_bytes(sourcefile.read_bytes())
    target = prefix / Path(source).with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    cmd = [str(L / 'bin/lean'), '-o', str(target), '-i', str(target.with_suffix('.ilean')),
           str(sourcefile)]
    start = time.monotonic()
    result = subprocess.run(cmd, cwd=P, env=env, capture_output=True)
    log = run / source.replace('/', '-').replace('.lean', '.log')
    log.write_bytes(result.stdout + result.stderr)
    row = {'source': source, 'source_sha256': sha(sourcefile), 'command': cmd,
           'exit_code': result.returncode, 'seconds': time.monotonic() - start,
           'log': log.name, 'log_sha256': sha(log)}
    record['commands'].append(row)
    (run / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
    print(source, result.returncode, round(row['seconds'], 2), flush=True)
    if result.returncode:
        print(log.read_text()[:8000], flush=True)
        raise SystemExit(result.returncode)

for pin in pins:
    assert subprocess.check_output(['git', '-C', pin['path'], 'rev-parse', 'HEAD']).decode().strip() == pin['actual']
    assert not subprocess.check_output(['git', '-C', pin['path'], 'status', '--porcelain=v1'])
record['pins_rechecked_after'] = True
record['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
record['verdict'] = 'PASS: statement typechecking only'
(run / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
(E / 'latest.json').write_text(json.dumps({'attempt': str(run), 'fresh_prefix': str(prefix),
                                         'result_sha256': sha(run / 'result.json')}, indent=2) + '\n')
print('PASS', run, flush=True)
