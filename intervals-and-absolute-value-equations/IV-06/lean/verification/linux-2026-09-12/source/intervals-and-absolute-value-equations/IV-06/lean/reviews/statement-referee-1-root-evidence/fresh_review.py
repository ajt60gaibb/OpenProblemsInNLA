"""Independent root statement-only elaboration with explicitly disclosed read-only pinned caches.

No project objects are reused. No lake command mutates the dependency caches.
The initial Lake manifest still describes ordinary independent fresh clones.
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

PROJECT = Path(__file__).resolve().parents[2]
EVIDENCE = Path(__file__).resolve().parent
CACHE_PROJECT = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean')
LEAN_HOME = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def run(args, **kw):
    return subprocess.run(args, capture_output=True, **kw)

manifest = json.loads((PROJECT / 'lake-manifest.json').read_text())
pins = []
for package in manifest['packages']:
    dep = CACHE_PROJECT / '.lake/packages' / package['name']
    head = run(['git', '-C', str(dep), 'rev-parse', 'HEAD'])
    status = run(['git', '-C', str(dep), 'status', '--porcelain=v1'])
    head.check_returncode()
    status.check_returncode()
    actual = head.stdout.decode().strip()
    assert actual == package['rev'] and not status.stdout, (dep, actual, status.stdout)
    pins.append({'name': package['name'], 'path': str(dep.resolve()), 'expected': package['rev'],
                 'actual': actual, 'status': status.stdout.decode(), 'remote': package['url'],
                 'cached_objects_present': (dep / '.lake/build/lib/lean').is_dir()})

prefix = Path(tempfile.mkdtemp(prefix='iv06-referee1-statements-', dir='/tmp/nla-lean-formalization/independent-prefixes'))
order = ['Cli', 'batteries', 'Qq', 'aesop', 'proofwidgets', 'importGraph',
         'LeanSearchClient', 'plausible', 'mathlib', 'leancert']
deps = [(CACHE_PROJECT / '.lake/packages' / name / '.lake/build/lib/lean').resolve() for name in order]
assert all((CACHE_PROJECT / '.lake/packages' / name / '.lake/build/lib/lean').is_dir()
           for name in ['mathlib', 'leancert'])
paths = [prefix, *deps, LEAN_HOME / 'lib/lean']
assert all('/.lake/packages/' in str(p) or p == prefix or p == LEAN_HOME / 'lib/lean' for p in paths)
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join(map(str, paths))
lean = str(LEAN_HOME / 'bin/lean')
record = {
    'scope': 'Local macOS statement-only elaboration; actual ten clean pinned dependency caches reused read-only. No Linux Comparator, fresh dependency rebuild or proof claim.',
    'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'platform': platform.platform(), 'fresh_prefix': str(prefix), 'LEAN_PATH': env['LEAN_PATH'],
    'excluded_project_objects': [str(CACHE_PROJECT / '.lake/build/lib/lean'), str(PROJECT / '.lake/build/lib/lean')],
    'lean_version': run([lean, '--version']).stdout.decode().strip(),
    'source_commit': run(['git', '-C', str(PROJECT), 'rev-parse', 'HEAD']).stdout.decode().strip(),
    'pins': pins, 'commands': []
}
for source in ['NLA/IV06/Definitions.lean', 'Challenge.lean', 'reviews/statement-referee-1-root-evidence/Inspect.lean']:
    cmd = [lean]
    outputs = []
    if not source.startswith('reviews/'):
        for flag, suffix in [('-o', '.olean'), ('-i', '.ilean')]:
            output = prefix / Path(source).with_suffix(suffix)
            output.parent.mkdir(parents=True, exist_ok=True)
            cmd.extend([flag, str(output)])
            outputs.append(output)
    cmd.append(str(PROJECT / source))
    start = time.monotonic()
    result = run(cmd, cwd=PROJECT, env=env)
    log = EVIDENCE / (source.replace('/', '-').replace('.lean', '') + '.log')
    log.write_bytes(result.stdout + result.stderr)
    row = {'source': source, 'source_sha256': sha(PROJECT / source), 'command': cmd,
           'exit_code': result.returncode, 'seconds': time.monotonic() - start,
           'log': log.name, 'log_sha256': sha(log),
           'outputs': {str(p.relative_to(prefix)): sha(p) for p in outputs if p.exists()}}
    record['commands'].append(row)
    (EVIDENCE / 'fresh-checks.json').write_text(json.dumps(record, indent=2) + '\n')
    print(source, result.returncode, row['seconds'], flush=True)
    if result.returncode:
        print(log.read_text(), flush=True)
        raise SystemExit(result.returncode)
record['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
record['verdict'] = 'PASS: definitions and eight deliberate Challenge placeholders type-check; no proof is established'
(EVIDENCE / 'fresh-checks.json').write_text(json.dumps(record, indent=2) + '\n')
print(record['verdict'], flush=True)
