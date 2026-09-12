"""Independent, statement-only local re-elaboration with fresh target artifacts."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import platform
import subprocess
import tempfile
import time

EVIDENCE = Path(__file__).resolve().parent
PROJECT = EVIDENCE.parents[1]
REPO = PROJECT.parents[2]

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def capture(args, cwd=PROJECT):
    result = subprocess.run(args, cwd=cwd, capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(f'{args}: {result.stderr}')
    return result.stdout.strip()

def save(name, data):
    (EVIDENCE / name).write_text(json.dumps(data, indent=2) + '\n')

freeze = json.loads((PROJECT / 'reviews/statement-freeze.json').read_text())
inputs = {}
for category in ('mathematical_sha256', 'configuration_sha256', 'source_sha256'):
    for name, expected in freeze[category].items():
        path = (REPO if category == 'source_sha256' else PROJECT) / name
        actual = sha(path)
        inputs[name] = {'sha256': actual, 'bytes': path.stat().st_size,
                        'freeze_sha256': expected, 'matches_freeze': actual == expected}
        assert actual == expected, name
assert not (PROJECT / 'NLA/MI06/Proof.lean').exists()
assert not (PROJECT / 'Solution.lean').exists()
save('inputs-before.json', inputs)

manifest = json.loads((PROJECT / 'lake-manifest.json').read_text())
packages = []
for package in manifest['packages']:
    directory = PROJECT / '.lake/packages' / package['name']
    head = capture(['git', 'rev-parse', 'HEAD'], directory)
    status = capture(['git', 'status', '--porcelain'], directory)
    packages.append({'name': package['name'], 'expected': package['rev'],
                     'actual': head, 'status': status,
                     'matches_pin': head == package['rev']})
    assert head == package['rev'] and status == '', package['name']
save('dependencies.json', packages)

prefix_parent = PROJECT / '.verification'
prefix_parent.mkdir(exist_ok=True)
prefix = Path(tempfile.mkdtemp(prefix='mi06-statement-referee1-', dir=prefix_parent))
lake_path = capture(['lake', 'env', 'printenv', 'LEAN_PATH'])
old_target_prefix = (PROJECT / '.lake/build/lib/lean').resolve()
dependency_paths = [part for part in lake_path.split(os.pathsep)
                    if Path(part).resolve() != old_target_prefix]
env = dict(os.environ)
env['LEAN_PATH'] = os.pathsep.join([str(prefix)] + dependency_paths)
checks = {'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'platform': platform.platform(),
          'lean_version': capture(['lean', '--version']),
          'repository_head': capture(['git', 'rev-parse', 'HEAD']),
          'branch': capture(['git', 'branch', '--show-current']),
          'fresh_prefix': str(prefix), 'LEAN_PATH': env['LEAN_PATH'],
          'notes': 'Local macOS statement re-elaboration. Dependency caches reused at checked clean pins. Existing project target artifact prefix excluded; Definitions and Challenge freshly compiled sequentially. No proof or Linux Comparator claim.',
          'commands': []}

jobs = [
    ('NLA/MI06/Definitions.lean', 'definitions.log', True),
    ('Challenge.lean', 'challenge.log', True),
    ('reviews/statement-referee-1-evidence/InspectStatements.lean', 'inspection.log', False),
]
for source, log, produce in jobs:
    command = ['lean']
    artifacts = []
    if produce:
        for suffix, flag in (('.olean', '-o'), ('.ilean', '-i')):
            output = prefix / Path(source).with_suffix(suffix)
            output.parent.mkdir(parents=True, exist_ok=True)
            command.extend([flag, str(output)])
            artifacts.append(output)
    command.append(source)
    print(f'Checking {source}', flush=True)
    start = time.monotonic()
    result = subprocess.run(command, cwd=PROJECT, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    elapsed = time.monotonic() - start
    (EVIDENCE / log).write_bytes(result.stdout)
    record = {'source': source, 'source_sha256': sha(PROJECT / source),
              'command': command, 'exit_code': result.returncode,
              'elapsed_seconds': elapsed, 'log': log, 'log_sha256': sha(EVIDENCE / log),
              'artifacts': {str(path.relative_to(prefix)): sha(path)
                            for path in artifacts if path.exists()}}
    checks['commands'].append(record)
    save('fresh-checks.json', checks)
    print(f'Exit {result.returncode}, {elapsed:.2f}s: {log}', flush=True)
    if result.returncode:
        print(result.stdout.decode(), flush=True)
        raise SystemExit(result.returncode)

after = {}
for name, item in inputs.items():
    path = REPO / name if name in freeze['source_sha256'] else PROJECT / name
    current = sha(path)
    after[name] = {'before': item['sha256'], 'after': current,
                   'unchanged': item['sha256'] == current}
    assert after[name]['unchanged'], name
assert not (PROJECT / 'NLA/MI06/Proof.lean').exists()
assert not (PROJECT / 'Solution.lean').exists()
save('inputs-after.json', after)
print('All frozen bytes and dependency pins unchanged; no Proof or Solution exists.', flush=True)
