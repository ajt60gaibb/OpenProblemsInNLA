"""Independent local statement re-elaboration with fresh target artifacts."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import platform
import subprocess
import tempfile
import time

OUT = Path(__file__).resolve().parent
PROJECT = OUT.parents[1]
REPO = PROJECT.parents[2]

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def capture(args, cwd=PROJECT):
    result = subprocess.run(args, cwd=cwd, capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(f'{args}: {result.stderr}')
    return result.stdout.strip()

def save(name, data):
    (OUT / name).write_text(json.dumps(data, indent=2) + '\n')

freeze = json.loads((PROJECT / 'verification/statement-freeze/hashes.json').read_text())
inputs = {}
for group, base in [('project_files', PROJECT), ('repository_sources', REPO)]:
    for name, expected in freeze[group].items():
        path = base / name
        actual = sha(path)
        assert actual == expected['sha256'] and path.stat().st_size == expected['bytes'], name
        item = {'sha256': actual, 'bytes': path.stat().st_size, 'matches_freeze': True}
        if group == 'repository_sources':
            data = subprocess.check_output(['git', 'show', freeze['source_commit'] + ':' + name], cwd=REPO)
            item['committed_source_sha256'] = hashlib.sha256(data).hexdigest()
            assert item['committed_source_sha256'] == actual, name
        inputs[name] = item
assert not (PROJECT / 'NLA/MI26/Proof.lean').exists()
assert not (PROJECT / 'Solution.lean').exists()
save('inputs-before.json', inputs)

manifest = json.loads((PROJECT / 'lake-manifest.json').read_text())
packages = []
for package in manifest['packages']:
    folder = PROJECT / '.lake/packages' / package['name']
    head = capture(['git', 'rev-parse', 'HEAD'], folder)
    status = capture(['git', 'status', '--porcelain'], folder)
    assert head == package['rev'] and not status, package['name']
    packages.append({'name': package['name'], 'expected': package['rev'],
                     'actual': head, 'status': status})
save('dependencies.json', packages)

parent = PROJECT / '.verification'
parent.mkdir(exist_ok=True)
prefix = Path(tempfile.mkdtemp(prefix='mi26-statement-referee1-', dir=parent))
existing = capture(['lake', 'env', 'printenv', 'LEAN_PATH'])
old = (PROJECT / '.lake/build/lib/lean').resolve()
env = dict(os.environ)
env['LEAN_PATH'] = os.pathsep.join([str(prefix)] + [p for p in existing.split(os.pathsep)
                                                   if Path(p).resolve() != old])
checks = {'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'platform': platform.platform(), 'lean_version': capture(['lean', '--version']),
          'repository_head': capture(['git', 'rev-parse', 'HEAD']),
          'fresh_prefix': str(prefix), 'LEAN_PATH': env['LEAN_PATH'],
          'scope': 'Local macOS statement re-elaboration. Fresh Definitions and Challenge, existing project artifacts excluded; dependency caches reused at verified clean pins. No proof or Linux Comparator claim.',
          'commands': []}
jobs = [('NLA/MI26/Definitions.lean', 'definitions.log', True),
        ('Challenge.lean', 'challenge.log', True),
        ('reviews/statement-referee-1-evidence/InspectStatements.lean', 'inspection.log', False)]
for source, logfile, produce in jobs:
    command = ['lean']
    artifacts = []
    if produce:
        for suffix, flag in [('.olean', '-o'), ('.ilean', '-i')]:
            output = prefix / Path(source).with_suffix(suffix)
            output.parent.mkdir(parents=True, exist_ok=True)
            command += [flag, str(output)]
            artifacts.append(output)
    command.append(source)
    print(f'Checking {source}', flush=True)
    start = time.monotonic()
    result = subprocess.run(command, cwd=PROJECT, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / logfile).write_bytes(result.stdout)
    checks['commands'].append({'source': source, 'source_sha256': sha(PROJECT / source),
        'command': command, 'exit_code': result.returncode, 'elapsed_seconds': time.monotonic() - start,
        'log': logfile, 'log_sha256': sha(OUT / logfile),
        'artifacts': {str(p.relative_to(prefix)): sha(p) for p in artifacts if p.exists()}})
    save('fresh-checks.json', checks)
    print(f'Exit {result.returncode}: {logfile}', flush=True)
    if result.returncode:
        print(result.stdout.decode(), flush=True)
        raise SystemExit(result.returncode)

after = {}
for name, item in inputs.items():
    path = (REPO if name in freeze['repository_sources'] else PROJECT) / name
    actual = sha(path)
    assert actual == item['sha256'], name
    after[name] = {'before': item['sha256'], 'after': actual, 'unchanged': True}
save('inputs-after.json', after)
assert not (PROJECT / 'NLA/MI26/Proof.lean').exists()
assert not (PROJECT / 'Solution.lean').exists()
print('PASS: fresh statements and actual instance inspection; all frozen inputs unchanged.', flush=True)
