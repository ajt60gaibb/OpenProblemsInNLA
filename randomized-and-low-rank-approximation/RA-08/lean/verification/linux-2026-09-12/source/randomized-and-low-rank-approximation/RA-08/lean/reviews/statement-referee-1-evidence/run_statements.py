"""Independent fresh-prefix RA-08 statement check; MI22 dependencies read-only."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import platform
import subprocess
import tempfile
import time

E = Path(__file__).resolve().parent
P = E.parents[1]
W = P.parents[2]
C = Path('/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages')
L = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1')


def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()


freeze_path = P / 'reviews/statement-freeze.json'
assert sha(freeze_path) == 'eb0460c3dd4c13a42f928e3f00c9c3710e486922b99aff74f4d6a3098c5ed332'
freeze = json.loads(freeze_path.read_text())


def check_sources():
    for name, digest in freeze['files'].items():
        assert sha(P / name) == digest, name
    for name, digest in freeze['source_files'].items():
        assert sha(W / name) == digest, name
        blob = subprocess.check_output(['git', 'show', freeze['base'] + ':' + name], cwd=W)
        assert hashlib.sha256(blob).hexdigest() == digest, name
    assert not (P / 'NLA/RA08/Proof.lean').exists() and not (P / 'Solution.lean').exists()


check_sources()
manifest = json.loads((P / 'lake-manifest.json').read_text())
pins = []
for item in manifest['packages']:
    dep = C / item['name']
    rev = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=dep, text=True).strip()
    assert rev == item['rev']
    assert not subprocess.check_output(['git', 'status', '--porcelain=v1'], cwd=dep)
    pins.append({'name': item['name'], 'path': str(dep.resolve()), 'expected': item['rev'], 'actual': rev, 'clean': True})
assert len(pins) == 10
order = ['Cli', 'batteries', 'Qq', 'aesop', 'proofwidgets', 'importGraph', 'LeanSearchClient', 'plausible', 'mathlib', 'leancert']
prefix = Path(tempfile.mkdtemp(prefix='ra08-referee1-statements-', dir='/tmp/nla-lean-formalization/independent-prefixes'))
assert not list(prefix.iterdir())
paths = [prefix, *[(C / name / '.lake/build/lib/lean').resolve() for name in order], L / 'lib/lean']
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join(map(str, paths))
record = {'reviewer': '/root/solved_statement_inventory', 'phase': 'independent statement referee 1',
          'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'platform': platform.platform(), 'fresh_prefix': str(prefix), 'LEAN_PATH': env['LEAN_PATH'],
          'toolchain': subprocess.check_output([str(L / 'bin/lean'), '--version'], text=True).strip(),
          'scope': 'Three fresh macOS statement/definition commands; all prior project objects excluded. Ten clean pinned dependency caches reused read-only. No proof, dependency build, cache copy, Linux or Comparator claim.',
          'pins': pins, 'statement_freeze_sha256': sha(freeze_path), 'commands': []}
for name in ['NLA/RA08/Definitions.lean', 'Challenge.lean', 'reviews/statement-referee-1-evidence/Inspect.lean']:
    source = P / name
    module = Path(name).with_suffix('')
    output = prefix / module.with_suffix('.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    command = [str(L / 'bin/lean'), '-o', str(output), '-i', str(output.with_suffix('.ilean')), str(source)]
    snapshot = E / (name.replace('/', '-') + '.txt')
    snapshot.write_bytes(source.read_bytes())
    log = E / (name.replace('/', '-').replace('.lean', '.log'))
    start = time.monotonic()
    result = subprocess.run(command, cwd=P, env=env, capture_output=True)
    log.write_bytes(result.stdout + result.stderr)
    row = {'source': name, 'sha256': sha(source), 'command': command, 'exit_code': result.returncode,
           'seconds': time.monotonic() - start, 'log': log.name, 'log_sha256': sha(log),
           'source_snapshot': snapshot.name, 'source_snapshot_sha256': sha(snapshot)}
    record['commands'].append(row)
    (E / 'fresh-checks.json').write_text(json.dumps(record, indent=2) + '\n')
    print(name, result.returncode, round(row['seconds'], 2), flush=True)
    if result.returncode:
        print(log.read_text()[-12000:], flush=True)
        raise SystemExit(result.returncode)
check_sources()
for pin in pins:
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=pin['path'], text=True).strip() == pin['actual']
    assert not subprocess.check_output(['git', 'status', '--porcelain=v1'], cwd=pin['path'])
record['pins_and_sources_rechecked_after'] = True
record['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
record['verdict'] = 'PASS: statement typechecking only; no proof approval implied'
(E / 'fresh-checks.json').write_text(json.dumps(record, indent=2) + '\n')
print(record['verdict'], flush=True)
