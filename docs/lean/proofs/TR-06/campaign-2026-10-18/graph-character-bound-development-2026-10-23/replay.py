#!/usr/bin/env python3
"""Fresh author replay of actual character/fixed-pivot graph-family bounds.
This local support gate does not establish the TR-06 Target or independent review.
"""
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[5]
ROOT = REPO / 'lean-statements'
DEFAULT_LEAN = REPO.parent / 'tooling/lean-4.33.1-darwin_aarch64/bin/lean'
LEAN = Path(os.environ.get('LEAN_BIN', str(DEFAULT_LEAN)))
SOURCES = HERE / 'sources'
OBJECTS = HERE / 'objects'
TARGET = 'NLA.Proofs.TR06.GraphProjectionOrderedBound'
CONSTANTS = [
    'exists_uniform_aeval_character_finset_bound',
    'exists_uniform_aeval_character_family_bound',
    'exists_uniform_row_character_family_bound',
    'ambientValues_injective',
    'exists_uniform_ordered_graph_family_bound',
]

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

if os.environ.get('PREPARE_SOURCES') == '1':
    assert not (HERE / 'source-lock.json').exists(), 'Source snapshot is already frozen.'
    seen = set()
    order = []
    def visit(module):
        if module in seen:
            return
        path = ROOT / (module.replace('.', '/') + '.lean')
        assert path.exists(), module
        seen.add(module)
        for dependency in re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$', path.read_text(), re.M):
            if dependency.startswith(('NLA.', 'Reviewed.')):
                visit(dependency)
        order.append(module)
    visit(TARGET)
    lock = []
    for module in order:
        rel = Path(module.replace('.', '/') + '.lean')
        source = ROOT / rel
        snapshot = SOURCES / rel
        snapshot.parent.mkdir(parents=True, exist_ok=True)
        snapshot.write_bytes(source.read_bytes())
        lock.append({'module': module, 'path': 'lean-statements/' + str(rel), 'sha256': digest(source)})
    consumer = SOURCES / 'GraphCharacterBoundConsumer.lean'
    consumer.write_text('import ' + TARGET + '\nset_option leancert.trust "kernel"\n' + ''.join(
        '#print axioms NLA.Proofs.TR06.GraphProjection.' + name + '\n' +
        '#assert_trust kernel NLA.Proofs.TR06.GraphProjection.' + name + '\n' for name in CONSTANTS))
    (HERE / 'source-lock.json').write_text(json.dumps(lock, indent=2) + '\n')

lock = json.loads((HERE / 'source-lock.json').read_text())
for record in lock:
    rel = Path(record['path']).relative_to('lean-statements')
    assert digest(ROOT / rel) == record['sha256'], ('Current source differs from snapshot', str(rel))
    assert digest(SOURCES / rel) == record['sha256'], ('Frozen snapshot differs', str(rel))

OBJECTS.mkdir(parents=True, exist_ok=True)
assert not list(OBJECTS.rglob('*.olean')), 'Replay output must be fresh; choose a new run directory.'
packages = ROOT / '.lake/packages'
paths = [OBJECTS] + [p / '.lake/build/lib/lean' for p in sorted(packages.iterdir())
                     if (p / '.lake/build/lib/lean').is_dir()]
env = dict(os.environ, PATH=str(LEAN.parent) + os.pathsep + os.environ['PATH'],
           LEAN_PATH=os.pathsep.join(map(str, paths)))
commands = []
for record in lock + [{'module': 'GraphCharacterBoundConsumer', 'path': 'lean-statements/GraphCharacterBoundConsumer.lean'}]:
    rel = Path(record['path']).relative_to('lean-statements')
    output = OBJECTS / rel.with_suffix('.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    process = subprocess.run([str(LEAN), '-o', str(output), str(rel)], cwd=SOURCES, env=env,
                             text=True, capture_output=True)
    log = HERE / (record['module'].split('.')[-1] + '.log')
    log.write_text(process.stdout + process.stderr)
    commands.append({'module': record['module'], 'exit_code': process.returncode,
                     'log_sha256': digest(log)})
    print(record['module'], process.returncode, flush=True)
    if process.returncode:
        print(process.stdout + process.stderr, flush=True)
        break
status = 'PASS' if len(commands) == len(lock) + 1 and all(x['exit_code'] == 0 for x in commands) else 'FAIL'
result = {'status': status, 'scope': 'Author exact-source private-object support-gate replay. Not independent review, full TR06 Target, Linux CI, or Comparator evidence.',
          'platform': platform.platform(), 'lean_version': subprocess.check_output([str(LEAN), '--version'], text=True).strip(),
          'sources': lock, 'commands': commands, 'new_constants': len(CONSTANTS),
          'project_objects_reused': False,
          'pins': [{'path': 'lean-statements/' + name, 'sha256': digest(ROOT / name)}
                   for name in ['lean-toolchain', 'lake-manifest.json']]}
(HERE / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
raise SystemExit(0 if status == 'PASS' else 1)
