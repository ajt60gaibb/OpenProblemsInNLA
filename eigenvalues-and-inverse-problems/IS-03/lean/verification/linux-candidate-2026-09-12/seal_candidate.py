"""Seal the complete IS-03 candidate input inventory, including nested manifests.

This does not invoke any proof, dependency, network, or Git mutation command.
The manifest itself is the only excluded candidate input. Generated output
directories/objects are not candidate inputs. Paths are relative to the outer
manifest's directory, so source paths usually start with ../../.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess

E = Path(__file__).resolve().parent
P = E.parents[1]
W = P.parents[2]
OUTER = E / 'EVIDENCE-MANIFEST.json'
EXCLUDED_DIRS = {'.lake', '.verification', '__pycache__'}
EXCLUDED_SUFFIXES = {'.olean', '.ilean', '.trace', '.pyc'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def eligible_files():
    found = []
    for parent, directories, files in os.walk(P):
        directories[:] = sorted(d for d in directories if d not in EXCLUDED_DIRS)
        for name in sorted(files):
            path = Path(parent) / name
            if path == OUTER or path.suffix in EXCLUDED_SUFFIXES:
                continue
            assert path.is_file() and not path.is_symlink(), path
            found.append(path)
    return sorted(found)


baseline = json.loads((E / 'baseline.json').read_text())
for name, record in baseline['original_project_inputs'].items():
    path = E / 'README.statement.md' if name == 'README.md' else P / name
    assert sha(path) == record['sha256'], name
    assert path.stat().st_size == record['bytes'], name
integrity = json.loads((E / 'integrity.json').read_text())
assert sha(P / 'README.md') == integrity['current_README_sha256']
assert sha(P / 'formalization.yaml') == integrity['formalization_yaml_sha256']
assert not subprocess.check_output(['git', 'diff', '--name-only'], cwd=W)
assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=W)

files = {
    os.path.relpath(path, E): {'sha256': sha(path), 'bytes': path.stat().st_size}
    for path in eligible_files()
}
nested = sorted(name for name in files if Path(name).name == OUTER.name)
assert len(nested) >= 4
record = {
    'phase': 'IS-03 reviewed Linux candidate; full project input inventory',
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'worktree': str(W), 'project': str(P),
    'base': baseline['base'],
    'canonical_status': 'Solved, unchanged; Linux verification pending',
    'packager': '/root/solved_statement_inventory, implementation coauthor; not an independent final referee',
    'path_base': 'Directory containing this outer manifest',
    'inventory_scope': 'Every actual project source, document and evidence input, including every nested manifest',
    'exact_self_exclusion': str(OUTER.relative_to(P)),
    'generated_noninputs': {'directories': sorted(EXCLUDED_DIRS), 'suffixes': sorted(EXCLUDED_SUFFIXES)},
    'file_count': len(files), 'total_including_this_outer_manifest': len(files) + 1,
    'nested_same_basename_manifests_included': nested,
    'wrapper_mutation_scope': ['README.md refreshed and exact historical bytes archived', 'formalization.yaml new'],
    'proof_freeze_sha256': sha(P / 'verification/proof-freeze.json'),
    'statement_freeze_sha256': sha(P / 'reviews/statement-freeze.json'),
    'handoff_sha256': sha(E / 'CANDIDATE-HANDOFF.md'),
    'integrity_sha256': sha(E / 'integrity.json'),
    'files': files,
}
OUTER.write_text(json.dumps(record, indent=2) + '\n')
sealed = json.loads(OUTER.read_text())
assert set(sealed['files']) == {os.path.relpath(path, E) for path in eligible_files()}
for name, item in sealed['files'].items():
    path = (E / name).resolve()
    assert path.is_relative_to(P)
    assert sha(path) == item['sha256'] and path.stat().st_size == item['bytes'], name
print(json.dumps({
    'verdict': 'PASS: exact complete inventory and all bound bytes',
    'bound_files': len(files), 'total_files': len(files) + 1,
    'included_nested_same_basename_manifests': len(nested),
    'manifest_sha256': sha(OUTER),
    'handoff_sha256': sealed['handoff_sha256'],
    'integrity_sha256': sealed['integrity_sha256'],
}, indent=2))
