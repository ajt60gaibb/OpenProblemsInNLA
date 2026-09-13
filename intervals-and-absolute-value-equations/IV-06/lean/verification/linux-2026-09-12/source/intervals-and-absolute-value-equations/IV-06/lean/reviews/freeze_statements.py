"""Freeze complete IV-06 statement-stage sources and the exact original sources."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

project = Path(__file__).resolve().parents[1]
repo = project.parents[2]
source = json.loads((project / 'source-inputs.json').read_text())
checks = json.loads((project / 'reviews/statement-evidence/fresh-checks.json').read_text())
config = json.loads((project / 'comparator.json').read_text())
challenge = (project / 'Challenge.lean').read_text()
exports = ['NLA.IV06.' + n for n in re.findall(r'^theorem (\w+)', challenge, re.M)]
assert len(exports) == 8 and exports == config['theorem_names']
assert config['definition_names'] == []
assert config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
assert len(re.findall(r'^  sorry$', challenge, re.M)) == 8
assert not (project / 'Solution.lean').exists()
assert not (project / 'NLA/IV06/Proof.lean').exists()
assert all(row['exit_code'] == 0 for row in checks['commands'])
assert len(checks['commands']) == 3 and len(checks['pins']) == 10

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

for path, record in source['files'].items():
    assert digest(repo / path) == record['sha256']
files = {}
for path in sorted(project.rglob('*')):
    relative = str(path.relative_to(project))
    if (not path.is_file() or '.lake' in path.parts or '__pycache__' in path.parts or
            relative in ['reviews/statement-freeze.json', 'reviews/statement-handoff.md']):
        continue
    files[relative] = digest(path)
result = {
    'phase': 'statement-only-before-two-independent-reviews',
    'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'base': source['base_commit'],
    'branch': subprocess.run(['git', '-C', str(repo), 'branch', '--show-current'],
                             capture_output=True, check=True).stdout.decode().strip(),
    'canonical_status': 'Solved, unchanged', 'files': files,
    'source_files': {path: row['sha256'] for path, row in source['files'].items()},
    'proof_absent': True, 'Challenge_placeholders': 8, 'export_names': exports,
    'fresh_commands': 3, 'definition_kernel_audits': 3,
    'clean_dependency_pins': 10,
    'dependency_artifacts': 'Available exact MI22 dependency objects reused read-only; no project objects reused; unused Cli has no object directory.',
    'local_lake_build_run': False, 'Linux_Comparator_run': False,
    'statement_review_approvals': []
}
out = project / 'reviews/statement-freeze.json'
out.write_text(json.dumps(result, indent=2) + '\n')
print('Frozen', len(files), 'project files and', len(source['files']), 'original source files')
print('freeze_sha256', digest(out))
for name in ['NLA/IV06/Definitions.lean', 'Challenge.lean', 'NUMERICAL_TARGETS.md']:
    print(name, files[name])
