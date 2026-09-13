"""Seal only this independent publication review, preserving all earlier evidence."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import subprocess

root = Path(__file__).resolve().parent
project = root.parents[1]
repo = project.parents[2]
pub = project / 'verification/publication-2026-09-12'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
git = lambda *a: subprocess.check_output(['git', *a], cwd=repo)

assert digest(pub / 'EVIDENCE-MANIFEST.json') == 'ab90352bc400a56881643a7f5896a5c6417a6474b6eddfc35cb895abc410b113'
assert git('rev-parse', 'HEAD').decode().strip() == '4c075f14209e85ef867eea90eacbea1e05e13a61'
integrity = json.loads((pub / 'INTEGRITY-CHECKS.json').read_text())
for rel, h in integrity['publication_sha256'].items():
    assert digest(repo / rel) == h
for rel, h in integrity['unchanged_nonwrapper_sha256'].items():
    assert digest(project / rel) == h
for rel, h in integrity['all_retained_operational_sha256'].items():
    assert digest(project / rel) == h
inputs = [
    repo / 'AGENTS.md', repo / 'CONTRIBUTING.md', repo / 'docs/lean/REVIEW.md',
    *[repo / rel for rel in integrity['publication_sha256']],
    project / 'comparator.json', project / 'lakefile.toml', project / 'lean-toolchain',
    project / 'lake-manifest.json', project / 'Challenge.lean', project / 'Solution.lean',
    project / 'NLA/IV06/Definitions.lean', project / 'NLA/IV06/Proof.lean',
    project / 'NUMERICAL_TARGETS.md', project / 'SourceCorrespondence.md',
    project / 'verification/proof-freeze.json',
    project / 'verification/linux-candidate-2026-09-12/README.statement.md',
    project / 'reviews/proof-referee-1.md', project / 'reviews/proof-referee-2.md',
    project / 'verification/linux-2026-09-12/OPERATIONAL-REVIEW.md',
    project / 'verification/linux-2026-09-12/EVIDENCE-MANIFEST.json',
    project / 'verification/root-operational-2026-09-12/ROOT-CHECKS.json',
    project / 'verification/root-operational-2026-09-12/EVIDENCE-MANIFEST.json',
    *[p for p in pub.rglob('*') if p.is_file()],
]
records = {p.relative_to(repo).as_posix(): {'bytes': p.stat().st_size, 'sha256': digest(p)} for p in sorted(set(inputs))}
(root / 'reviewed-inputs.json').write_text(json.dumps({
    'purpose': 'Public wording, preservation inputs and prior evidence inspected; not a new proof execution',
    'file_count': len(records), 'files': records}, indent=2) + '\n')
diff = git('diff', '--', 'CATALOG.md', 'README.md', 'RESOLVED.md',
    'intervals-and-absolute-value-equations/README.md',
    'intervals-and-absolute-value-equations/IV-06/README.md',
    'intervals-and-absolute-value-equations/IV-06/problem.tex',
    'intervals-and-absolute-value-equations/IV-06/lean/README.md',
    'intervals-and-absolute-value-equations/IV-06/lean/formalization.yaml')
(root / 'publication.diff').write_bytes(diff)
(root / 'COMMANDS.json').write_text(json.dumps({
    'role': 'Read-only publication auditing; no proof/dependency/test/catalog/render mutation was rerun',
    'commands': [
        {'command': ['/tmp/nla-lean-formalization/venv/bin/python', 'reviews/publication-referee-1-evidence/audit.py'],
         'workdir_context': 'Project script invoked from repository root with full relative project path',
         'exit_code': 0, 'actual_tool_wall_time_seconds': 6.749116583,
         'result': 'PASS: 200 candidate inputs; 198 nonwrappers; five exact manifest fields; 355 operational files; 217 permanent IDs; only IV-06 promotion.'},
        {'command': ['/tmp/nla-lean-formalization/venv/bin/python', 'reviews/publication-referee-1-evidence/final_checks.py'],
         'workdir_context': 'Project script invoked from repository root with full relative project path',
         'exit_code': 0, 'actual_tool_wall_time_seconds': 1.729368542,
         'result': 'PASS: final 23-file preparer seal, nine outputs, 6967 other upstream files, all 126 proof-freeze inputs via exact README archive, eight original sources, and three PDF pages.'}],
    'note': 'Exit codes and displayed stdout transcribed from the actual completed exec_command results; scripts write their own bound audit-result.json and final-checks.json. PDF bbox command/exit is bound separately in PDF-REVIEW.json.'}, indent=2) + '\n')

outer = root / 'EVIDENCE-MANIFEST.json'
files = {p.relative_to(root).as_posix(): {'bytes': p.stat().st_size, 'sha256': digest(p)}
         for p in sorted(root.rglob('*')) if p.is_file() and p != outer}
report = root.parent / 'publication-referee-1.md'
files['../publication-referee-1.md'] = {'bytes': report.stat().st_size, 'sha256': digest(report)}
outer.write_text(json.dumps({
    'utc': datetime.now(timezone.utc).isoformat(), 'reviewer': '/root/leancert_examples',
    'file_count': len(files), 'files': files,
    'inventory_rule': 'Every internal file except this exact outer manifest, plus the explicit adjacent review report; nested manifests would be retained.',
    'scope': 'Independent IV-06 publication review, preserving the separate immutable preparer and operational evidence.'}, indent=2) + '\n')
check = subprocess.run(['/tmp/nla-lean-formalization/venv/bin/python', str(root / 'verify_evidence.py')],
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
assert check.returncode == 0, check.stdout
print(check.stdout.decode(), end='')
print(json.dumps({'report_sha256': digest(report), 'evidence_manifest_sha256': digest(outer),
                  'bound_review_files': len(files), 'read_input_hashes': len(records),
                  'preparer_outer_unchanged': digest(pub / 'EVIDENCE-MANIFEST.json'),
                  'pdf_sha256': digest(project.parent / 'problem.pdf')}, indent=2))
