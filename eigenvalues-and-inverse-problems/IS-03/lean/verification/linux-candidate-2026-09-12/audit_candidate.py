"""Check IS-03 candidate metadata and byte preservation without invoking Lean.

Run with the campaign Python environment containing PyYAML. Historical proof
and review logs are read, never regenerated. The evidence inventory is sealed
separately after this script's final result and the handoff have been written.
"""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess
import yaml

E = Path(__file__).resolve().parent
P = E.parents[1]
W = P.parents[2]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


baseline = json.loads((E / 'baseline.json').read_text())
archive = E / 'README.statement.md'
assert sha(archive) == baseline['readme_original_sha256']
proof = json.loads((P / 'verification/proof-freeze.json').read_text())
statement = json.loads((P / 'reviews/statement-freeze.json').read_text())
assert len(proof['files']) == 203 and len(statement['files']) == 34
for freeze in (proof, statement):
    for name, digest in freeze['files'].items():
        path = archive if name == 'README.md' else P / name
        assert sha(path) == digest, name
for name, record in baseline['original_project_inputs'].items():
    path = archive if name == 'README.md' else P / name
    assert sha(path) == record['sha256'], name
    assert path.stat().st_size == record['bytes'], name

for name, digest in proof['source_files'].items():
    assert sha(W / name) == digest, name
    blob = subprocess.check_output(['git', 'show', proof['base'] + ':' + name], cwd=W)
    assert hashlib.sha256(blob).hexdigest() == digest, name

evidence_counts = {}
for name, digest in baseline['review_reports_and_manifests'].items():
    path = P / name
    assert sha(path) == digest, name
    if path.name == 'EVIDENCE-MANIFEST.json':
        record = json.loads(path.read_text())
        for relative, item in record['files'].items():
            bound = (path.parent / relative).resolve()
            assert bound.is_relative_to(P), relative
            assert sha(bound) == item['sha256'], relative
            assert bound.stat().st_size == item['bytes'], relative
        evidence_counts[name] = len(record['files'])
assert evidence_counts == baseline['review_evidence_bound_counts']

config = json.loads((P / 'comparator.json').read_text())
names = ['NLA.IS03.' + name for name in re.findall(
    r'^theorem (\w+)', (P / 'Challenge.lean').read_text(), re.M)]
solution_names = ['NLA.IS03.' + name for name in re.findall(
    r'^theorem (\w+)', (P / 'Solution.lean').read_text(), re.M)]
assert len(names) == 7 and names == config['theorem_names'] == solution_names
assert config['definition_names'] == []
axioms = ['propext', 'Classical.choice', 'Quot.sound']
assert config['permitted_axioms'] == axioms
metadata = yaml.safe_load((P / 'formalization.yaml').read_text())
assert metadata['version'] == 'v0.4'
assert [x['declaration'] for x in metadata['status']['main_results']] == names
assert [x['declaration'] for x in metadata['alignment']] == names
assert metadata['status']['sorry_count'] == metadata['status']['sorry_in_definitions'] == 0
assert metadata['status']['axioms'] == axioms
assert metadata['review']['linux_verification']['status'] == 'pending'
assert metadata['project']['authors'] == ['George Stepaniants']
assert metadata['project']['affiliations']['George Stepaniants'] == (
    'Department of Computing and Mathematical Sciences, California Institute of Technology, '
    'Pasadena, California, USA')
assert len(metadata['review']['statement_reports']) == 2
assert len(metadata['review']['proof_reports']) == 2
for record in metadata['review']['statement_reports'] + metadata['review']['proof_reports']:
    assert sha(P / record['file']) == record['sha256']
for group in ['statement_report_evidence', 'proof_report_evidence']:
    assert len(metadata['review'][group]) == 2
    for name, record in metadata['review'][group].items():
        assert sha(P / name) == record['sha256']
        assert (P / name).stat().st_size == record['bytes']
for name in ['statement_freeze', 'proof_freeze', 'coordinator_acceptance']:
    record = metadata['review'][name]
    assert sha(P / record['file']) == record['sha256']

links = []
for link in re.findall(r'\[[^\]]*\]\(([^)]+)\)', (P / 'README.md').read_text()):
    if '://' not in link and not link.startswith('#'):
        assert (P / link.split('#', 1)[0]).resolve().exists(), link
        links.append(link)
for name in ['README.md', 'formalization.yaml']:
    text = (P / name).read_text()
    assert text.endswith('\n')
    assert not any(line.rstrip() != line for line in text.splitlines()), name
    assert not re.search(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}', text), name
assert sha(P / 'README.md') != baseline['readme_original_sha256']
assert 'formalization.yaml' not in baseline['original_project_inputs']

checks = json.loads((E / 'validation-checks.json').read_text())
assert len(checks['commands']) == 2
for record in checks['commands']:
    assert record['result']['exit_code'] == 0
    assert sha(E / record['log']) == record['log_sha256']
assert 'PASS (7 declarations)' in (E / 'manifest.log').read_text()
assert 'Validated 217 permanent problem IDs against origin/main' in (E / 'permanent-ids.log').read_text()
assert 'Ran 17 tests' in (P / 'reviews/statement-evidence/permanent-id-tests.log').read_text()
assert sha(W / 'problem_ids.json') == baseline['registry_sha256']
assert len(json.loads((W / 'problem_ids.json').read_text())) == 217
assert '**Status:** Solved' in (P.parent / 'README.md').read_text()
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=W, text=True).strip() == baseline['base']
assert not subprocess.check_output(['git', 'diff', '--name-only'], cwd=W)
assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=W)

record = {
    'phase': 'IS-03 reviewed Linux candidate packaging',
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'worktree': str(W), 'base': baseline['base'],
    'proof_inputs_preserved': 203, 'proof_inputs_byte_identical_except_README': 202,
    'statement_inputs_preserved': 34,
    'prepackaging_project_inputs': len(baseline['original_project_inputs']),
    'prepackaging_inputs_byte_identical_except_README': len(baseline['original_project_inputs']) - 1,
    'original_source_git_blobs_unchanged': len(proof['source_files']),
    'review_evidence_counts_rechecked': evidence_counts,
    'historical_README_archive_sha256': sha(archive),
    'current_README_sha256': sha(P / 'README.md'),
    'formalization_yaml_sha256': sha(P / 'formalization.yaml'),
    'proof_freeze_sha256': sha(P / 'verification/proof-freeze.json'),
    'final_review_acceptance_sha256': sha(P / 'verification/final-review-acceptance.json'),
    'wrapper_mutation_scope': ['README.md refreshed with exact old archive', 'formalization.yaml new'],
    'other_additions': 'Historical README archive and candidate packaging evidence only',
    'all_seven_exports': names, 'definition_exceptions': [], 'permitted_axioms': axioms,
    'relative_README_links_checked': links,
    'actual_schema_and_Comparator_coverage': 'PASS (7 declarations)',
    'permanent_ID_validation': 'PASS: 217 IDs against origin/main; registry byte-identical',
    'ID_tests': 'Prior sealed 17-test result retained; no repeated tests during metadata-only packaging',
    'canonical_and_catalog_files': 'All tracked files unchanged; no catalog regeneration needed',
    'tracked_and_staged_diff_empty': True,
    'proof_or_dependency_build_download_or_cache_change': False,
    'independent_final_referees_added_by_packaging': 0,
    'canonical_status': 'Solved, unchanged',
    'Linux_Comparator_default_kernel_controls_operational_review': 'pending',
    'commit_push_or_publication': False,
}
(E / 'integrity.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
