"""Candidate packaging integrity, without re-elaborating proofs or invoking dependencies."""
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


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


baseline = json.loads((E / 'baseline.json').read_text())
freeze_path = P / 'verification/proof-freeze.json'
assert sha(freeze_path) == baseline['proof_freeze_sha256']
freeze = json.loads(freeze_path.read_text())
for name, row in freeze['files'].items():
    actual = E / 'README.statement.md' if name == 'README.md' else P / name
    assert sha(actual) == row['sha256'] and actual.stat().st_size == row['bytes'], name
for name, row in baseline['original_project_inputs'].items():
    actual = E / 'README.statement.md' if name == 'README.md' else P / name
    assert sha(actual) == row['sha256'] and actual.stat().st_size == row['bytes'], name
for name, digest in freeze['source_files'].items():
    assert sha(W / name) == digest, name
    blob = subprocess.check_output(['git', 'show', freeze['source_commit'] + ':' + name], cwd=W)
    assert hashlib.sha256(blob).hexdigest() == digest, name
review_evidence = {}
for name, digest in baseline['review_reports_and_manifests'].items():
    path = P / name
    assert sha(path) == digest, name
    if name.endswith('EVIDENCE-MANIFEST.json'):
        manifest = json.loads(path.read_text())
        for relative, row in manifest['files'].items():
            item = (path.parent / relative).resolve()
            assert item.is_relative_to(P)
            assert sha(item) == row['sha256'] and item.stat().st_size == row['bytes'], relative
        review_evidence[name] = len(manifest['files'])
for name, row in baseline['catalog_inputs'].items():
    assert sha(W / name) == row['sha256'], name
assert not subprocess.check_output(['git', 'diff', '--name-only'], cwd=W)

config = json.loads((P / 'comparator.json').read_text())
challenge = (P / 'Challenge.lean').read_text()
solution = (P / 'Solution.lean').read_text()
expected = ['NLA.IV06.' + name for name in re.findall(r'^theorem (\w+)', challenge, re.M)]
actual = ['NLA.IV06.' + name for name in re.findall(r'^theorem (\w+)', solution, re.M)]
assert len(expected) == 8 and expected == actual == config['theorem_names']
assert config['definition_names'] == []
assert config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
metadata = yaml.safe_load((P / 'formalization.yaml').read_text())
assert metadata['version'] == 'v0.4'
assert [row['declaration'] for row in metadata['status']['main_results']] == expected
assert metadata['status']['sorry_count'] == metadata['status']['sorry_in_definitions'] == 0
assert metadata['review']['linux_verification']['status'] == 'pending'
assert metadata['project']['authors'] == ['George Stepaniants']
assert metadata['project']['affiliations']['George Stepaniants'] == (
    'Department of Computing and Mathematical Sciences, California Institute of Technology, '
    'Pasadena, California, USA')
assert len(metadata['review']['statement_reports']) == len(metadata['review']['proof_reports']) == 2
for report in metadata['review']['statement_reports'] + metadata['review']['proof_reports']:
    assert sha(P / report['file']) == report['sha256']

readme = (P / 'README.md').read_text()
links = []
for link in re.findall(r'\[[^\]]*\]\(([^)]+)\)', readme):
    if '://' not in link and not link.startswith('#'):
        path = (P / link.split('#', 1)[0]).resolve()
        assert path.exists(), link
        links.append(link)
for name in ['README.md', 'formalization.yaml']:
    text = (P / name).read_text()
    assert text.endswith('\n')
    assert not any(line.rstrip() != line for line in text.splitlines()), name
    assert not re.search(r'[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}', text), name
assert '**Status:** Solved' in (W / 'intervals-and-absolute-value-equations/IV-06/README.md').read_text()
assert sha(E / 'README.statement.md') == baseline['readme_original_sha256']
assert sha(P / 'README.md') != baseline['readme_original_sha256']
checks = json.loads((E / 'validation-checks.json').read_text())
assert len(checks['commands']) == 4 and checks['catalog_byte_identity']
for row in checks['commands']:
    assert row['exit_code'] == 0 and sha(E / row['log']) == row['log_sha256']
assert 'Ran 17 tests' in (E / 'permanent-id-tests.log').read_text()
assert 'PASS (8 declarations)' in (E / 'manifest.log').read_text()

# Generated private-prefix objects remain ignored by the unchanged per-project patterns.
generated = list((P / '.verification').rglob('*.olean')) + list((P / '.verification').rglob('*.ilean'))
ignored = []
for obj in generated:
    relative = obj.relative_to(W).as_posix()
    r = subprocess.run(['git', 'check-ignore', '--quiet', relative], cwd=W)
    assert r.returncode == 0, relative
    ignored.append(relative)

record = {
    'phase': 'reviewed-linux-candidate-packaging',
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'base': freeze['source_commit'],
    'proof_freeze_sha256': sha(freeze_path),
    'proof_frozen_inputs': len(freeze['files']), 'unchanged_nonwrapper_frozen_inputs': len(freeze['files']) - 1,
    'all_original_project_inputs': len(baseline['original_project_inputs']),
    'unchanged_original_project_inputs_except_README': len(baseline['original_project_inputs']) - 1,
    'original_source_git_blobs_unchanged': len(freeze['source_files']),
    'historical_README_archive_sha256': sha(E / 'README.statement.md'),
    'current_README_sha256': sha(P / 'README.md'),
    'formalization_yaml_sha256': sha(P / 'formalization.yaml'),
    'review_reports_and_manifests': baseline['review_reports_and_manifests'],
    'verified_review_evidence_counts': review_evidence,
    'exact_export_names': expected, 'definition_exceptions': [],
    'allowed_axioms': config['permitted_axioms'],
    'relative_README_links_checked': links,
    'generated_object_files_confirmed_ignored': len(ignored),
    'metadata_and_comparator_validation': 'PASS: actual schema v0.4 and all eight exports',
    'permanent_ID_validation': 'PASS against origin/main; 17 tests passed',
    'catalog_regeneration': 'PASS, every catalog input byte-identical; tracked diff empty',
    'proof_or_dependency_build_or_download': False,
    'proof_referee_count_added_by_packaging': 0,
    'Linux_Comparator_and_operational_review': 'pending',
    'canonical_status': 'Solved, unchanged',
    'commit_push_or_publication': False}
(E / 'integrity.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
