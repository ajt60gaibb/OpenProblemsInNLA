from pathlib import Path
from datetime import datetime, timezone
import collections
import copy
import hashlib
import json
import re
import subprocess
import yaml

repo = Path('/tmp/nla-lean-ra07-worktree')
entry = repo / 'randomized-and-low-rank-approximation/RA-07'
project = entry / 'lean'
publication = project / 'verification/publication-2026-09-12'
linux = project / 'verification/linux-2026-09-12'
before = json.loads((publication / 'before.json').read_text())
revision, base = before['verified_revision'], before['upstream_base']

def sha(data):
    return hashlib.sha256(data).hexdigest()

def file_hash(path):
    return sha(path.read_bytes())

def git(*args):
    return subprocess.check_output(['git', *args], cwd=repo)

def old_file(rev, path):
    return git('show', rev + ':' + str(path.relative_to(repo)))

assert git('rev-parse', 'HEAD').decode().strip() == before['integrated_head']
assert git('rev-parse', 'nla-upstream/main').decode().strip() == base
assert git('show', '-s', '--format=%ae%x00%ce', 'HEAD').strip() == b'\0'
for rel, expected in before['protected'].items():
    assert file_hash(project / rel) == expected == sha(old_file(revision, project / rel)), rel
for rel, expected in before['reviews'].items():
    assert file_hash(project / 'reviews' / rel) == expected, rel
input_changes = {
    rel: {'verified_sha256': expected, 'publication_sha256': file_hash(project / rel)}
    for rel, expected in before['all_verified_inputs'].items()
    if file_hash(project / rel) != expected
}
assert set(input_changes) == {'README.md', 'formalization.yaml'}
for rel, expected in before['operational_evidence'].items():
    assert file_hash(linux / rel) == expected, rel
evidence = json.loads((linux / 'EVIDENCE-MANIFEST.json').read_text())
assert len(evidence['files']) == 237
for rel, record in evidence['files'].items():
    data = (linux / rel).read_bytes()
    assert sha(data) == record['sha256'] and len(data) == record['bytes'], rel
assert len(before['operational_evidence']) == 238
actual_evidence_files = {str(path.relative_to(linux)) for path in linux.rglob('*') if path.is_file()}
supplemental_name = 'source/randomized-and-low-rank-approximation/RA-07/lean/verification/linux-candidate-2026-09-12/EVIDENCE-MANIFEST.json'
assert actual_evidence_files - set(before['operational_evidence']) == {supplemental_name}
supplemental_input = 'verification/linux-candidate-2026-09-12/EVIDENCE-MANIFEST.json'
assert file_hash(linux / supplemental_name) == before['all_verified_inputs'][supplemental_input]
assert file_hash(linux / supplemental_name) == sha(old_file(revision, project / supplemental_input))
assert len(actual_evidence_files) == 239
supplement = {
    'result': 'PASS: complete retained evidence count is 239; no original evidence file changed',
    'reason': 'The original outer manifest omitted a nested source snapshot with the same EVIDENCE-MANIFEST.json basename. That file is already bound by the actual 123-input Linux receipt and immutable Git revision; this record explicitly accounts for it without rewriting the original audit or outer manifest.',
    'outer_manifest_sha256': file_hash(linux / 'EVIDENCE-MANIFEST.json'),
    'outer_manifest_bound_files': 237,
    'outer_manifest_itself_files': 1,
    'supplemental_source_snapshot': {
        'file': supplemental_name,
        'sha256': file_hash(linux / supplemental_name),
        'bytes': (linux / supplemental_name).stat().st_size,
        'also_bound_by_linux_receipt_input': supplemental_input,
        'immutable_revision': revision,
    },
    'total_retained_files': 239,
}
(publication / 'evidence-count-supplement.json').write_text(json.dumps(supplement, indent=2) + '\n')

def target_tail(text):
    text = re.sub(r'<!-- navigation -->.*?<!-- /navigation -->', '', text, flags=re.S)
    return text[text.index('For $`n\\geq3`$ and positive real numbers'):].strip()

canonical = entry / 'README.md'
target = target_tail(canonical.read_text())
for rev in [revision, base]:
    assert target_tail(old_file(rev, canonical).decode()) == target
for rel, expected in before['original_informal_files'].items():
    assert file_hash(repo / rel) == expected == sha(git('show', base + ':' + rel)), rel
registry = json.loads((repo / 'problem_ids.json').read_text())
assert file_hash(repo / 'problem_ids.json') == before['problem_ids_sha256']
assert len(registry) == 217
for ident, expected in before['other_canonical'].items():
    path = repo / registry[ident]
    assert file_hash(path) == expected == sha(old_file(base, path)), ident
assert len(before['other_canonical']) == 216

expected_changes = {
    'CATALOG.md', 'README.md', 'RESOLVED.md',
    'randomized-and-low-rank-approximation/README.md',
    *[str((entry / rel).relative_to(repo)) for rel in [
        'README.md', 'problem.pdf', 'problem.tex', 'lean/README.md', 'lean/formalization.yaml']],
}
assert set(git('diff', '--name-only').decode().splitlines()) == expected_changes
preserved_base_files = []
for record in git('ls-tree', '-rz', base).split(b'\0'):
    if not record:
        continue
    descriptor, path_bytes = record.split(b'\t', 1)
    mode, kind, expected = descriptor.split()
    rel = path_bytes.decode()
    if rel in expected_changes:
        continue
    assert kind == b'blob' and mode != b'120000'
    data = (repo / rel).read_bytes()
    current_blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    assert current_blob == expected.decode(), rel
    preserved_base_files.append(rel)
shared_paths = ['tools', '.github', 'docs/lean']
assert git('diff', '--name-only', revision, base, '--', *shared_paths) == b''

new_yaml = yaml.safe_load((project / 'formalization.yaml').read_text())
old_yaml = yaml.safe_load(old_file(revision, project / 'formalization.yaml'))
comparable = copy.deepcopy(new_yaml)
changed_yaml_fields = []
for fields in [('status', 'scope'), ('review', 'status'), ('review', 'notes'),
               ('review', 'linux_verification', 'status'), ('review', 'linux_verification', 'note')]:
    new_parent, old_parent = comparable, old_yaml
    for section in fields[:-1]:
        new_parent, old_parent = new_parent[section], old_parent[section]
    field = fields[-1]
    assert new_parent[field] != old_parent[field]
    changed_yaml_fields.append('.'.join(fields))
    new_parent[field] = old_parent[field]
assert comparable == old_yaml
config = json.loads((project / 'comparator.json').read_text())
receipt = json.loads((linux / before['receipt']).read_text())
assert receipt['result'] == 'comparator-accepted'
assert receipt['repository_commit'] == revision
assert receipt['input_sha256'] == before['all_verified_inputs']
assert receipt['config'] == config
assert [x['declaration'] for x in new_yaml['status']['main_results']] == config['theorem_names']
assert len(config['theorem_names']) == 6
assert new_yaml['project']['authors'] == ['George Stepaniants']
affiliation = new_yaml['project']['affiliations']['George Stepaniants']
assert 'Department of Computing and Mathematical Sciences' in affiliation
assert 'California Institute of Technology' in affiliation
assert '@' not in json.dumps(new_yaml['project'])
status_counts = collections.Counter()
for rel in registry.values():
    text = (repo / rel).read_text()
    status_counts[re.search(r'^\*\*Status:\*\*\s+([^\n]+)', text, re.M).group(1).strip()] += 1
assert dict(status_counts) == {'Solved': 78, 'Open': 56, 'Partially resolved': 71, 'Lean verified': 12}
added_lines = [line[1:] for line in git('diff', '--', '*.md', '*.yaml').decode().splitlines()
               if line.startswith('+') and not line.startswith('+++')]
assert re.findall(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}', '\n'.join(added_lines)) == []

pdf_info = (publication / 'pdfinfo.log').read_text()
assert re.search(r'^Pages:\s+2$', pdf_info, re.M)
assert not re.search(r'Overfull|Missing character', (publication / 'render.log').read_text())
checks = []
for command, filename in [
    (['python3', 'tools/format_math.py', '--check', 'RA-07'], 'format-check-final.log'),
    (['git', 'diff', '--check'], 'diff-check-final.log'),
]:
    with (publication / filename).open('w') as output:
        result = subprocess.run(command, cwd=repo, stdout=output, stderr=subprocess.STDOUT)
    checks.append({'command': command, 'exit_code': result.returncode, 'log': filename})
    assert result.returncode == 0
(publication / 'final-checks.json').write_text(json.dumps(checks, indent=2) + '\n')
check_hashes = {path.name: file_hash(path) for path in sorted(publication.iterdir())
               if path.is_file() and path.name not in {'integrity.json', 'PUBLICATION-REVIEW.md'}}
image_dir = Path('/tmp/nla-lean-formalization/ra07-publication/final-png')
output = {
    'result': 'PASS: publication preparation; pending parent independent final publication review',
    'created_utc': datetime.now(timezone.utc).isoformat(),
    'verified_revision': revision,
    'verified_run': 34715563781,
    'upstream_base': base,
    'integration_commit': before['integrated_head'],
    'integration_author_email': '',
    'integration_committer_email': '',
    'origin_main': git('rev-parse', 'origin/main').decode().strip(),
    'verified_input_count': 123,
    'unchanged_verified_input_count': 121,
    'changed_verified_inputs': input_changes,
    'protected_source_config_pins': before['protected'],
    'unchanged_review_reports': before['reviews'],
    'retained_linux_evidence_files': 239,
    'manifest_bound_linux_files': 237,
    'additional_snapshot_bound_by_receipt_and_supplement': supplement['supplemental_source_snapshot'],
    'operational_review_sha256': file_hash(linux / 'OPERATIONAL-REVIEW.md'),
    'operational_manifest_sha256': file_hash(linux / 'EVIDENCE-MANIFEST.json'),
    'original_target_tail_sha256_normalized_outer_whitespace': sha(target.encode()),
    'original_target_same_as': [revision, base],
    'original_informal_files': before['original_informal_files'],
    'unchanged_other_canonical_entries': 216,
    'unchanged_registry_entries': 217,
    'registry_sha256': before['problem_ids_sha256'],
    'preserved_prior_lean_verified': before['prior_lean_verified'],
    'all_other_base_tracked_files_unchanged': len(preserved_base_files),
    'shared_infrastructure_same_as_verified_revision': shared_paths,
    'yaml_semantic_changes_only': changed_yaml_fields,
    'export_names': config['theorem_names'],
    'axiom_whitelist': config['permitted_axioms'],
    'attribution': {'formalizer': 'George Stepaniants', 'affiliation': affiliation,
                    'mathematical_author': 'Matthew J. Colbrook', 'new_email_addresses': []},
    'branch_counts': dict(status_counts),
    'publication_hashes': {rel: file_hash(repo / rel) for rel in sorted(expected_changes)},
    'check_and_render_record_hashes': check_hashes,
    'pdf_review': {
        'pages': 2,
        'reviewed': [1, 2],
        'result': 'PASS: both final pages visually inspected; complete formulas, readable links and code, correct credits, no clipping or missing glyphs. The initial three-page layout was condensed to avoid a nearly empty third page; the original target is unchanged.',
        'png_sha256': {f'page-{number}.png': file_hash(image_dir / f'page-{number}.png') for number in [1, 2]},
        'parent_independent_visual_review': 'pending',
    },
    'no_publication_commit_push_or_pull_request_by_preparer': True,
}
(publication / 'integrity.json').write_text(json.dumps(output, indent=2) + '\n')
print(json.dumps({key: output[key] for key in ['result', 'integration_commit',
    'unchanged_verified_input_count', 'retained_linux_evidence_files',
    'all_other_base_tracked_files_unchanged', 'branch_counts', 'publication_hashes']}, indent=2))
