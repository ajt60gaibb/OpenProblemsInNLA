from pathlib import Path
from datetime import datetime, timezone
import collections
import copy
import hashlib
import json
import re
import subprocess
import yaml

repo = Path('/tmp/nla-lean-tr15-worktree')
entry = repo / 'tensor-computations/TR-15'
project = entry / 'lean'
pub = project / 'verification/publication-2026-09-12'
linux = project / 'verification/linux-2026-09-12'
before = json.loads((pub / 'before.json').read_text())

def sha(data):
    return hashlib.sha256(data).hexdigest()

def file_hash(path):
    return sha(path.read_bytes())

def git(*args):
    return subprocess.check_output(['git', *args], cwd=repo)

assert git('rev-parse', 'HEAD').decode().strip() == before['integrated_head']
identity = git('show', '-s', '--format=%an%x00%ae%x00%cn%x00%ce', 'HEAD').rstrip(b'\n').split(b'\0')
assert identity == [b'George Stepaniants', b'', b'George Stepaniants', b'']
changes = {name: {'verified_sha256': expected, 'current_sha256': file_hash(project / name)}
           for name, expected in before['all_verified_inputs'].items()
           if file_hash(project / name) != expected}
assert set(changes) == {'README.md', 'formalization.yaml'}
assert len(before['all_verified_inputs']) == 135
for name, expected in before['all_verified_inputs'].items():
    assert expected == sha(git('show', before['verified_revision'] + ':tensor-computations/TR-15/lean/' + name))
for name, expected in before['all_operational_evidence'].items():
    assert file_hash(project / name) == expected, name
assert len(before['all_operational_evidence']) == 254
assert {str(p.relative_to(project)) for p in linux.rglob('*') if p.is_file()} == set(before['all_operational_evidence'])
outer = linux / 'EVIDENCE-MANIFEST.json'
evidence = json.loads(outer.read_text())
assert {str(p.relative_to(linux)) for p in linux.rglob('*') if p.is_file() and p != outer} == set(evidence['files'])
for name, expected in evidence['files'].items():
    data = (linux / name).read_bytes()
    assert sha(data) == expected['sha256'] and len(data) == expected['bytes']
assert len(evidence['files']) == 253

canonical = (entry / 'README.md').read_text()
tail = canonical[canonical.index('## Statement'):]
assert sha(tail.encode()) == before['canonical_target_tail_sha256']
for rev in [before['base'], before['verified_revision']]:
    original = git('show', rev + ':tensor-computations/TR-15/README.md').decode()
    assert original[original.index('## Statement'):] == tail
registry = json.loads((repo / 'problem_ids.json').read_text())
assert file_hash(repo / 'problem_ids.json') == before['problem_ids_sha256']
assert len(registry) == 217 and len(before['other_canonical']) == 216
for ident, expected in before['other_canonical'].items():
    assert file_hash(repo / registry[ident]) == expected, ident
expected_changes = {
    'CATALOG.md', 'README.md', 'RESOLVED.md', 'tensor-computations/README.md',
    'tensor-computations/TR-15/README.md',
    'tensor-computations/TR-15/problem.tex',
    'tensor-computations/TR-15/problem.pdf',
    'tensor-computations/TR-15/lean/README.md',
    'tensor-computations/TR-15/lean/formalization.yaml',
}
actual_changes = set(git('diff', '--name-only', 'HEAD').decode().splitlines())
assert actual_changes == expected_changes, actual_changes ^ expected_changes

current = yaml.safe_load((project / 'formalization.yaml').read_text())
original = yaml.safe_load(git('show', before['verified_revision'] + ':tensor-computations/TR-15/lean/formalization.yaml'))
remaining = copy.deepcopy(current)
fields = [('status', 'scope'), ('review', 'status'), ('review', 'notes'),
          ('review', 'linux_verification', 'status'), ('review', 'linux_verification', 'note')]
for names in fields:
    a, b = remaining, original
    for name in names[:-1]:
        a, b = a[name], b[name]
    assert a[names[-1]] != b[names[-1]]
    a[names[-1]] = b[names[-1]]
assert remaining == original
config = json.loads((project / 'comparator.json').read_text())
assert [x['declaration'] for x in current['status']['main_results']] == config['theorem_names']
assert len(config['theorem_names']) == 7
assert current['project']['authors'] == ['George Stepaniants']
affiliation = current['project']['affiliations']['George Stepaniants']
assert affiliation == 'Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'
added = '\n'.join(line[1:] for line in git('diff', '--', '*.md', '*.yaml').decode().splitlines()
                  if line.startswith('+') and not line.startswith('+++'))
assert not re.findall(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}', added)
counts = collections.Counter(re.search(r'^\*\*Status:\*\*\s+([^\n]+)', (repo / path).read_text(), re.M).group(1).strip() for path in registry.values())
expected_counts = dict(before['branch_counts_before'])
expected_counts['Solved'] -= 1
expected_counts['Lean verified'] += 1
assert dict(counts) == expected_counts

local_links = []
for document in [entry / 'README.md', project / 'README.md']:
    for link in re.findall(r'\]\(([^)]+)\)', document.read_text()):
        if re.match(r'[a-z]+:', link):
            continue
        path = link.split('#')[0]
        assert (document.parent / path).exists(), (document, link)
        local_links.append({'document': str(document.relative_to(repo)), 'link': link})
pdfinfo = (pub / 'pdfinfo.log').read_text()
assert re.search(r'^Pages:\s+2$', pdfinfo, re.M)
assert not re.search(r'Overfull|Missing character', (pub / 'render.log').read_text())
pdftext = subprocess.check_output(['/opt/homebrew/bin/pdftotext', '-layout', str(entry / 'problem.pdf'), '-'])
(pub / 'pdf-text.txt').write_bytes(pdftext)
for required in ['Lean verified', 'Computing and Mathematical Sciences', 'California Institute of Technology', '6a2d086', '34716902324']:
    assert required in pdftext.decode(), required
images = sorted(Path('/tmp/nla-lean-formalization/tr15-publication/pages').glob('page-*.png'))
assert len(images) == 2
visual = {'reviewer': '/root/solved_statement_inventory',
          'result': 'PASS: both PDF pages individually displayed and visually inspected',
          'observations': 'Readable title, full attribution, seven exports, complete reproduction commands and original target/references; no clipping, overlap, missing glyphs or overfull warnings. Original source section and reference pagination retained by the unchanged renderer.',
          'pdf_sha256': file_hash(entry / 'problem.pdf'),
          'rendered_images': {str(p): file_hash(p) for p in images}}
(pub / 'visual-review.json').write_text(json.dumps(visual, indent=2) + '\n')
checks = []
for args, name in [
    (['git', 'diff', '--check', 'HEAD', '--', ':!**/verification/linux-2026-09-12/**'], 'scoped-diff-check'),
    (['python3', 'tools/format_math.py', '--check', 'TR-15'], 'final-format'),
]:
    result = subprocess.run(args, cwd=repo, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (pub / (name + '.log')).write_bytes(result.stdout)
    record = {'command': args, 'exit_code': result.returncode, 'log_sha256': sha(result.stdout)}
    checks.append(record)
    assert result.returncode == 0, result.stdout.decode()
(pub / 'final-checks.json').write_text(json.dumps(checks, indent=2) + '\n')
record = {
    'result': 'PASS: ready for independent parent publication review; no publication commit or push',
    'created_utc': datetime.now(timezone.utc).isoformat(),
    'verified_revision': before['verified_revision'],
    'verified_run': before['verified_run'],
    'upstream_base': before['base'],
    'integration_commit': before['integrated_head'],
    'integration_author_email': '', 'integration_committer_email': '',
    'verified_input_count': 135, 'only_changed_verified_inputs': changes,
    'unchanged_verified_inputs': 133, 'unchanged_operational_evidence_files': 254,
    'outer_evidence_manifest_complete_including_nested': True,
    'all_216_other_canonical_pages_unchanged': True,
    'original_target_and_references_tail_byte_identical': True,
    'original_informal_proof_and_all_shared_harness_files_unchanged': True,
    'permanent_ids': 217, 'status_counts_before': before['branch_counts_before'],
    'status_counts_after': dict(counts),
    'metadata_changed_fields_only': ['.'.join(x) for x in fields],
    'changed_tracked_files': sorted(expected_changes),
    'changed_file_sha256': {name: file_hash(repo / name) for name in sorted(expected_changes)},
    'local_links_checked': local_links,
    'no_email_added': True, 'pdf_pages_visually_checked': 2,
    'scoped_whitespace_check_excludes_immutable_linux_logs': True,
}
(pub / 'integrity.json').write_text(json.dumps(record, indent=2) + '\n')
(pub / 'finish.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({k: record[k] for k in ['result', 'integration_commit', 'unchanged_verified_inputs', 'unchanged_operational_evidence_files', 'status_counts_after', 'changed_tracked_files']}, indent=2))
