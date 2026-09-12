"""Independent root check after normal integration of newly merged upstream work."""
from collections import Counter
from pathlib import Path
import hashlib, json, re, subprocess, yaml

repo = Path(__file__).resolve().parents[5]
pub = Path(__file__).resolve().parent
prefix = 'matrix-inequalities-and-norms/MI-03/lean/'
project = repo / prefix
verified = '901ba5ffad3b57557b60c7360df67659d8b8aa21'
base = '5830ed4fb06da0659414a3deb2a40ad327aca052'
integration = 'd7f8c41104daf6d5c48783c368dd108734d74f96'
sha = lambda b: hashlib.sha256(b).hexdigest()
def git(*args): return subprocess.check_output(['git', *args], cwd=repo)
def blob(rev, path): return git('show', rev + ':' + path)
assert git('rev-parse', 'HEAD').decode().strip() == integration
assert git('show', '-s', '--format=%ae%x00%ce', integration).strip(b'\n') == b'\0'
for ancestor in [verified, base]:
    subprocess.run(['git', 'merge-base', '--is-ancestor', ancestor, integration], cwd=repo, check=True)
linux = project / 'verification/linux-2026-09-12'
receipt = json.loads((linux / 'artifacts/lean-MI-03/verify-20260912T222447Z-4133/result.json').read_text())
assert receipt['repository_commit'] == verified and receipt['project'] == prefix.rstrip('/')
assert receipt['config'] == json.loads((project / 'comparator.json').read_text())
assert len(receipt['input_sha256']) == 173
preserved = {}
for rel, digest in receipt['input_sha256'].items():
    assert sha(blob(verified, prefix + rel)) == digest, rel
    if rel not in ['README.md', 'formalization.yaml']:
        assert sha((project / rel).read_bytes()) == digest, rel
        preserved[rel] = digest
    else:
        archive = 'README.linux-candidate.md' if rel == 'README.md' else 'formalization.linux-candidate.yaml'
        assert sha((pub / 'archive' / archive).read_bytes()) == digest, rel
assert len(preserved) == 171
freeze = json.loads((project / 'reviews/proof-freeze.json').read_text())
assert len(freeze['files']) == 101 and len(freeze['source_files']) == 8
for rel, item in freeze['files'].items():
    digest = item if isinstance(item, str) else item['sha256']
    f = project / rel if rel != 'README.md' else project / 'verification/candidate-2026-09-12/README.statement.md'
    assert sha(f.read_bytes()) == digest, rel
for rel, digest in freeze['source_files'].items():
    assert sha(blob(freeze['source_commit'], rel)) == digest, rel
outer = linux / 'EVIDENCE-MANIFEST.json'
assert sha(outer.read_bytes()) == 'ecbdf4f208c72dd016442ca7dba5fd925b5c51286719454e5a58563460a610d9'
manifest = json.loads(outer.read_text())['files']
assert len(manifest) == 303
for rel, item in manifest.items():
    b = (linux / rel).read_bytes()
    assert sha(b) == item['sha256'] and len(b) == item['bytes'], rel
all_evidence = {str(f.relative_to(linux)): sha(f.read_bytes()) for f in linux.rglob('*') if f.is_file()}
assert len(all_evidence) == 304 and set(all_evidence) - set(manifest) == {'EVIDENCE-MANIFEST.json'}
assert sha((linux / 'OPERATIONAL-REVIEW.md').read_bytes()) == '0c582ae4b9271ce89cd9484a45d380f3cfa8cab60595a7986debcaa67c084e30'
registry = (repo / 'problem_ids.json').read_bytes()
assert registry == blob(base, 'problem_ids.json')
ids = json.loads(registry); assert len(ids) == 217
counts = Counter()
for code, rel in ids.items():
    b = (repo / rel).read_bytes()
    counts[re.search(rb'\*\*Status:\*\* ([^\r\n]+)', b).group(1).decode().strip()] += 1
    if code != 'MI-03':
        assert b == blob(base, rel), code
    else:
        tail = b.split(b'## Problem statement', 1)[1].strip()
        for revision in [base, verified]:
            assert tail == blob(revision, rel).split(b'## Problem statement', 1)[1].strip()
assert counts == {'Lean verified': 17, 'Solved': 75, 'Open': 53, 'Partially resolved': 72}, counts
names = ['CATALOG.md', 'README.md', 'RESOLVED.md', 'matrix-inequalities-and-norms/README.md',
    'matrix-inequalities-and-norms/MI-03/README.md', 'matrix-inequalities-and-norms/MI-03/problem.tex',
    'matrix-inequalities-and-norms/MI-03/problem.pdf', prefix + 'README.md', prefix + 'formalization.yaml']
assert set(git('diff', '--name-only').decode().splitlines()) == set(names)
other_files = 0
for item in git('ls-tree', '-r', '-z', base).split(b'\0'):
    if not item: continue
    metadata, name = item.split(b'\t', 1); rel = name.decode(); mode, kind, oid = metadata.split()
    if rel in names or rel.startswith(prefix): continue
    assert kind == b'blob' and mode in [b'100644', b'100755'], rel
    b = (repo / rel).read_bytes()
    assert oid == hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest().encode(), rel
    other_files += 1
assert other_files > 6500
for subtree in ['tools/lean', '.github', 'docs/lean']:
    assert git('ls-tree', '-r', base, '--', subtree) == git('ls-tree', '-r', verified, '--', subtree)
# Upstream changed only FR12/IE12 renderer branches, unrelated to MI03.
assert (repo / 'tools/render_problems.py').read_bytes() == blob(base, 'tools/render_problems.py')
pattern = rb'(?ms)^#### MI-03\b.*?(?=^#### MI-04\b)'
assert re.sub(pattern, b'', (repo / 'RESOLVED.md').read_bytes()) == re.sub(pattern, b'', blob(base, 'RESOLVED.md'))
old, new = [yaml.safe_load(b) for b in [blob(verified, prefix + 'formalization.yaml'), (project / 'formalization.yaml').read_bytes()]]
for key, subkey in [('status', 'scope'), ('review', 'status'), ('review', 'notes')]:
    old[key].pop(subkey); new[key].pop(subkey)
for key in ['status', 'note']:
    old['review']['linux_verification'].pop(key); new['review']['linux_verification'].pop(key)
assert old == new, 'Unexpected semantic metadata change'
prepared = pub / 'EVIDENCE-MANIFEST.json'
assert sha(prepared.read_bytes()) == '564bf0bf9417d33bef9a829f435d4814a38ac96059bc1184ab22425144b33072'
for rel, item in json.loads(prepared.read_text())['files'].items():
    b = (pub / rel).read_bytes()
    assert sha(b) == item['sha256'] and len(b) == item['bytes'], rel
integrity = json.loads((pub / 'integrity.json').read_text())
for rel, digest in integrity['changed_file_sha256'].items():
    if rel.startswith('matrix-inequalities-and-norms/MI-03/'):
        assert sha((repo / rel).read_bytes()) == digest, rel
visual = json.loads((pub / 'visual-review.json').read_text())
assert sha((repo / 'matrix-inequalities-and-norms/MI-03/problem.pdf').read_bytes()) == visual['pdf_sha256']
for name, digest in visual['rendered_images'].items():
    assert sha(Path(name).read_bytes()) == digest, name
for rel in [prefix + 'README.md', prefix + 'formalization.yaml', 'matrix-inequalities-and-norms/MI-03/README.md']:
    text = (repo / rel).read_text(); flat = ' '.join(text.split())
    for required in ['George Stepaniants', 'Department of Computing and Mathematical Sciences', 'California Institute of Technology', 'Matthew J. Colbrook']:
        assert required in flat, (rel, required)
    assert not re.search(r'[\w.%+\-]+@[\w.\-]+\.[A-Za-z]{2,}', text)
checks = json.loads((pub / 'root-integration/checks.json').read_text())
for c in checks:
    assert c['exit_code'] == 0 and sha((pub / 'root-integration' / c['log']).read_bytes()) == c['log_sha256']
assert 'Ran 17 tests' in (pub / 'root-integration/id-tests.log').read_text()
record = {'status': 'PASS independent root publication review', 'verified_revision': verified,
    'linux_run': 34722618003, 'upstream': base, 'integration': integration, 'blank_integration_emails': True,
    'verified_input_count': 173, 'unchanged_nonwrapper_inputs': preserved,
    'proof_freeze_nonREADME_inputs_preserved': 100, 'historical_README_archived': True,
    'original_source_Git_blobs': 8, 'all_retained_linux_files': all_evidence,
    'exact_linux_evidence_count': 304, 'outer_bound_count': 303,
    'other_canonical_pages_preserved': 216, 'permanent_IDs': 217,
    'all_other_upstream_files_preserved': other_files, 'other_RESOLVED_blocks_preserved': True,
    'branch_counts': dict(counts), 'prior_main_Lean_verifications_preserved': 16,
    'publication_sha256': {r: sha((repo / r).read_bytes()) for r in names},
    'pdf_review': 'Root independently displayed all three final PDF pages. Credits, formulas, text, links and commands are readable, with no clipping or missing glyphs. Same PDF bytes retained after integration; upstream renderer changes affect only FR12/IE12.',
    'proof_rebuild': 'Not repeated; proof, config, pins, reviewed source and all prior Linux evidence are unchanged.',
    'preparer_snapshot': 'Sealed f41 handoff remains unchanged historical evidence; root integration/checks separately bind the newly merged base.'}
(pub / 'ROOT-CHECKS.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({k: v for k, v in record.items() if k not in ['unchanged_nonwrapper_inputs', 'all_retained_linux_files', 'publication_sha256']}, indent=2))
