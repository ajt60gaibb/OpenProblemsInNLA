"""Independent parent review of IV-06 candidate metadata and frozen evidence."""
from pathlib import Path
import hashlib, json, re, subprocess, yaml

P = Path(__file__).resolve().parents[2]
R = P.parents[2]
O = Path(__file__).resolve().parent
sha = lambda f: hashlib.sha256(Path(f).read_bytes()).hexdigest()
before = json.loads((O / 'baseline.json').read_text())
assert sha(O / 'baseline.json') == 'fd476f58410cda4a5ebde1a38b2146f3c317aa337a78563bcae773c84ec9732e'
assert len(before['original_project_inputs']) == 184
for rel, rec in before['original_project_inputs'].items():
    f = O / 'README.statement.md' if rel == 'README.md' else P / rel
    assert sha(f) == rec['sha256'] and f.stat().st_size == rec['bytes'], rel
fp = P / 'verification/proof-freeze.json'
assert sha(fp) == '5bc8cfd590e82a27807ad5f6832c0cc5d634832979241f80eb30d8d76eaaa673'
freeze = json.loads(fp.read_text())
assert len(freeze['files']) == 126 and len(freeze['source_files']) == 8
for rel, rec in freeze['files'].items():
    f = O / 'README.statement.md' if rel == 'README.md' else P / rel
    assert sha(f) == rec['sha256'] and f.stat().st_size == rec['bytes'], rel
for rel, digest in before['source_files'].items():
    assert sha(R / rel) == digest
    b = subprocess.check_output(['git', 'show', before['base'] + ':' + rel], cwd=R)
    assert hashlib.sha256(b).hexdigest() == digest
for rel, digest in before['review_reports_and_manifests'].items(): assert sha(P / rel) == digest
evidence = {}
for rel, count in before['review_evidence_file_counts'].items():
    f = P / rel; m = json.loads(f.read_text())
    assert len(m['files']) == count
    actual = {t.resolve() for t in f.parent.rglob('*') if t.is_file() and t != f}
    internal = set()
    for name, rec in m['files'].items():
        t = f.parent / name
        assert sha(t) == rec['sha256'] and t.stat().st_size == rec['bytes'], name
        if t.resolve().is_relative_to(f.parent.resolve()): internal.add(t.resolve())
    assert actual == internal, rel
    evidence[rel] = {'sha256': sha(f), 'bound_files': count,
                     'internal_files': len(actual), 'complete_inventory': True}
outer = O / 'EVIDENCE-MANIFEST.json'
assert sha(outer) == '163a1617ea2551c284faa659fa5c2fed3423cb992325d756d011f403cbf9e080'
m = json.loads(outer.read_text())
assert len(m['files']) == 12
for rel, rec in m['files'].items():
    f = O / rel; assert sha(f) == rec['sha256'] and f.stat().st_size == rec['bytes'], rel
assert sha(O / 'integrity.json') == 'e8bbd3b25e878c077a5ea1924c9a405e8051c6f2efc969f9bb3957ea2d34e334'
doc = yaml.safe_load((P / 'formalization.yaml').read_text())
config = json.loads((P / 'comparator.json').read_text())
assert doc['version'] == 'v0.4'
assert [t['declaration'] for t in doc['status']['main_results']] == config['theorem_names']
assert [t['declaration'] for t in doc['alignment']] == config['theorem_names']
assert len(config['theorem_names']) == 8 and config['definition_names'] == []
assert set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
assert doc['review']['linux_verification']['status'] == 'pending'
for label in ['statement_reports', 'proof_reports']:
    assert len(doc['review'][label]) == 2
    for item in doc['review'][label]: assert sha(P / item['file']) == item['sha256']
for rel in ['README.md', 'formalization.yaml']:
    text = (P / rel).read_text(); flat = ' '.join(text.split())
    for required in ['George Stepaniants', 'Department of Computing and Mathematical Sciences',
                     'California Institute of Technology', 'Matthew J. Colbrook']:
        assert required in flat, required
    assert not re.search(r'[\w.%+\-]+@[\w.\-]+\.[A-Za-z]{2,}', text)
assert not subprocess.check_output(['git', 'diff', '--name-only', 'HEAD'], cwd=R).strip()
registry = json.loads((R / 'problem_ids.json').read_text()); assert len(registry) == 217
for rel in registry.values():
    assert (R / rel).read_bytes() == subprocess.check_output(['git', 'show', before['base'] + ':' + rel], cwd=R)
assert '**Status:** Solved' in (P.parent / 'README.md').read_text()
cp = subprocess.run(['/tmp/nla-lean-formalization/venv/bin/python', 'tools/lean/validate_manifest.py',
                     'intervals-and-absolute-value-equations/IV-06/lean'], cwd=R,
                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
assert cp.returncode == 0, cp.stdout.decode()
(O / 'root-schema.log').write_bytes(cp.stdout)
assert 'Ran 17 tests' in (O / 'permanent-id-tests.log').read_text()
record = {'status': 'APPROVE exact Linux candidate; actual Linux pending', 'reviewer': '/root',
 'role': 'Independent candidate metadata review; prior independent final proof referee 2, not implementation or packaging author',
 'source_base': before['base'], 'unchanged_preexisting_nonREADME_inputs': 183,
 'unchanged_proof_nonREADME_inputs': 125, 'exact_old_README_archived': True,
 'original_source_blobs': 8, 'review_reports_and_manifests': before['review_reports_and_manifests'],
 'review_evidence': evidence, 'unchanged_canonical_pages_and_IDs': 217,
 'theorem_count': 8, 'canonical_status': 'Solved', 'Linux_status': 'pending',
 'metadata_sha256': {rel: sha(P / rel) for rel in ['README.md', 'formalization.yaml']},
 'schema_exit': cp.returncode, 'schema_log_sha256': sha(O / 'root-schema.log'),
 'handoff_sha256': sha(O / 'CANDIDATE-HANDOFF.md'), 'preparer_manifest_sha256': sha(outer),
 'review_conclusion': 'Full original independent-entry real interval box, genuine nonzero eigenvector and determinant semantics, real subtype ConnectedComponents and Cardinal order, all eight exports, and material kernel LeanCert -18<0 are accurately described. Both independent statement and final proof approvals retained. Exact finite data and universal/topological bridges reviewed in the prior root proof report remain unchanged. Historical README finding closed by exact archive and truthful current guide. Actual Linux and operational/publication approval remain pending; no correction required.'}
(O / 'ROOT-CHECKS.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'root_checks_sha256': sha(O / 'ROOT-CHECKS.json'),
                  'preserved_nonREADME_proof_inputs': 125, 'exports': 8}))
