"""Parent review of completed-proof metadata and immutable candidate inputs; no Lean rerun."""
from pathlib import Path
import hashlib, json, re, subprocess, yaml

P = Path(__file__).resolve().parents[2]
R = P.parents[2]
O = Path(__file__).resolve().parent
sha = lambda f: hashlib.sha256(Path(f).read_bytes()).hexdigest()
before = json.loads((O / 'inputs-before.json').read_text())
assert len(before['preexisting_project_inputs']) == 166
for rel, item in before['preexisting_project_inputs'].items():
    f = P / rel if rel != 'README.md' else O / 'README.statement.md'
    assert sha(f) == item['sha256'] and f.stat().st_size == item['bytes'], rel
assert len(before['proof_frozen_inputs']) == 104
for rel, item in before['proof_frozen_inputs'].items():
    f = P / rel if rel != 'README.md' else O / 'README.statement.md'
    assert sha(f) == item['sha256'] and f.stat().st_size == item['bytes'], rel
for rel, digest in before['source_inputs'].items():
    b = subprocess.check_output(['git', 'show', before['base'] + ':' + rel], cwd=R)
    assert hashlib.sha256(b).hexdigest() == digest == sha(R / rel)
for rel, digest in before['report_sha256'].items(): assert sha(P / rel) == digest
for rel, item in before['review_evidence'].items():
    f = P / rel; assert sha(f) == item['sha256']
    m = json.loads(f.read_text())
    for name, rec in m['files'].items():
        t = f.parent / name
        assert sha(t) == rec['sha256'] and t.stat().st_size == rec['bytes'], name
outer = O / 'EVIDENCE-MANIFEST.json'
assert sha(outer) == 'e4ea6506d3458e620fb6d3dc27587411c0ee3983b133d78b454fd51495a3deaa'
m = json.loads(outer.read_text())
for rel, item in m['files'].items():
    f = O / rel; assert sha(f) == item['sha256'] and f.stat().st_size == item['bytes'], rel
for rel, item in m['current_metadata_relative_to_project'].items():
    f = P / rel; assert sha(f) == item['sha256'] and f.stat().st_size == item['bytes'], rel
doc = yaml.safe_load((P / 'formalization.yaml').read_text())
config = json.loads((P / 'comparator.json').read_text())
assert doc['version'] == 'v0.4'
assert [x['declaration'] for x in doc['status']['main_results']] == config['theorem_names']
assert [x['declaration'] for x in doc['alignment']] == config['theorem_names']
assert len(config['theorem_names']) == 8 and config['definition_names'] == []
assert set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
assert doc['review']['linux_verification']['status'] == 'pending'
for label in ['statement_reports', 'proof_reports']:
    assert len(doc['review'][label]) == 2
    for item in doc['review'][label]: assert sha(P / item['file']) == item['sha256']
for rel in ['README.md', 'formalization.yaml']:
    text = (P / rel).read_text(); flat = ' '.join(text.split())
    for required in ['George Stepaniants', 'Department of Computing and Mathematical Sciences',
                     'California Institute of Technology', 'Matthew J. Colbrook', 'Dokmanić', 'Gribonval']:
        assert required in flat, required
    assert not re.search(r'[\w.%+\-]+@[\w.\-]+\.[A-Za-z]{2,}', text)
assert not subprocess.check_output(['git', 'diff', '--name-only', 'HEAD'], cwd=R).strip()
registry = json.loads((R / 'problem_ids.json').read_text())
assert len(registry) == 217
for rel in registry.values():
    assert (R / rel).read_bytes() == subprocess.check_output(['git', 'show', before['base'] + ':' + rel], cwd=R)
assert '**Status:** Solved' in (P.parent / 'README.md').read_text()
cp = subprocess.run(['/tmp/nla-lean-formalization/venv/bin/python', 'tools/lean/validate_manifest.py',
                     'linear-systems-and-elimination/IE-23/lean'], cwd=R, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
assert cp.returncode == 0, cp.stdout.decode()
(O / 'root-schema.log').write_bytes(cp.stdout)
assert 'Ran 17 tests' in (O / 'permanent-id-tests.log').read_text()
record = {'status': 'APPROVE exact Linux candidate; actual Linux pending', 'reviewer': '/root',
    'role': 'Independent metadata review; prior final proof referee 2, not implementation author',
    'source_base': before['base'], 'unchanged_preexisting_nonREADME_inputs': 165,
    'unchanged_proof_nonREADME_inputs': 103, 'exact_old_README_archived': True,
    'original_source_blobs': 8, 'review_reports': before['report_sha256'],
    'review_evidence': before['review_evidence'], 'unchanged_canonical_pages_and_IDs': 217,
    'theorem_count': 8, 'canonical_status': 'Solved', 'Linux_status': 'pending',
    'metadata_sha256': {r: sha(P / r) for r in ['README.md', 'formalization.yaml']},
    'schema_exit': cp.returncode, 'schema_log_sha256': sha(O / 'root-schema.log'),
    'handoff_sha256': sha(O / 'CANDIDATE-HANDOFF.md'), 'preparer_manifest_sha256': sha(outer),
    'review_conclusion': 'Full complex norms/powers/supremum/right-inverse/global-minimum scope and all eight exports accurately described. Pure exact LeanCert kernel-auditor role, two independent statement/final reviewers, fixed-path historical runners and pending actual Linux correctly distinguished. No mathematical or metadata correction required.'}
(O / 'ROOT-CHECKS.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'root_checks_sha256': sha(O / 'ROOT-CHECKS.json'),
                  'preserved_nonREADME_proof_inputs': 103, 'exports': 8}))
