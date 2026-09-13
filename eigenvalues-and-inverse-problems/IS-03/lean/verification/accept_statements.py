"""Root accepts two sealed independent statement approvals before any proof edit."""
from pathlib import Path
import datetime, hashlib, json, subprocess

P = Path(__file__).resolve().parents[1]
R = P.parents[2]
sha = lambda f: hashlib.sha256(Path(f).read_bytes()).hexdigest()
freeze_path = P / 'reviews/statement-freeze.json'
assert sha(freeze_path) == '588196a54decb127a814dc4860621505d6874a077295f3e30a782d7f28b8ac6c'
freeze = json.loads(freeze_path.read_text())
assert len(freeze['files']) == 34 and len(freeze['source_files']) == 10
for rel, digest in freeze['files'].items(): assert sha(P / rel) == digest, rel
for rel, digest in freeze['source_files'].items():
    assert sha(R / rel) == digest, rel
    b = subprocess.check_output(['git', 'show', freeze['base'] + ':' + rel], cwd=R)
    assert hashlib.sha256(b).hexdigest() == digest, rel
reports = {
 'reviews/statement-referee-1.md': '79d057b4608eb72826d1265f7e718f57855907cfdd3283ab791bbbc98321f71a',
 'reviews/statement-referee-2.md': 'cca3fa8d9627d3ca91f64286a216ee102d137eb711f5c47ce945c519bda9ea70'}
manifests = {
 'reviews/statement-referee-1-evidence/EVIDENCE-MANIFEST.json': '71c1789f34770665834324143edd1a8dad5a55531404be24e2b309a0e30dd964',
 'reviews/statement-referee-2-evidence/EVIDENCE-MANIFEST.json': '90628b3315e31f6a33c8d5a1ec8292e9eded24b7bc5e4a52bbdb07f41dfe268d'}
for rel, digest in reports.items(): assert sha(P / rel) == digest
evidence = {}
for rel, digest in manifests.items():
    f = P / rel; assert sha(f) == digest
    m = json.loads(f.read_text())
    actual = {t.resolve() for t in f.parent.rglob('*') if t.is_file() and t != f}
    bound_internal = set()
    for name, rec in m['files'].items():
        t = f.parent / name
        assert sha(t) == rec['sha256'] and t.stat().st_size == rec['bytes'], name
        if t.resolve().is_relative_to(f.parent.resolve()): bound_internal.add(t.resolve())
    assert actual == bound_internal
    evidence[rel] = {'sha256': digest, 'bound_files': len(m['files']),
                     'internal_files': len(actual), 'complete_inventory': True}
assert not (P / 'NLA/IS03/Proof.lean').exists()
assert not (P / 'Solution.lean').exists()
assert '**Status:** Solved' in (P.parent / 'README.md').read_text()
out = P / 'verification/proof-start.json'
assert not out.exists()
record = {'phase': 'PROOF IMPLEMENTATION AUTHORIZED after two independent statement approvals',
 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'coordinator': '/root', 'coordinator_role': 'Statement coauthor, not an independent statement referee',
 'independent_statement_reviewers': ['/root/leancert_examples', '/root/formal_review_standards'],
 'statement_freeze_sha256': sha(freeze_path), 'preserved_statement_inputs': 34,
 'preserved_original_source_Git_blobs': 10, 'reports': reports, 'evidence': evidence,
 'root_review': 'Both complete sealed reports, final Definitions, all seven Challenge signatures, numerical targets and source correspondence read. Their exact unrestricted real-matrix target and numerical values are accepted without correction; all evidence bytes and source identities independently rechecked. Prior full canonical/manuscript reading retained.',
 'obligations': 'Prove the full arbitrary-matrix characteristic-polynomial-to-trace bridge for all seven moments. No assumed diagonalizability or separability, nor companion-only substitute. Derive any spectral property actually used. Material kernel LeanCert negative rational certificate must feed the complete original universal negation. Frozen definitions, targets, Challenge and pins remain unchanged.',
 'proof_absent_at_gate': True, 'canonical_status': 'Solved, unchanged',
 'completed_proof_final_reviews_Linux_and_publication': 'pending'}
out.write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({'status': 'PASS: proof gate open', 'gate_sha256': sha(out), 'evidence': evidence}, indent=2))
