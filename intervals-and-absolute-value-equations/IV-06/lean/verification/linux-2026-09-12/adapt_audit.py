"""Derive IV-06 evidence-only checks from the previously audited MI-03 pipeline."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
source=Path('/tmp/nla-lean-formalization/linux-mi03/audit_checks.py')
text=source.read_text()
text=text.replace('MI-03','IV-06').replace('MI03','IV06').replace('/tmp/nla-lean-mi03-worktree','/tmp/nla-lean-iv06-worktree').replace('matrix-inequalities-and-norms/IV-06/lean','intervals-and-absolute-value-equations/IV-06/lean')
text=text.replace("COMMIT = '901ba5ffad3b57557b60c7360df67659d8b8aa21'", "RUN_CONFIG = json.loads((OUT / 'run-config.json').read_text())\nCOMMIT = RUN_CONFIG['commit']")
text=text.replace("BASE = 'c0601d8825e9f9e744212c62e6a43fefc1c60a22'", "BASE = 'f41f1f9ffa2171550d4bb795862c6170c4f26070'")
text=text.replace('RUN = 34722618003', "RUN = RUN_CONFIG['run']\nassert RUN_CONFIG['problem'] == 'IV-06'")
text=text.replace('input_count = len(tracked)', "input_count = len(tracked)\ncommitted = json.loads((OUT / 'committed-candidate.json').read_text())\nassert committed['commit'] == COMMIT\nassert input_count == committed['complete_tracked_inputs'] == RUN_CONFIG['expected_candidate_inputs']\nassert set(committed['files']) == tracked\nfor rel, record in committed['files'].items():\n    assert record['sha256'] == receipt['input_sha256'][rel]")
start=text.index("pack = json.loads(")
end=text.index("lock_bytes = retain_source", start)
replacement=r'''preflight = json.loads((OUT / 'preflight.json').read_text())
pack = json.loads((WT / PROJECT / 'verification/linux-candidate-2026-09-12/integrity.json').read_text())
assert sha((WT / PROJECT / 'verification/linux-candidate-2026-09-12/integrity.json').read_bytes()) == preflight['packaging_integrity_sha256']
proof_freeze_bytes = (WT / PROJECT / 'verification/proof-freeze.json').read_bytes()
assert sha(proof_freeze_bytes) == preflight['proof_freeze_sha256'] == '5bc8cfd590e82a27807ad5f6832c0cc5d634832979241f80eb30d8d76eaaa673'
proof_freeze = json.loads(proof_freeze_bytes)
for rel, record in proof_freeze['files'].items():
    target = preflight['historical_README_archive'] if rel == 'README.md' else rel
    assert receipt['input_sha256'][target] == record['sha256']
    assert len(retain_source(PROJECT + '/' + target)) == record['bytes']
for rel, digest in pack['review_reports_and_manifests'].items():
    assert receipt['input_sha256'][rel] == digest == preflight['reports_and_manifests'][rel]
assert pack['review_reports_and_manifests']['reviews/proof-referee-1.md'] == 'fa9372a15b89f580959b9febb539d9b5c50e626b4a45672ff8848efce5e9ebc7'
assert pack['review_reports_and_manifests']['reviews/proof-referee-2.md'] == '3d333d14b69424f448e87b5d52984eda37585bf13023eb68890d2964dd534abc'
ref1 = json.loads((WT / PROJECT / 'reviews/proof-referee-1-evidence/integrity-final.json').read_text())
ref2 = json.loads((WT / PROJECT / 'reviews/proof-referee-2-root-evidence/audit.json').read_text())
assert ref1['status'] == 'PASS' and ref1['all_inputs_unchanged']
assert ref2['verdict'].startswith('PASS independent local final proof review')
assert ref1['proof_freeze_sha256'] == ref2['proof_freeze_sha256'] == sha(proof_freeze_bytes)
for rel, record in ref2['source_safety'].items():
    assert record['sha256'] == receipt['input_sha256'][rel] == proof_freeze['files'][rel]['sha256']
for ref in ['reviews/proof-referee-1.md', 'reviews/proof-referee-2.md']:
    assert sha(proof_freeze_bytes) in (WT / PROJECT / ref).read_text()
for manifest_rel, expected_count in pack['verified_review_evidence_counts'].items():
    manifest_path = WT / PROJECT / manifest_rel
    assert sha(manifest_path.read_bytes()) == pack['review_reports_and_manifests'][manifest_rel]
    bound = json.loads(manifest_path.read_text())['files']
    actual = {str(p.relative_to(manifest_path.parent)) for p in manifest_path.parent.rglob('*')
              if p.is_file() and p != manifest_path}
    if manifest_rel == 'reviews/proof-referee-2-root-evidence/EVIDENCE-MANIFEST.json':
        actual.add('../proof-referee-2.md')
    assert actual == set(bound) and len(bound) == expected_count
    for rel, record in bound.items():
        path = manifest_path.parent / rel
        assert path.stat().st_size == record['bytes'] and sha(path.read_bytes()) == record['sha256']
assert len(proof_freeze['files']) == pack['proof_frozen_inputs'] == preflight['proof_freeze_file_count']
assert len(proof_freeze['source_files']) == pack['original_source_git_blobs_unchanged']
assert pack['unchanged_nonwrapper_frozen_inputs'] == len(proof_freeze['files']) - 1
config = json.loads((WT / PROJECT / 'comparator.json').read_text())
names = ['eigenvalue_determinant_semantics', 'family_and_determinant_semantics',
         'witness_eigenpairs', 'witness_separators', 'connected_component_intervals',
         'four_components', 'counterexample', 'not_componentBoundConjecture']
assert config == receipt['config'] == preflight['config']
assert config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
assert config['definition_names'] == []
assert config['theorem_names'] == ['NLA.IV06.' + name for name in names] == proof_freeze['completed_exports']
assert receipt['input_sha256']['README.md'] == pack['current_README_sha256']
assert receipt['input_sha256']['formalization.yaml'] == pack['formalization_yaml_sha256']
candidate_manifest = WT / PROJECT / 'verification/linux-candidate-2026-09-12/EVIDENCE-MANIFEST.json'
assert sha(candidate_manifest.read_bytes()) == preflight['candidate_manifest_sha256']
candidate = json.loads(candidate_manifest.read_text())
for rel, record in candidate['files'].items():
    data = (candidate_manifest.parent / rel).read_bytes()
    assert sha(data) == record['sha256'] and len(data) == record['bytes']
root_manifest_path = candidate_manifest.parent / 'ROOT-EVIDENCE-MANIFEST.json'
assert sha(root_manifest_path.read_bytes()) == RUN_CONFIG['root_candidate_manifest_sha256']
root_manifest = json.loads(root_manifest_path.read_text())
actual_root_files = {str(path.relative_to(root_manifest_path.parent))
                    for path in root_manifest_path.parent.rglob('*')
                    if path.is_file() and path != root_manifest_path}
assert actual_root_files == set(root_manifest['files'])
assert len(actual_root_files) == root_manifest['file_count']
for rel, record in root_manifest['files'].items():
    data = (root_manifest_path.parent / rel).read_bytes()
    assert sha(data) == record['sha256'] and len(data) == record['bytes']
assert sha((candidate_manifest.parent / 'ROOT-CHECKS.json').read_bytes()) == RUN_CONFIG['root_candidate_acceptance_sha256']
for rel, digest in root_manifest['metadata_relative_to_project'].items():
    assert receipt['input_sha256'][rel] == digest

'''
text=text[:start]+replacement+text[end:]
text=text.replace("harness = retain_source('tools/lean/harness.py')\nnode", "harness = retain_source('tools/lean/harness.py')\nassert harness == git('show', '214c142d6bfe0f0c338808f188062acbbad0fb19:tools/lean/harness.py')\nnode")
text=text.replace("for module in ['Definitions', 'Modulus', 'UpperBound', 'Roots', 'Witness', 'Sharpness', 'Proof']:", "for module in ['Definitions', 'Proof']:")
text=text.replace("proof_freeze['kernel_assertion_count'] == 16", "proof_freeze['kernel_and_standard_three_checks'] == preflight['expected_kernel_assertions'] == 17")
text=text.replace("assert assertion_counts == {'NLA/IV06/Proof.lean': 8, 'Solution.lean': 8}", "assert assertion_counts == {'NLA/IV06/Proof.lean': 9, 'Solution.lean': 8}")
start=text.index("for rel in ['NLA/IV06/Proof.lean', 'Solution.lean']:\n    proof_source")
end=text.index("manifest = json.loads((WT / PROJECT / 'lake-manifest.json')",start)
text=text[:start]+r'''proof_source = (WT / PROJECT / 'NLA/IV06/Proof.lean').read_text()
assert 'set_option leancert.trust "kernel"' in proof_source
assert proof_source.count('interval_decide (trust := kernel)') == 1
assert re.search(r'theorem numerical_separator_margin\s*:\s*\(-18\s*:\s*ℝ\)\s*<\s*0', proof_source)
implementation_paths = sorted((WT / PROJECT / 'NLA/IV06').glob('*.lean')) + [WT / PROJECT / 'Solution.lean']
for path in implementation_paths:
    code = re.sub(r'/\-.*?\-/', '', path.read_text(), flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', code), str(path)
    assert not re.search(r'^import\s+Challenge\b', code, re.M)
ref1_dependencies = json.loads((WT / PROJECT / 'reviews/proof-referee-1-evidence/actual-dependencies.json').read_text())
ref1_certificate = json.loads((WT / PROJECT / 'reviews/proof-referee-1-evidence/certificate-audit.json').read_text())
assert ref1_certificate['status'] == 'PASS' and ref1_certificate['standard_three_only']
assert not ref1_certificate['native_execution_trust']
for required in ['LeanCert.Validity.verify_strict_upper_bound_dyadic_checked',
                 'NLA.IV06.numerical_separator_margin', 'NLA.IV06.witness_separators_proved',
                 'NLA.IV06.four_components_proved', 'NLA.IV06.counterexample_proved']:
    assert required in ref1_dependencies['actual_consumed'] and required in ref2['actual_required_dependencies']

'''+text[end:]
text=text.replace("'all_eleven_core_hashes_match_both_final_referee_evidence_sets': True,", "'all_core_hashes_match_both_final_referee_frozen_evidence_sets': True,")
text=text.replace("'independent_review_hashes': pack['independent_reports']", "'independent_review_hashes': pack['review_reports_and_manifests']")
text=text.replace("'Explicit kernel trust auditing of a pure exact proof; no numerical interval certificate. The exact all-k complex roots, CFC moduli, Euclidean operator norms, universal positive decomposition and actual IsLeast/infimum proof are bound to both independent final reviews by the actual verified input set.'", "'One materially consumed explicit kernel LeanCert point certificate for -18<0. Exact matrix, full-box affine, real connected-component and Cardinal proofs are bound to both independent final reviews by the actual verified input set. This operational audit did not repeat their mathematical proof reviews.'")
assert 'MI03' not in text and 'MI-03' not in text and 'mi03' not in text
compile(text,'audit_checks.py','exec')
(root/'audit_checks.py').write_text(text)
(root/'audit-script-provenance.json').write_text(json.dumps({'source':'/tmp/nla-lean-formalization/linux-mi03/audit_checks.py','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'adaptation':'Project-specific source, review and numerical certificate bindings replaced for IV-06; full actual control assertions retained. Exact run/commit required via run-config.json. All scripts are evidence-only; no candidate modification.','derived_sha256':hashlib.sha256(text.encode()).hexdigest(),'performed_at_preparation':'Python syntax check only; operational execution awaits actual successful artifacts'},indent=2)+'\n')
print('Prepared IV-06 evidence-only audit; syntax PASS; not executed against Linux artifacts')
