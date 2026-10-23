#!/usr/bin/env python3
"""Independent preservation/claim review; no Lean source or promotion mutation."""
import collections, hashlib, json, pathlib, re, subprocess, zipfile
HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parents[6]
assert (REPO / 'problem_ids.json').is_file(), REPO
h = lambda b: hashlib.sha256(b).hexdigest()
file_h = lambda p: h(p.read_bytes())
lockpath = HERE.parent / 'source-lock.json'
expected_lock = '838f29c15e7804416b869c2c4d25bfbed2f5c15b46afdd35e390afbd73b5bcc7'
assert file_h(lockpath) == expected_lock
lock = json.loads(lockpath.read_text())
assert len(lock['records']) == 322
assert len({x['path'] for x in lock['records']}) == 322
for x in lock['records']:
    assert file_h(REPO / x['path']) == x['sha256'], x['path']
ci = REPO / 'docs/lean/proofs/TR-06/verification/linux-ci/2b049df5'
raw = ci / 'artifact/verify-20261023T224123Z-3965'
receipt = json.loads((raw / 'result.json').read_text())
commit = '2b049df5e9b15318987f3fa592b1a7c65a0c0057'
assert receipt['repository_commit'] == commit
assert receipt['result'] == 'comparator-accepted'
assert receipt['lean_cert_proof_trust'] == 'kernel-checked'
inputs = receipt['input_sha256']
assert len(inputs) == 153
package = REPO / 'tensor-computations/TR-06/lean'
lean_inputs = [x for x in inputs if x.endswith('.lean')]
assert len(lean_inputs) == 144
for x in inputs:
    b = subprocess.run(['git', 'show', commit + ':tensor-computations/TR-06/lean/' + x],
                       cwd=REPO, capture_output=True, check=True).stdout
    assert h(b) == inputs[x], x
mismatch = [x for x in inputs if file_h(package / x) != inputs[x]]
assert set(mismatch) == {'README.md', 'formalization.yaml'}, mismatch
assert all(file_h(package / x) == inputs[x] for x in lean_inputs)
for name in ['root-review-2026-10-23.json', 'independent-review-2026-10-23.json']:
    review = json.loads((ci / name).read_text())
    assert review['passed'] and len(review['checks']) == 45
    assert all(x['passed'] for x in review['checks'])
    assert len(review['inputs']) == 153 and len(review['copy_records']) == 140
    assert len(review['retained_records']) == 58
    for x in review['copy_records']:
        assert file_h(REPO / x['source']) == file_h(REPO / x['destination']) == x['source_sha256']
    for x in review['retained_records']:
        assert file_h(REPO / x['published_path']) == file_h(REPO / x['campaign_path']) == x['sha256']
    assert file_h(ci / 'artifact-12536268648.zip') == review['archive_sha256']
    assert file_h(ci / 'run-view.json') == review['github_metadata_sha256']
    assert file_h(ci / 'artifact-12536268648.json') == review['artifact_metadata_sha256']
with zipfile.ZipFile(ci / 'artifact-12536268648.zip') as z:
    members = [x for x in z.infolist() if not x.is_dir()]
    assert len(members) == 15
    for x in members:
        assert z.read(x.filename) == (ci / 'artifact' / x.filename).read_bytes(), x.filename
run = json.loads((ci / 'run-api.json').read_text())
assert run['head_sha'] == commit and run['event'] == 'push'
assert run['status'] == 'completed' and run['conclusion'] == 'success'
proof_trust = (raw / 'leancert-proof-trust.log').read_text()
assert 'EXIT_STATUS=0' in proof_trust
axioms = re.findall(r'depends on axioms: \[([^]]*)\]', proof_trust)
assert len(axioms) == 11
for x in axioms:
    assert set(x.strip() for x in x.split(',')) == {'propext', 'Classical.choice', 'Quot.sound'}
comp = (raw / 'comparator.log').read_text()
assert 'Lean default kernel accepts the solution' in comp and 'EXIT_STATUS=0' in comp
config = json.loads((package / 'comparator.json').read_text())
assert len(config['theorem_names']) == 11 and config['definition_names'] == []
canonical = json.loads((REPO / 'docs/lean/proofs/TR-06/campaign-2026-10-18/verification/CANONICAL_144_APPROVAL_2026-10-23.json').read_text())
for key, val in [('canonical_Lean_sources', 144), ('explicit_declarations_checked', 772),
                 ('positive_compile_commands', 145), ('negative_Challenge_rejections', 11)]:
    assert canonical[key] == val
assert canonical['passed'] and not canonical['authoritative_linux_comparator']
archivepath = REPO / 'docs/lean/proofs/TR-06/originals-c4c7be59/manifest.json'
archive = json.loads(archivepath.read_text())
assert len(archive['records']) == 5
for x in archive['records']:
    b = subprocess.run(['git', 'show', archive['base_ref'] + ':' + x['source']],
                       cwd=REPO, capture_output=True, check=True).stdout
    assert h(b) == file_h(REPO / x['archive']) == x['sha256'], x['source']
    if x['source'].startswith('references/'):
        assert file_h(REPO / x['source']) == x['sha256']
original = (REPO / 'docs/lean/proofs/TR-06/originals-c4c7be59/README.md').read_text()
current = (REPO / 'tensor-computations/TR-06/README.md').read_text()
stripped = re.sub(r'<!-- lean-tr06-complete-2026-10-23 -->.*?<!-- /lean-tr06-complete-2026-10-23 -->\n\n',
                  '', current, flags=re.S)
stripped = stripped.replace('**Status:** Lean verified', '**Status:** Solved').replace(
    '**Last checked:** 2026-10-23', '**Last checked:** 2026-09-11')
assert stripped == original
ids = json.loads((REPO / 'problem_ids.json').read_text())
assert len(ids) == 217 and ids['TR-06'] == 'tensor-computations/TR-06/README.md'
base_ids = subprocess.run(['git', 'show', 'origin/main:problem_ids.json'],
                          cwd=REPO, capture_output=True, check=True).stdout
assert base_ids == (REPO / 'problem_ids.json').read_bytes()
statuses = collections.Counter()
for path in ids.values():
    text = (REPO / path).read_text()
    statuses[re.search(r'^\*\*Status:\*\* ([^\n]+)', text, re.M).group(1).strip()] += 1
assert statuses['Lean verified'] == 84 and statuses['Solved'] == 34
qa = REPO / 'docs/lean/proofs/TR-06/verification/promotion-pdf-qa-2026-10-23'
visual = json.loads((qa / 'VISUAL_QA.json').read_text())
assert file_h(REPO / 'tensor-computations/TR-06/problem.pdf') == visual['pdf_sha256']
for name, digest in visual['page_sha256'].items():
    assert file_h(qa / name) == digest
# The two PNGs bound above were independently visually inspected through view_image.
for x in lock['records']:
    assert file_h(REPO / x['path']) == x['sha256'], x['path']
result = {
    'reviewer': '/root/recover_geometry', 'date': '2026-10-23', 'passed': True,
    'scope': 'Independent review of other-author publication/promotion changes and retained artifact evidence; no independent approval of this reviewer-authored TR06 proof bodies',
    'promotion_input_lock_sha256': expected_lock, 'frozen_input_count': 322,
    'source_commit_of_actual_linux_proof_evidence': commit,
    'checks': {
        'all_frozen_promotion_inputs_unchanged': True,
        'all_153_receipt_inputs_match_exact_proof_commit': True,
        'all_144_checked_Lean_inputs_still_identical': True,
        'only_two_descriptive_package_inputs_differ_since_proof_receipt': mismatch,
        'all_140_shared_copies_exact': True, 'all_58_retained_sources_exact': True,
        'all_5_original_archives_match_published_base': True,
        'original_README_unchanged_modulo_explicit_added_block_status_date': True,
        'retained_authorship_and_copyright_headers_preserved_by_full_source_identity': True,
        'all_217_ID_path_registry_bytes_match_origin_main': True,
        'both_retained_strict_replays_pass_45_controls': True,
        'raw_zip_all_15_files_match_exact_extraction': True,
        'actual_push_success_metadata_bound_to_proof_commit': True,
        'all_11_kernel_trust_reports_have_only_standard_three_axioms': True,
        'Comparator_default_kernel_acceptance_recorded': True,
        'canonical_fresh_audit_claims_match_separately_scoped_receipt': True,
        'counts_84_Lean_verified_34_Solved_match_canonical_pages': True,
        'all_two_latest_PNG_pages_visually_inspected': True,
        'no_clipping_overlap_missing_glyphs_or_target_split_observed': True,
        'publication_claims_explicitly_leave_fresh_promotion_Linux_pending': True
    },
    'visual_pdf_sha256': visual['pdf_sha256'], 'page_png_sha256': visual['page_sha256'],
    'limitations': [
        'This review did not rerun Lean, Linux Comparator or the strict replay checker; it independently checks retained actual artifacts, source identity and the correctness of the promotion claims.',
        'This reviewer authored geometry/model/retained-boundary mathematical support sources. Independent mathematical approval of those sources is excluded here and supplied by the separate other-author/full verifier reviews.',
        'The descriptive promotion has not yet obtained its own exact-input Linux receipt; approval is for the concrete frozen publication changes and their explicitly scoped proof-commit claims, with fresh promotion CI still required.'
    ]
}
(HERE / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
