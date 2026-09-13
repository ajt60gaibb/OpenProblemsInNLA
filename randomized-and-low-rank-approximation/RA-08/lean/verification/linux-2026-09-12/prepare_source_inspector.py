"""Adapt this reviewer's MF16 exact Git/input inspector to the actual RA08 formats."""
from pathlib import Path
import hashlib,json
O=Path(__file__).resolve().parent
T=Path('/tmp/nla-lean-mf16-worktree/matrix-functions-and-stability/MF-16/lean/verification/linux-2026-09-12/source_audit.py')
old=T.read_text();s=old.replace('MF-16','RA-08').replace('MF16','RA08')
replacements={
 "==294":"==613",
 "'candidate_input_count':294":"'candidate_input_count':613",
 "'candidate_inputs':294":"'candidate_inputs':613",
 "f4b21be066d0e55e56aae5b3fd1119433ef09d7ed5822d57dacab906b38ac720":"ab05e2bf801e6906453e88a4d84d5e73191f776db05610fb8b8e5e4a03d4f856",
 "eaba8311f143727f2061f2b4c945e403e62b7e9041712d983ef56ccf2e7f0587":"eb0460c3dd4c13a42f928e3f00c9c3710e486922b99aff74f4d6a3098c5ed332",
 "archive='verification/pre-candidate-README.md'":"archive={'README.md':'verification/pre-candidate-README.md','formalization.yaml':'verification/pre-candidate-formalization.yaml'}",
 "(proof,182),(statement,45)":"(proof,450),(statement,39)",
 "archive if n=='README.md' else n":"archive.get(n,n)",
 "len(proof['source_files'])==14":"len(proof['source_files'])==10",
 "baseline['input_count']==len(baseline['reviewer_entry_inputs'])==271":"baseline['original_project_input_count']==len(baseline['original_project_inputs'])==586",
 "baseline['reviewer_entry_inputs'].items()":"baseline['original_project_inputs'].items()",
 "'verification/linux-candidate-2026-09-12/formalization.initial.yaml' if n=='formalization.yaml' else n":"archive.get(n,n)",
 "assert len(nested)==7":"assert len(nested)==8",
 "5ce1d3313888dd2f8b95a9e23513e754841880725b017102b88aa92ce3494393":"bf9faf859b4184c4b27717e4eda8b482f272105eca0f693adf6a9643d91a6e4a",
 "cpj['file_count']==289":"cpj['file_count']==608",
 "root['preparer_input_count']==290":"root['preparer_input_count']==609",
 "94a681f53089ea8b45e9fc8e1760d015d00cfcd18af145a61c87c021aa021753":"ab7c97b219b098a9d6e1f72cad49e21d68a1ac37cd73f600d971aca5977de84d",
 "assert r['successful_direct_source_commands']==10 and r['exact_standard_three_reports']==26":"assert (r['successful_direct_source_commands'],r['exact_standard_three_reports'])==((20,61) if r['report']=='reviews/final-referee-1.md' else (19,62))",
 "==22":"==59",
 "['NLA/RA08/Numerical.lean','NLA/RA08/CayleyHamilton.lean','NLA/RA08/Proof.lean','Solution.lean']":"['NLA/RA08/Numerical.lean','NLA/RA08/Proof.lean']",
 "assert 'decide +kernel' in num and 'krawczykCheck_sound polynomialSystem rootBox rootCertificate {} actual_krawczyk_checked' in num":"assert 'interval_decide (trust := kernel)' in num and '0 < witnessGap' in num",
 "'proof_inputs':182,'statement_inputs':45":"'proof_inputs':450,'statement_inputs':39",
 "'archive_mapping':{'README.md':archive},'reviewer_entry_inputs_preserved':271":"'archive_mapping':archive,'reviewer_entry_inputs_preserved':586",
 "'packaging_bound_inputs':289,'packaging_outer_inputs':290":"'packaging_bound_inputs':608,'packaging_outer_inputs':609",
 "'embedded_kernel_assertions':22":"'embedded_kernel_assertions':59",
 "'final_review_26_count_scope':'Each final referee also checked four retained computational helper declarations; 22 assertions are embedded in the candidate itself.'":"'final_review_count_scope':'Referee 1 additionally checked two helper declarations, referee 2 three; 59 assertions are embedded in the candidate itself.'",
 "'material_LeanCert_scope':'Kernel full Krawczyk certificate and soundness theorem yield a genuine root, consumed via complete matrix-word bridge in all-complex positive-definite uniqueness negation.'":"'material_LeanCert_scope':'Actual kernel strict-upper-bound checker for constant zero on [0,0] against the positive exact rational gap; soundness feeds actual Rayleigh and all-basis original spectral-transfer negation.'",
 "'proof_coauthors':['/root/leancert_examples','/root/solved_statement_inventory','/root']":"'proof_coauthors':['/root/formal_review_standards','/root/solved_statement_inventory','/root']",
 "'nested_manifests':7":"'nested_manifests':8",
 "'exports':9":"'exports':14"
}
for a,b in replacements.items():
    assert a in s,a
    s=s.replace(a,b)
a=s.index("names=['word_semantics'")
b=s.index("\nconfig=json.loads",a)
s=s[:a]+"""names=['orderedSpectral_exists','orderedSpectral_semantics','functionalCalculus_spectral','spectral_tail_norms',
       'operator_rayleigh_bound','witness_data','witness_spectral_location','minorant_scalar',
       'minorant_functional_calculus','witness_tail_data','witness_rational_certificate',
       'numerical_gap_positive','counterexample','not_concaveSpectralTransferConjecture']"""+s[b:]
s=s.replace("assert proof['source_files']==statement['source_files']",
            "assert proof['source_files']==statement['source_files']\nassert proof['source_git_blobs']==statement['source_git_blobs']")
(O/'source').mkdir(exist_ok=True)
(O/'source/MF16-source-template.py.txt').write_text(old)
(O/'source_audit.py').write_text(s)
(O/'source-inspector-adaptation.json').write_text(json.dumps({'template':'source/MF16-source-template.py.txt',
 'template_sha256':hashlib.sha256(old.encode()).hexdigest(),'actual_RA08_replacements':replacements,
 'export_list':'Fourteen exact original RA08 exports, explicitly listed in generated inspector',
 'two_exact_archive_mappings':{'README.md':'verification/pre-candidate-README.md','formalization.yaml':'verification/pre-candidate-formalization.yaml'},
 'additional_git_check':'Proof and statement source Git blob maps must also agree',
 'generated_script_sha256':hashlib.sha256(s.encode()).hexdigest(),'mathematical_source_changed':False},indent=2)+'\n')
print('Prepared RA08 committed-source inspector with explicit format adaptations')
