"""Adapt the same independent reviewer's sealed MF16/IS03 runtime audit logic.
Actual RA08 source count, module list, exports and graph counts were read first.
No original raw artifact or source identity is shared between the two runs.
"""
from pathlib import Path
import hashlib,json
O=Path(__file__).resolve().parent
T=Path('/tmp/nla-lean-mf16-worktree/matrix-functions-and-stability/MF-16/lean/verification/linux-2026-09-12')
old=(T/'runtime_audit.py').read_text()
s=old.replace('MF-16','RA-08').replace('MF16','RA08')
replacements={
 '==294':'==613','== 294':'== 613',
 "'candidate_source_inputs_matched_to_actual_receipt':294":"'candidate_source_inputs_matched_to_actual_receipt':613",
 "'candidate_inputs':294":"'candidate_inputs':613",
 "len(names)==9":"len(names)==14",
 "'exports':9":"'exports':14",
 'PASS (9 declarations)':'PASS (14 declarations)',
 '==22':'==59','== 22':'== 59',
 "'actual_standard_three_axiom_reports':22":"'actual_standard_three_axiom_reports':59",
 "'actual_standard_three_reports':22":"'actual_standard_three_reports':59",
 '[2840,2863]':'[2710,3161]',
 "['Definitions', 'Algebra', 'Recovery', 'Polynomial', 'CayleyHamilton', 'Numerical', 'Proof']":
 "['Definitions','Basis','Certificate','Fourth','Functional','Location','Numerical','OrderedExistence','Polynomial','ProjectionNorm','Proof','Scalar','Spectral','SpectralCFC','Tails','Witness']"
}
for a,b in replacements.items():
    if a=='== 294' and a not in s:continue
    assert a in s,a
    s=s.replace(a,b)
(O/'source/MF16-runtime-template.py.txt').write_text(old)
(O/'runtime_audit.py').write_text(s)
a=(T/'archive_candidate.py').read_text()
begin=a.index('from pathlib')
a='"""Retain one exact RA08 candidate source snapshot from committed Git blobs.\\nNo dependency object, artifact redownload, or proof rebuild is involved.\\n"""\\n'.replace('\\n','\n')+a[begin:]
a=a.replace("'change_from_initial_disk_plan':'With recovered headroom, retain one small immutable full source snapshot so publication wrapper changes preserve evidence.'",
 "'snapshot_purpose':'Retain one immutable full source snapshot so later publication wrapper changes preserve exact evidence.'")
(O/'archive_candidate.py').write_text(a)
(O/'runtime-inspector-adaptation.json').write_text(json.dumps({'template':'source/MF16-runtime-template.py.txt',
 'template_sha256':hashlib.sha256(old.encode()).hexdigest(),'actual_RA08_replacements':replacements,
 'namespace_changes':['MF16 -> RA08','MF-16 -> RA-08'],
 'generated_runtime_sha256':hashlib.sha256(s.encode()).hexdigest(),'common_control_assertions':'Preserved with actual original RA08 job/artifact bytes, not a reused control result.',
 'candidate_or_checker_configuration_change':False},indent=2)+'\n')
print('Prepared RA08 actual runtime inspector and immutable candidate snapshot driver')
