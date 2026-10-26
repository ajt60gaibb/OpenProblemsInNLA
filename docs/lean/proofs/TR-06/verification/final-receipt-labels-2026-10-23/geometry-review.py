#!/usr/bin/env python3
"""Independent exact-diff review of three already-fulfilled TR06 receipt labels."""
from pathlib import Path
import hashlib,json,subprocess
D=Path(__file__).resolve().parent
R=D.parents[5]
assert (R/'problem_ids.json').is_file()
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
q=json.loads((D/'request.json').read_text());before=(D/'before.yaml.txt').read_bytes();after=(D/'after.yaml.txt').read_bytes()
assert hashlib.sha256(before).hexdigest()==q['before_sha256']
assert hashlib.sha256(after).hexdigest()==q['after_sha256']
expected=before.decode()
for a,b in q['replacements'].items():
 assert expected.count(a)==1
 expected=expected.replace(a,b)
assert expected.encode()==after
package=R/'tensor-computations/TR-06/lean'
assert (package/'formalization.yaml').read_bytes()==after
prior=subprocess.check_output(['git','show',q['actual_promoted_source']+':tensor-computations/TR-06/lean/formalization.yaml'],cwd=R)
assert prior==before
ci=R/'docs/lean/proofs/TR-06/verification/promotion-linux-ci/5a9f6eef'
reports=[]
for name in ['root-review-2026-10-23.json','independent-review-2026-10-23.json']:
 p=ci/name;d=json.loads(p.read_text());assert d['passed'] and len(d['checks'])==45 and all(x['passed'] for x in d['checks']);assert d['source_commit']==q['actual_promoted_source'];assert len(d['inputs'])==153
 for x in d['inputs']:
  if x['path']=='formalization.yaml':assert x['expected_sha256']==q['before_sha256']
  else:assert h(package/x['path'])==x['expected_sha256'],x['path']
 assert len([x for x in d['inputs'] if x['path'].endswith('.lean')])==144
 reports.append({'path':str(p.relative_to(R)),'sha256':h(p),'checks':45,'passed':True})
changed=subprocess.check_output(['git','diff','--name-only','--','tensor-computations/TR-06/lean'],cwd=R,text=True).splitlines()
assert changed==['tensor-computations/TR-06/lean/formalization.yaml'],changed
result={'reviewer':'/root/recover_geometry','date':'2026-10-23','passed':True,'scope':'Independent review of exactly three already-fulfilled metadata receipt labels; no new mathematical approval or final tiny-commit Linux acceptance claim','request_sha256':h(D/'request.json'),'before_sha256':q['before_sha256'],'after_sha256':q['after_sha256'],'exactly_requested_three_values_changed':True,'all_152_other_package_inputs_and_144_Lean_sources_unchanged':True,'actual_promotion_strict45_reports':reports,'final_label_commit_exact_CI_still_required':True}
(D/'GEOMETRY_LABEL_REVIEW.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
