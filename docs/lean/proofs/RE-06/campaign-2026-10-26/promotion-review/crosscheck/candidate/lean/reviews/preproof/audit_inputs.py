#!/usr/bin/env python3
"""Author preservation/signature audit only; no mathematical proof or approval."""
from pathlib import Path
import argparse,hashlib,json,subprocess
ap=argparse.ArgumentParser()
ap.add_argument('--packet',type=Path,default=Path(__file__).resolve().parent)
ap.add_argument('--repo',type=Path)
ap.add_argument('--reuse-repo',type=Path,default=Path('/Users/ajt253/Documents/OpenProblemsInNLA/campaign-workspaces/tr04'))
ap.add_argument('--output',type=Path,required=True)
a=ap.parse_args();p=a.packet.resolve();repo=a.repo or p.parents[2]
sha=lambda b:hashlib.sha256(b).hexdigest()
git=lambda r,*args:subprocess.check_output(['git','-C',str(r),*args])
checks=[]
def check(name,condition):
 checks.append({'check':name,'passed':bool(condition)})
 assert condition,name
lock=json.loads((p/'INPUT_LOCK.json').read_text());base=lock['published_base']
check('exact_published_commit',git(repo,'rev-parse',base).decode().strip()==base)
check('frozen_published_file_count',len(lock['files'])==49)
for row in lock['files']:
 b=(p/'originals'/row['path']).read_bytes()
 check('published:'+row['path'],sha(b)==row['sha256'] and len(b)==row['bytes'] and git(repo,'show',base+':'+row['path'])==b and git(repo,'rev-parse',base+':'+row['path']).decode().strip()==row['git_blob'])
registry=json.loads((p/'originals/problem_ids.json').read_text())
check('all_217_registry_pairs_exact',len(registry)==217 and registry==json.loads(git(repo,'show',base+':problem_ids.json')))
check('RE06_permanent_canonical_path',registry['RE-06']=='randomized-and-low-rank-approximation/RE-06/README.md' and lock['registry_pair']=={'RE-06':registry['RE-06']})
check('canonical_original_readme_identity',(p/'originals'/registry['RE-06']).read_bytes()==(p/'originals/docs/lean/statements/RE-06/ORIGINAL.md').read_bytes())
check('Sidney_Holden_credit',lock['credited_mathematical_author']=='Sidney Holden' and 'Sidney Holden' in (p/'originals/randomized-and-low-rank-approximation/RE-06/solution.tex').read_text())
reuse=json.loads((p/'REUSE_LOCK.json').read_text());ref=reuse['source_commit']
check('reuse_exact_commit',git(a.reuse_repo,'rev-parse',ref).decode().strip()==ref)
check('reuse_file_count',len(reuse['files'])==9)
for row in reuse['files']:
 b=(p/'supplementary-reuse'/row['path']).read_bytes()
 check('supplementary:'+row['path'],sha(b)==row['sha256'] and len(b)==row['bytes'] and git(a.reuse_repo,'show',ref+':'+row['path'])==b and git(a.reuse_repo,'rev-parse',ref+':'+row['path']).decode().strip()==row['git_blob'])
svd='lean-statements/NLA/Computation/SVDMachine.lean'
check('reused_SVD_model_exact_published_RE06',(p/'supplementary-reuse'/svd).read_bytes()==(p/'originals'/svd).read_bytes())
exports=json.loads((p/'EXPORTS.json').read_text())['exports']
check('exact_six_export_names',[e['name'] for e in exports]==['svd_total','query_bound','successful','original_claim','explicit_claim','target'])
challenge=(p/'Challenge.lean').read_text()
check('kernel_mode_option','set_option leancert.trust "kernel"' in challenge)
check('exact_six_intentional_challenge_holes',challenge.count('  sorry\n')==6 and challenge.count('#assert_trust kernel ')==6 and challenge.count('#print axioms ')==6)
for e in exports:
 header=f"theorem {e['name']} {e['binders']} :\n    {e['type']} := by\n  sorry"
 check('literal_challenge_header:'+e['name'],header in challenge)
manifest=json.loads((p/'originals/lean-statements/lake-manifest.json').read_text())
revs={q['name']:q['rev'] for q in manifest['packages']}
check('Lean_4_33_1',(p/'originals/lean-statements/lean-toolchain').read_text().strip()=='leanprover/lean4:v4.33.1')
check('Mathlib_exact_pin',revs['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474')
check('LeanCert_exact_pin',revs['leancert']=='621a43d7cf21f87872392a01e874f2f1dbddc926')
# Optional complete frozen packet audit. Do not overwrite its retained output in a replay.
if (p/'PACKET_LOCK.json').exists():
 for row in json.loads((p/'PACKET_LOCK.json').read_text())['files']:
  b=(p/row['path']).read_bytes()
  check('packet:'+row['path'],sha(b)==row['sha256'] and len(b)==row['bytes'])
a.output.parent.mkdir(parents=True,exist_ok=True)
a.output.write_text(json.dumps({'scope':'AUTHOR preservation/signature audit only; no independent approval, RE-06 proof, Comparator or CI claim.','published_base':base,'supplementary_commit':ref,'input_lock_sha256':sha((p/'INPUT_LOCK.json').read_bytes()),'reuse_lock_sha256':sha((p/'REUSE_LOCK.json').read_bytes()),'checks':checks,'check_count':len(checks),'passed':all(q['passed'] for q in checks)},indent=2)+'\n')
print(f'{len(checks)}/{len(checks)} preservation/signature checks passed')
