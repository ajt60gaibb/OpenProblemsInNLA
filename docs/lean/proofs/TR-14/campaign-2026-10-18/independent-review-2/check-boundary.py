from pathlib import Path
import hashlib,json,subprocess,os,platform,shutil,re
r=Path('/Users/ajt253/.codex/worktrees/tr14-lean-proof/OpenProblemsInNLA')
s=Path('/private/tmp/nla-sp12-lean-oct18')
out=Path('/private/tmp/nla-tr14-next-preproof/independent-review-2')
out.mkdir(parents=True,exist_ok=True)
src=out/'sources';src.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inputs=['AGENTS.md','problem_ids.json','tensor-computations/TR-14/README.md','tensor-computations/TR-14/problem.tex','tensor-computations/TR-14/problem.pdf','tensor-computations/TR-14/solution.tex','tensor-computations/TR-14/solution.pdf','references/holden-tr14-2026-09-12/README.md','references/holden-tr14-2026-09-12/independent-review.md','docs/lean/statements/TR-14/ORIGINAL.md','docs/lean/statements/TR-14/NUMERICAL_TARGETS.md','docs/lean/statements/TR-14/statement.json','lean-statements/NLA/Statements/Infrastructure.lean','lean-statements/NLA/Statements/TR14.lean','lean-statements/Reviewed/TR14.lean','lean-statements/lean-toolchain','lean-statements/lakefile.toml','lean-statements/lake-manifest.json','docs/lean/proofs/TR-14/EXACT_PROOF_PRE_REVIEW.md','docs/lean/proofs/TR-14/BINARY_UPPER_PRE_REVIEW_2026-10-16.md','docs/lean/proofs/TR-14/ORDINARY_LOWER_PRE_REVIEW_2026-10-16.md']
proofs=sorted((r/'lean-statements/NLA/Proofs/TR14').glob('*.lean'))
lock={'date':'2026-10-18','reviewer':'/root/fr05_statement','source_checkout':str(r),'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip(),'source_status':subprocess.check_output(['git','status','--porcelain'],cwd=r,text=True),'inputs':[],'candidate_proof_modules':[]}
assert lock['source_commit']=='fdb40b66425ec58e4806cee93d2aaf92a0f8597c';assert lock['source_status']==''
for name in inputs:
 p=r/name
 dst=src/name;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst)
 lock['inputs'].append({'path':name,'sha256':sha(p),'campaign_same_bytes':(s/name).exists() and sha(p)==sha(s/name)})
for p in proofs:
 lock['candidate_proof_modules'].append({'path':str(p.relative_to(r)),'sha256':sha(p),'imports':re.findall(r'^import\s+(\S+)',p.read_text(),re.M),'line_count':len(p.read_text().splitlines())})
assert len(proofs)==39
live=(r/'lean-statements/NLA/Statements/TR14.lean').read_text()
frozen=(r/'lean-statements/Reviewed/TR14.lean').read_text()
assert frozen.removeprefix('/- Frozen statement boundary. Changes reopen independent review. -/\n').replace('NLA.ReviewedStatements.TR14','NLA.Statements.TR14')==live
lock['live_frozen_identical_except_namespace_and_frozen_header']=True
lock['canonical_readme_matches_retained_original']=sha(r/'tensor-computations/TR-14/README.md')==sha(r/'docs/lean/statements/TR-14/ORIGINAL.md')
assert lock['canonical_readme_matches_retained_original']
assert json.loads((r/'problem_ids.json').read_text())['TR-14']=='tensor-computations/TR-14/README.md'
lock['registered_canonical_path']='tensor-computations/TR-14/README.md'
(out/'input-lock.json').write_text(json.dumps(lock,indent=2)+'\n')
objects=out/'objects';objects.mkdir(exist_ok=True)
bin=Path('/private/tmp/pf05-tooling/elan-home/toolchains/leanprover--lean4---v4.33.1/bin')
cache=s/'lean-statements/.lake/packages'
deps=[p/'.lake/build/lib/lean' for p in cache.iterdir() if(p/'.lake/build/lib/lean').is_dir()]
env=dict(os.environ,PATH=str(bin)+':'+os.environ['PATH'],LEAN_PATH=':'.join(map(str,[objects]+deps)))
result={'date':'2026-10-18','platform':platform.platform(),'scope':'Fresh isolated boundary source build only, no TR14 proof modules built or claimed verified.','builds':[]}
for name in ['NLA/Statements/Infrastructure.lean','NLA/Statements/TR14.lean','Reviewed/TR14.lean']:
 cwd=src/'lean-statements';p=cwd/name;dest=objects/Path(name).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 cmd=[str(bin/'lean'),'-o',str(dest),name];res=subprocess.run(cmd,cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 log=out/(name.replace('/','_')+'.log');log.write_text(res.stdout)
 row={'path':name,'sha256':sha(p),'command':cmd,'cwd':str(cwd),'exit_code':res.returncode,'log':log.name,'log_sha256':sha(log)}
 result['builds'].append(row)
 print(name,res.returncode,res.stdout.strip(),flush=True)
 assert res.returncode==0
result['pass']=True
(out/'boundary-build.json').write_text(json.dumps(result,indent=2)+'\n')
shutil.copy2(__file__,out/'check-boundary.py')
