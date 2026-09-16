from pathlib import Path
import hashlib,json,re,subprocess,shutil
r=Path('/tmp/nla-lean-next-20260915');o=Path(__file__).parent;p=o/'inputs';repo='/Users/georgestepaniants/Research/OpenProblemsInNLA';commit='f3c22761166868df60938a27bdb08111dfc90f0d'
sha=lambda b:hashlib.sha256(b).hexdigest()
mods=['Words','Parameters','Norms','Tensor','MatrixAlgebra','Budgets','HolderBound']
records={}
for rel in [*(f'NLA/MF12/{m}.lean' for m in mods),'NLA/MF12/Definitions.lean','Challenge.lean']:
 gp='.lean-development/'+('Challenges/MF12.lean' if rel=='Challenge.lean' else rel)
 b=subprocess.check_output(['git','show',f'{commit}:{gp}'],cwd=repo)
 assert b==(p/rel).read_bytes(),rel
 blob=subprocess.check_output(['git','rev-parse',f'{commit}:{gp}'],cwd=repo,text=True).strip()
 records[rel]={'sha256':sha(b),'git_path':gp,'git_blob':blob,'matches_immutable_git':True}
challenge=(p/'Challenge.lean').read_text();allnames=re.findall(r'^theorem\s+(\w+)\b',challenge,re.M)
proof='\n'.join((p/f'NLA/MF12/{m}.lean').read_text() for m in mods)
exps=[]
def sig(s,n):
 m=re.search(r'\btheorem\s+'+re.escape(n)+r'\b([\s\S]*?)\s*:=',s)
 assert m,n
 return re.sub(r'\s+',' ',m.group(1)).strip()
for n in allnames:
 k=len(re.findall(r'^theorem\s+'+re.escape(n)+r'\b',proof,re.M))
 if k:
  assert k==1,n
  assert sig(proof,n)==sig(challenge,n),n
  assert '#assert_trust kernel '+n in proof,n
  assert '#print axioms '+n in proof,n
  exps.append(n)
assert len(exps)==14,exps
for m in mods:
 s=(p/f'NLA/MF12/{m}.lean').read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',s),m
 assert not re.search(r'^import\s+.*Challenge',s,re.M),m
 assert not re.search(r'^import\s+.*RootLimit',s,re.M),m
canonical={}
for gp in ['matrix-functions-and-stability/MF-12/README.md','references/colbrook-jsr-growth-2026-09-11/manuscripts/arbitrary_growth_exponents.tex']:
 b=subprocess.check_output(['git','show','8f04b905eb2e0827b6b84f37d9d080ae1f05b202:'+gp],cwd=repo)
 q=o/'canonical'/gp;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
 canonical[gp]={'sha256':sha(b),'git_blob':subprocess.check_output(['git','rev-parse','8f04b905eb2e0827b6b84f37d9d080ae1f05b202:'+gp],cwd=repo,text=True).strip()}
if (r/'NEXT-BATCH-6-FINAL.json').exists():shutil.copyfile(r/'NEXT-BATCH-6-FINAL.json',o/'NEXT-BATCH-6-FINAL.json')
result={'reviewer':'/root/next_elimination','implementation_author':'/root/next_matrix_functions','review_scope':'seven-module, fourteen-export mathematical source-only prefix','source_commit':commit,'inputs':records,'canonical_upstream_commit':'8f04b905eb2e0827b6b84f37d9d080ae1f05b202','canonical_sources':canonical,'accepted_source_export_names':exps,'excluded_remaining_export_names':[x for x in allnames if x not in exps],'fourteen_literal_types_match_frozen_challenge':True,'source_trust_diagnostics_present':True,'no_holes_axioms_native_or_challenge_imports':True,'lean_executed_by_referee':False,'comparator_or_default_kernel_acceptance_claim':False,'complete_MF12_acceptance_claim':False,'numeric_sampling_used_as_universal_proof':False}
(o/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'inputs_match_commit':True,'export_count':len(exps),'exports':exps,'excluded_count':len(allnames)-len(exps)},indent=2))
