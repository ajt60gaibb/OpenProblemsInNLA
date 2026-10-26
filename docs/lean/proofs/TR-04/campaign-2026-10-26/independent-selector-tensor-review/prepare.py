#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,sys
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5];PRIOR=BASE.parent/'independent-threshold-scan-review'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
shutil.copyfile(PRIOR/'source_inventory.py',BASE/'source_inventory.py');sys.path.insert(0,str(BASE));from source_inventory import declarations_of
specs=[('selector','best-candidate-author-2026-10-26/source-lock.json','3988bced69ed9b9cac228b1d84270185c5210cfc92ad4bcebe90ec8d5e1a8819'),('tensor_operations','tensor-multiply-author-2026-10-26/source-lock.json','fa9b4c94f2da17a66af1b7dbb79e0a00e9535de1cf558363ed0677639631f826')]
endpoints={'selector':['NLA.Proofs.TR04.'+n for n in ['BestCandidateData.minimum_take','BestCandidateData.minimum_keep','bestCandidateProgram_initial','bestCandidateProgram_error','bestCandidateProgram_first','bestCandidateProgram_take','bestCandidateProgram_keep','bestCandidateProgram_trace_result','bestCandidateProgram_run','bestCandidateProgram_exists_trace','RoutineEmbedding.bestCandidate_run_at','RoutineEmbedding.bestCandidate_value_at']],'tensor_operations':['NLA.Proofs.TR04.TensorFormat.'+n for n in ['storesTensor_iff_flat','storesTensor_readMatrix_iff','radixOffset_merge_indices','storesTensor_merge_iff','storesTensor_unmerge_iff','storesFrame_dense_iff','storesFrame_prefix','storesTensor_original','contractMultiplyData_product','liftMultiplyData_product','contractMultiplyData_safe','liftMultiplyData_safe']]+['NLA.Proofs.TR04.RoutineEmbedding.contract_run_at','NLA.Proofs.TR04.RoutineEmbedding.lift_run_at']}
def norm(p):return p if p.startswith('lean-statements/') else 'lean-statements/'+p
blocks=[];union={}
for key,rel,digest in specs:
 p=REPO/'docs/lean/proofs/TR-04/campaign-2026-10-23'/rel;assert sha(p)==digest;d=json.loads(p.read_text());records=[dict(r,path=norm(r['path'])) for r in d.get('project_closure',d.get('sources'))]
 for r in records:
  assert sha(REPO/r['path'])==r['sha256']
  if r['path'] in union:assert union[r['path']]['sha256']==r['sha256']
  union[r['path']]=r
 owned=d['authored_sources'];owned=[r for r in records if r['path'].removeprefix('lean-statements/') in owned] if isinstance(owned[0],str) else [dict(r,path=norm(r['path'])) for r in owned]
 decls=[v for r in records for v in declarations_of(r['path'].removeprefix('lean-statements/'),(REPO/r['path']).read_bytes())];ownednames=sorted(v['name'] for v in decls if norm(v['source']) in {r['path'] for r in owned})
 if d.get('authored_declarations') is not None:assert set(ownednames)==set(d['authored_declarations'])
 for v in d.get('unchanged_boundary_and_pins',[]):assert sha(REPO/v['path'])==v['sha256']
 blocks.append({'key':key,'author_lock_path':str(p.relative_to(REPO)),'author_lock_sha256':digest,'author':d.get('author','/root/recover_algebra'),'records':records,'owned':owned,'declarations':decls,'owned_declarations':ownednames,'roots':d.get('targets',['NLA.Proofs.TR04.MachineTensorMultiplyTrace']),'literal_endpoints':endpoints[key]})
 print(key,len(records),'sources',len(owned),'owned',len(ownednames),'authored names')
config={'reviewer':'/root/recover_verification','self_authored_proof_sources':[],'scope':'Frozen best-candidate selector6 followed by tensor operational3. Shared fresh private source closure and two separately scoped consumers. Actual every-legal-trace minimum and physical contraction/lift memory/cost contracts; no whole approximation program, full Target, global complexity, Linux or Comparator acceptance claim.','blocks':blocks,'union':list(union.values()),'inventory_helper_provenance':{'path':str((PRIOR/'source_inventory.py').relative_to(REPO)),'sha256':sha(PRIOR/'source_inventory.py'),'change':'Exact copy.'}}
(BASE/'source-lock.json').write_text(json.dumps(config,indent=2)+'\n');s=(PRIOR/'replay.py').read_text();needle="'NLA.Proofs.TR04.thresholdScanProgram_nonzero_reals'}";assert needle in s;s=s.replace(needle,"'NLA.Proofs.TR04.thresholdScanProgram_nonzero_reals','NLA.Proofs.TR04.bestCandidateProgram_nonzero_realRegisters'}");needle="BASE/'integration-examples.lean.txt'";assert needle in s;s=s.replace(needle,"BASE/('integration-'+b['key']+'.lean.txt')");(BASE/'replay.py').write_text(s)
print('UNION',len(union),'sources')
