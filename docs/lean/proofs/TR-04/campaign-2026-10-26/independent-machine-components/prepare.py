#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,shutil,sys
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5]
PRIOR=REPO/'docs/lean/proofs/TR-04/campaign-2026-10-25/independent-batch-review'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
shutil.copyfile(PRIOR/'source_inventory.py',BASE/'source_inventory.py');sys.path.insert(0,str(BASE));from source_inventory import declarations_of,without_comments
specs=[('matrix_multiply','matrix-multiply-author-2026-10-25/source-lock.json','a6c4e691c3d218a7318bddc0c4922833e542951dd01af51500c15aecbbc2a017'),('squared_error','machine-squared-error-author-2026-10-25/source-lock.json','f83c242ee2a645ba5f6b60124fd3fff0accb2192c9750ccfa76815d67751ebeb'),('matrix_callable','matrix-multiply-callable-author-2026-10-25/source-lock.json','ffe94faed554359e9fe68f8e487dac3e4188d75cd7b1ee62be3535ca307d5d36')]
endpoints={
'matrix_multiply':['MatrixMultiplyData.leftMatrix_dense','MatrixMultiplyData.rightMatrix_transpose','MatrixMultiplyData.productMatrix_entry','MatrixMultiplyData.dense_inputsOutsideOutput','matrixMultiplyProgram_exists_trace','matrixMultiplyProgram_trace_product','matrixMultiplyProgram_trace_cost','matrixMultiplyTime_le_cubic','matrixMultiplyProgram_run'],
'squared_error':['squaredErrorProgram_trace_result','squaredErrorProgram_trace_cost','RoutineEmbedding.squaredError_run_at','RoutineEmbedding.squaredError_run_value'],
'matrix_callable':['matrixMultiplyProgram_return','matrixMultiplyProgram_nohalt','RoutineEmbedding.matrixMultiply_run_at','RoutineEmbedding.matrixMultiply_product_at']}
def norm(p):return p if p.startswith('lean-statements/') else 'lean-statements/'+p
blocks=[];union={}
for key,rel,digest in specs:
 p=REPO/'docs/lean/proofs/TR-04/campaign-2026-10-23'/rel;assert sha(p)==digest
 d=json.loads(p.read_text());records=[dict(r,path=norm(r['path'])) for r in d.get('project_closure',d.get('sources'))]
 for r in records:
  assert sha(REPO/r['path'])==r['sha256'],r['path']
  if r['path'] in union:assert union[r['path']]['sha256']==r['sha256']
  union[r['path']]=r
 owned=d['authored_sources']
 if isinstance(owned[0],str):owned=[r for r in records if r['path'] in {norm(o) for o in owned}]
 else:owned=[dict(r,path=norm(r['path'])) for r in owned]
 decls=[v for r in records for v in declarations_of(r['path'].removeprefix('lean-statements/'),(REPO/r['path']).read_bytes())]
 ownednames=sorted(v['name'] for v in decls if norm(v['source']) in {r['path'] for r in owned})
 if d.get('authored_declarations') is not None:assert set(ownednames)==set(d['authored_declarations'])
 for r in d.get('unchanged_boundary_and_pins',[]):assert sha(REPO/r['path'])==r['sha256']
 roots=d.get('targets',['NLA.Proofs.TR04.MachineSquaredErrorTrace'])
 blocks.append({'key':key,'author_lock_path':str(p.relative_to(REPO)),'author_lock_sha256':digest,'author':d.get('author','/root/recover_algebra'),'records':records,'owned':owned,'declarations':decls,'owned_declarations':ownednames,'roots':roots,'literal_endpoints':['NLA.Proofs.TR04.'+n for n in endpoints[key]]})
 print(key,len(records),'closure',len(owned),'new',len(ownednames),'new named')
# NoEarlyHalt is frozen by the callable author lock and exact root-announced SHA.
callableblock=blocks[-1];byname={r['path'].removeprefix('lean-statements/').removesuffix('.lean').replace('/','.'):r for r in callableblock['records']};closure=[]
def visit(module):
 if module in closure:return
 assert module in byname,module
 data=(REPO/byname[module]['path']).read_bytes()
 for line in without_comments(data.decode()).splitlines():
  m=re.fullmatch(r'import\s+([A-Za-z0-9_.]+)\s*',line)
  if m and (REPO/'lean-statements'/(m[1].replace('.','/')+'.lean')).is_file():visit(m[1])
 closure.append(module)
visit('NLA.Proofs.TR04.MachineNoEarlyHalt');records=[byname[m] for m in closure];owned=[byname['NLA.Proofs.TR04.MachineNoEarlyHalt']];assert owned[0]['sha256']=='fa6db2ad40ea256bd82e1c8b75e641f4597bafe791f4261a1b022929271e7b46'
decls=[v for r in records for v in declarations_of(r['path'].removeprefix('lean-statements/'),(REPO/r['path']).read_bytes())];ownednames=sorted(v['name'] for v in decls if norm(v['source'])==owned[0]['path'])
blocks.insert(0,{'key':'no_early_halt','author_lock_path':callableblock['author_lock_path'],'author_lock_sha256':callableblock['author_lock_sha256'],'author':'/root','binding_note':'Exact root-announced source SHA also frozen as dependency in callable author source lock; no separate root proof claim is inferred.','records':records,'owned':owned,'declarations':decls,'owned_declarations':ownednames,'roots':['NLA.Proofs.TR04.MachineNoEarlyHalt'],'literal_endpoints':['NLA.Proofs.TR04.ordinary_running_prefix','NLA.Proofs.TR04.ordinary_nohalt_prefix_of_running']})
config={'reviewer':'/root/recover_verification','self_authored_proof_sources':[],'scope':'Frozen actual RAM components: no-early-halt bridge, strided matrix multiplication, squared-error sum and callable multiplication. Fresh shared private producer snapshot with separate literal consumers. No full TR04 Target, complete algorithm, global polynomial cost, Linux or Comparator acceptance claim.','blocks':blocks,'union':list(union.values()),'inventory_helper_provenance':{'prior_path':str((PRIOR/'source_inventory.py').relative_to(REPO)),'sha256':sha(PRIOR/'source_inventory.py'),'change':'Exact copy, including leading-indentation declaration support.'}}
(BASE/'source-lock.json').write_text(json.dumps(config,indent=2)+'\n')
s=(PRIOR/'replay.py').read_text().replace('len(frozen)==54','len(frozen)==len(config[\'union\'])').replace('==59','==len(frozen)+len(consumers)').replace('/59 ', '/{len(frozen)+len(consumers)} ').replace('open scoped BigOperators Matrix InnerProductSpace','open scoped BigOperators Matrix')
kind_old="kind='theorem' if d['kind'] in {'theorem','lemma'} else 'inductive' if d['kind'] in {'inductive','structure'} else 'definition'"
kind_new="kind='theorem' if d['kind'] in {'theorem','lemma'} or d['name']=='NLA.Proofs.TR04.squaredErrorProgram_nonzero_realRegisters' else 'inductive' if d['kind'] in {'inductive','structure'} else 'definition'"
assert kind_old in s;s=s.replace(kind_old,kind_new)
count_old="'kind_check_count':len(kinds),"
count_new="'kind_check_count':len(kinds),'actual_kernel_theorem_count':sum(kind=='theorem' for _,kind in kinds),'actual_owned_kernel_theorem_count':sum(kind=='theorem' and name in b['owned_declarations'] for name,kind in kinds),"
assert count_old in s;s=s.replace(count_old,count_new)
(BASE/'replay.py').write_text(s)
print('UNION',len(union),'sources;',len(blocks),'consumers;',len(records),'no-halt closure')
