#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,sys
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5];PRIOR=BASE.parent/'independent-explicit-frame-review'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
shutil.copyfile(PRIOR/'source_inventory.py',BASE/'source_inventory.py');sys.path.insert(0,str(BASE));from source_inventory import declarations_of
specs=[('header_program','campaign-2026-10-25/header-product-author/source-lock.json','4af4a5975bcfe6896fe2abe5b1e98fbbd923570fed3b055102d4c79811d468a2'),('original_header','campaign-2026-10-23/shape-header-original-author-2026-10-26/source-lock.json','33a4e52566c33b9b5e9319076436f883c9cda91b65c2fe52f21f22c246ee6223'),('original_frobenius','campaign-2026-10-23/squared-error-original-author-2026-10-26/source-lock.json','a7cda1ef20bceeb98ab93de1cf49c2c4fd95c624d727264d1ea31103adac59bd')]
endpoints={
'header_program':['RoutineEmbedding.ordinary_iterate_relates','RoutineEmbedding.ordinary_iterate_natural_outside','headerProduct_initial','headerProduct_decode','headerProduct_iterations','headerProduct_trace_result','headerProduct_trace_cost','headerProduct_return_running','RoutineEmbedding.headerProduct_run_at'],
'original_header':['inputMemory_shapeHeader','shapeHeaderValues_product','shape_sum_modes_le_denseSize','shape_suffix_le_denseSize','headerPrefixProduct_shape_le','headerProductTime_shape_le_size','shape_headerProduct_trace_exists','shape_headerProduct_trace_result'],
'original_frobenius':['originalRadixIndexEquiv_eq_decode','tensor_memory_cells_iff','squaredErrorSum_eq_frobeniusSq','squaredErrorTime_shape_le_size','RoutineEmbedding.squaredError_run_frobenius']}
def norm(p):return p if p.startswith('lean-statements/') else 'lean-statements/'+p
blocks=[];union={}
for key,rel,digest in specs:
 p=REPO/'docs/lean/proofs/TR-04'/rel;assert sha(p)==digest;d=json.loads(p.read_text());records=[dict(r,path=norm(r['path'])) for r in d['project_closure']]
 for r in records:
  assert sha(REPO/r['path'])==r['sha256'],r['path']
  if r['path'] in union:assert union[r['path']]['sha256']==r['sha256']
  union[r['path']]=r
 owned=d.get('authored_sources')
 if owned is None:owned=[r for r in records if Path(r['path']).stem in d['authored_modules']]
 owned=[dict(r,path=norm(r['path'])) for r in owned]
 decls=[v for r in records for v in declarations_of(r['path'].removeprefix('lean-statements/'),(REPO/r['path']).read_bytes())];ownednames=sorted(v['name'] for v in decls if norm(v['source']) in {r['path'] for r in owned})
 assert set(ownednames)==set(d['authored_declarations']),(key,ownednames)
 for v in d.get('reviewed_original_inputs',d.get('unchanged_boundary_and_pins',[])):assert sha(REPO/v['path'])==v['sha256']
 blocks.append({'key':key,'author_lock_path':str(p.relative_to(REPO)),'author_lock_sha256':digest,'author':d['author'],'records':records,'owned':owned,'declarations':decls,'owned_declarations':ownednames,'roots':d['targets'],'literal_endpoints':['NLA.Proofs.TR04.'+n for n in endpoints[key]]})
 print(key,len(records),'sources',len(owned),'owned',len(ownednames),'authored names')
config={'reviewer':'/root/recover_verification','self_authored_proof_sources':[],'scope':'Frozen original-boundary machine components: header initialization program, exact shape/Start bridge, and actual squared-error/Frobenius bridge. Shared fresh producer snapshot with three separate exact-type consumers. No full finite RAM approximation program, full Target, total polynomial cost, Linux or Comparator acceptance claim.','blocks':blocks,'union':list(union.values()),'inventory_helper_provenance':{'prior_path':str((PRIOR/'source_inventory.py').relative_to(REPO)),'sha256':sha(PRIOR/'source_inventory.py'),'change':'Exact copy.'}}
(BASE/'source-lock.json').write_text(json.dumps(config,indent=2)+'\n')
s=(PRIOR/'replay.py').read_text().replace('len(frozen)==51',"len(frozen)==len(config['union'])").replace('==53','==len(frozen)+len(consumers)').replace('/53 ','/{len(frozen)+len(consumers)} ')
old="kind='theorem' if d['kind'] in {'theorem','lemma'} else 'inductive' if d['kind'] in {'inductive','structure'} else 'definition'";new="kind='theorem' if d['kind'] in {'theorem','lemma'} or d['name']=='NLA.Proofs.TR04.squaredErrorProgram_nonzero_realRegisters' else 'inductive' if d['kind'] in {'inductive','structure'} else 'definition'";assert old in s;s=s.replace(old,new)
s=s.replace("'kind_check_count':len(kinds),","'kind_check_count':len(kinds),'actual_kernel_theorem_count':sum(kind=='theorem' for _,kind in kinds),'actual_owned_kernel_theorem_count':sum(kind=='theorem' and name in b['owned_declarations'] for name,kind in kinds),")
# Every closure now uses matrix/real syntax, but InnerProductSpace need not be imported.
s=s.replace('open scoped BigOperators Matrix InnerProductSpace','open scoped BigOperators Matrix')
(BASE/'replay.py').write_text(s)
print('UNION',len(union),'sources, consumers',len(blocks))
