#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,sys
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5];PRIOR=BASE.parent/'independent-selector-tensor-review'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
shutil.copyfile(PRIOR/'source_inventory.py',BASE/'source_inventory.py');sys.path.insert(0,str(BASE));from source_inventory import declarations_of
specs=[('layout','campaign-2026-10-23/tt-memory-layout-author-2026-10-26/source-lock.json','e6b0ca4835dcdac42dea4a820dca3dddfae658f4b52390d00972984a9cad7de3'),('assembly','campaign-2026-10-26/tt-program-assembly-author/source-lock.json','8ba5869b692e3461689b98a77ae491473eba2b5638fc2c41f9f9e83db5a08398')]
endpoints={'layout':['NLA.Proofs.TR04.TTMemoryLayout.'+n for n in ['Layout.frame_fits','Layout.frames_disjoint','Layout.metadataCell_injective','Layout.candidates_disjoint','Layout.first_outputs_disjoint','Layout.child_outputs_disjoint','Layout.frame_workA_rectangle_disjoint','Layout.work_rectangle_disjoint','Layout.write_firstSVD_prefix','Layout.write_childSVD_work','Layout.write_firstSVD_later','Layout.write_childSVD_other_frame','Layout.endAddress_eq','ofShape_endAddress_le_size','ofShape_allocated_address_lt_size','Layout.contraction_inputsOutsideOutput','Layout.lifting_inputsOutsideOutput','Layout.contraction_leftMatrix','Layout.lifting_leftMatrix']],'assembly':['NLA.Proofs.TR04.'+n for n in ['installCodeBank_outside','installCodeBank_exit','trace_scalar_block_at','trace_svd_at','ttProgram_code_first_svd','ttProgram_code_child_svd','ttProgram_code_header_exit','ttProgram_code_matrix_exit','ttProgram_code_copy_exit','ttProgram_code_gather_exit','ttProgram_code_threshold_exit','ttProgram_code_best_exit','ttProgram_code_caller','ttProgram_svd_positions','ttHeader_initial_relates','ttProgram_trace_exists','ttProgram_header_result','ttProgram_header_natural_outside']]}
def norm(p):return p if p.startswith('lean-statements/') else 'lean-statements/'+p
blocks=[];union={}
for key,rel,digest in specs:
 p=REPO/'docs/lean/proofs/TR-04'/rel;assert sha(p)==digest;d=json.loads(p.read_text());records=[dict(r,path=norm(r['path'])) for r in d.get('project_closure',d.get('sources'))]
 for r in records:
  assert sha(REPO/r['path'])==r['sha256']
  if r['path'] in union:assert union[r['path']]['sha256']==r['sha256']
  union[r['path']]=r
 owned=d.get('authored_sources',d.get('authored_modules'));owned=[r for r in records if r['path'].removeprefix('lean-statements/') in owned or Path(r['path']).stem in owned] if isinstance(owned[0],str) else [dict(r,path=norm(r['path'])) for r in owned]
 decls=[v for r in records for v in declarations_of(r['path'].removeprefix('lean-statements/'),(REPO/r['path']).read_bytes())];ownednames=sorted(v['name'] for v in decls if norm(v['source']) in {r['path'] for r in owned})
 if d.get('authored_declarations') is not None:assert set(ownednames)==set(d['authored_declarations'])
 for v in d.get('unchanged_boundary_and_pins',[]):assert sha(REPO/v['path'])==v['sha256']
 blocks.append({'key':key,'author_lock_path':str(p.relative_to(REPO)),'author_lock_sha256':digest,'author':d.get('author','/root/recover_algebra'),'records':records,'owned':owned,'declarations':decls,'owned_declarations':ownednames,'roots':d.get('targets',['NLA.Proofs.TR04.MachineTensorMultiplyTrace']),'literal_endpoints':endpoints[key]})
 print(key,len(records),'sources',len(owned),'owned',len(ownednames),'authored names')
config={'reviewer':'/root/recover_verification','self_authored_proof_sources':[],'scope':'Frozen TT memory layout4 and finite program assembly4. Shared fresh private prerequisites, separately scoped consumers, exact allocation, generic bank installation, six literal embeddings, header prefix and actual SVD sites; no complete program correctness, total cost, Target, Linux or Comparator acceptance claim.','blocks':blocks,'union':list(union.values()),'inventory_helper_provenance':{'path':str((PRIOR/'source_inventory.py').relative_to(REPO)),'sha256':sha(PRIOR/'source_inventory.py'),'change':'Exact copy.'}}
(BASE/'source-lock.json').write_text(json.dumps(config,indent=2)+'\n');(BASE/'replay.py').write_text((PRIOR/'replay.py').read_text())
print('UNION',len(union),'sources')
