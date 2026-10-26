#!/usr/bin/env python3
"""Freeze independent audit inputs; does not edit proof or package sources."""
from pathlib import Path
import hashlib, json, re
BASE=Path(__file__).resolve().parent
REPO=BASE.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
old=REPO/'docs/lean/proofs/TR-04/campaign-2026-10-23/independent-svd-bridges-verification-2026-10-25/source_inventory.py'
helper=old.read_text()
needle='*)", line)'
assert helper.count(needle)==1
helper=helper.replace(needle,'*)", line.lstrip())')
(BASE/'source_inventory.py').write_text(helper)
from source_inventory import without_comments,declarations_of
specs=[
 ('recursive_tensor','campaign-2026-10-23/recursive-tensor-author-2026-10-25/source-lock.json','fd4f144ddcb75051d5eaf49c9c8c219f76b956a0de77007e803ba793b0df9c63'),
 ('svd_tie','campaign-2026-10-23/svd-tie-author-2026-10-25/source-lock.json','cb3f5d6594dc2373411ae6eda366d9bc2cc7a46a26dd67bbc3191e5e77f27b2e'),
 ('scalar_programs','campaign-2026-10-25/scalar-programs-author/source-lock.json','551c43d1ef32ddf406446c1e02cacb6d0e640eef4e231053360467c74f5c007d'),
 ('radix_interface','campaign-2026-10-23/radix-interface-author-2026-10-25/source-lock.json','c8c40258fc55ef6ccc8cab619aff0ba667c9721ceda403c6dae5ba4e16b68d06'),
 ('svd_memory','campaign-2026-10-23/machine-svd-memory-author-2026-10-25/source-lock.json','d82b1ad398e4c13e69acfe21c074759f0917300ebe05b117f1d4728431fa8525')]
endpoints={
 'recursive_tensor':('NLA.Proofs.TR04.TensorFormat',['original_completion_exists','original_completion_feasible','original_completion_optimum_bound','original_completion_exact_of_optimum_zero','exists_projected_completion','projected_completion_bound','rank_unfold_original','original_feasible_iff','error_lift_decomposition','completion_comparator_bound']),
 'svd_tie':('NLA.Proofs.TR04.SVD',['exists_tieStructure','card_tieSelection','TieStructure.first_error','TieStructure.frame_rank','TieStructure.equality_average_residual','TieStructure.full_equality_residual_zero','TieStructure.equality_exists_strict_residual','TieStructure.exists_frame','frame_projectMatrix']),
 'scalar_programs':('NLA.Proofs.TR04',['copyProgram_trace_cells','copyProgram_trace_cost','decodeNaturalProgram_trace_result','decodeNaturalProgram_trace_cost']),
 'radix_interface':('NLA.Proofs.TR04.TensorFormat',['original_decode_offset','original_offset_decode','original_offset_injective','original_inputMemory_tensor_cell','radix_validSVD_to_denseFirst','completion_step_radix']),
 'svd_memory':('NLA.Proofs.TR04',['matrixCell_entry','readMatrix_writeSVD_u','writeSVD_sigma_entry','readMatrix_writeSVD_v','writeSVD_outside'])}
def norm(p):return p if p.startswith('lean-statements/') else 'lean-statements/'+p
def fullrec(r):return dict(r,path=norm(r['path']))
blocks=[];union={}
for key,rel,digest in specs:
 p=REPO/'docs/lean/proofs/TR-04'/rel
 assert sha(p)==digest,(p,sha(p))
 d=json.loads(p.read_text());records=[fullrec(r) for r in d.get('project_closure',d.get('sources'))]
 for r in records:
  assert sha(REPO/r['path'])==r['sha256'],r['path']
  if r['path'] in union:assert union[r['path']]['sha256']==r['sha256']
  union[r['path']]=r
 owned=d.get('authored_sources')
 if owned is None:
  owned=[r for r in records if not r['prior_frozen']] if key=='svd_tie' else [r for r in records if Path(r['path']).stem in d['authored_modules']]
 owned=[fullrec(r) for r in owned]
 parsed=[v for r in records for v in declarations_of(r['path'].removeprefix('lean-statements/'),(REPO/r['path']).read_bytes())]
 ownednames={v['name'] for v in parsed if norm(v['source']) in {r['path'] for r in owned}}
 expected=d.get('authored_declarations')
 if expected is not None:assert ownednames==set(expected),(key,sorted(ownednames-set(expected)),sorted(set(expected)-ownednames))
 for r in d.get('unchanged_boundary_and_pins',d.get('reviewed_original_inputs',[])):
  assert sha(REPO/r['path'])==r['sha256'],('boundary',r)
 roots=d.get('targets',['NLA.Proofs.TR04.SVDFrameSpace'])
 prefix,names=endpoints[key]
 blocks.append({'key':key,'author_lock_path':str(p.relative_to(REPO)),'author_lock_sha256':digest,'author':d['author'],'records':records,'owned':owned,'declarations':parsed,'owned_declarations':sorted(ownednames),'roots':roots,'literal_endpoints':[prefix+'.'+n for n in names]})
 print(key,len(records),'sources',len(owned),'new',len(parsed),'named',len(ownednames),'owned')
config={'reviewer':'/root/recover_verification','self_authored_proof_sources':[], 'scope':'Five frozen TR04 support blocks only. Shared fresh closure build; separate literal consumers and approval scopes. No full Target, uniform program, global runtime, or Linux Comparator acceptance claim.','blocks':blocks,'union':list(union.values()),'inventory_helper_provenance':{'prior_path':str(old.relative_to(REPO)),'prior_sha256':sha(old),'change':'Only declaration matching accepts leading whitespace, capturing two indented theorem declarations; namespace tracking unchanged.','sha256':sha(BASE/'source_inventory.py')}}
(BASE/'source-lock.json').write_text(json.dumps(config,indent=2)+'\n')
print('UNION',len(union),'sources')
