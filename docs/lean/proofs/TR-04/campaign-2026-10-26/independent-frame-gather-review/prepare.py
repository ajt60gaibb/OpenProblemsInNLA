#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,sys
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5];PRIOR=BASE.parent/'independent-original-machine-review'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
shutil.copyfile(PRIOR/'source_inventory.py',BASE/'source_inventory.py');sys.path.insert(0,str(BASE));from source_inventory import declarations_of
p=REPO/'docs/lean/proofs/TR-04/campaign-2026-10-23/frame-gather-author-2026-10-26/source-lock.json';digest='8b4dd02316aa540d892756b1d595d9984380411b3799fbad1ded621cf7619f11';assert sha(p)==digest;d=json.loads(p.read_text());records=[dict(r,path='lean-statements/'+r['path']) for r in d['sources']]
for r in records:assert sha(REPO/r['path'])==r['sha256']
owned=[r for r in records if r['path'].removeprefix('lean-statements/') in d['authored_sources']]
decls=[v for r in records for v in declarations_of(r['path'].removeprefix('lean-statements/'),(REPO/r['path']).read_bytes())];ownednames=sorted(v['name'] for v in decls if 'lean-statements/'+v['source'] in {r['path'] for r in owned})
endpoints=['FrameGatherParameters.Valid.width_le','FrameGatherParameters.column_lt','FrameGatherParameters.sourceAddress_flat','frameGatherProgram_initialize','frameGatherProgram_eleven_steps','frameGatherProgram_trace_result','RoutineEmbedding.frameGather_run_cells','RoutineEmbedding.frameGather_run_matrix','tieGatherParameters_valid','tieGatherParameters_width','frameGatherMatrix_tie','prefixGatherParameters_valid','frameGatherMatrix_prefix']
block={'key':'frame_gather','author_lock_path':str(p.relative_to(REPO)),'author_lock_sha256':digest,'author':'/root/recover_algebra','records':records,'owned':owned,'declarations':decls,'owned_declarations':ownednames,'roots':['NLA.Proofs.TR04.MachineFrameGatherSVD'],'literal_endpoints':['NLA.Proofs.TR04.'+n for n in endpoints]}
config={'reviewer':'/root/recover_verification','self_authored_proof_sources':[],'scope':'Six frozen FrameGather RAM component sources and their full47-source prerequisite closure. Actual every-legal-trace copy/cost/preservation and exact cyclic/prefix frame readback; no complete approximation algorithm, full Target, global complexity, Linux or Comparator acceptance claim.','blocks':[block],'union':records,'inventory_helper_provenance':{'path':str((PRIOR/'source_inventory.py').relative_to(REPO)),'sha256':sha(PRIOR/'source_inventory.py'),'change':'Exact copy.'}}
(BASE/'source-lock.json').write_text(json.dumps(config,indent=2)+'\n')
s=(PRIOR/'replay.py').read_text();needle="text+='end\\n'";assert s.count(needle)==1;s=s.replace(needle,"text+=(BASE/'integration-examples.lean.txt').read_text()+'\\n'\n text+='end\\n'");(BASE/'replay.py').write_text(s)
print('SNAPSHOT',len(records),'sources',len(owned),'new',len(ownednames),'owned names',len(decls),'explicit names')
