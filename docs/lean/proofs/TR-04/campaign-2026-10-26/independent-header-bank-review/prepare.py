#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,sys
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5];PRIOR=BASE.parent/'independent-frame-gather-review'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
shutil.copyfile(PRIOR/'source_inventory.py',BASE/'source_inventory.py');sys.path.insert(0,str(BASE));from source_inventory import declarations_of
p=REPO/'docs/lean/proofs/TR-04/campaign-2026-10-26/header-bank-entries-author/source-lock.json';digest='3b854c113743515a63d01b1d83fc37a69b756d420c523a65e51d39c02bac4cb2';assert sha(p)==digest;d=json.loads(p.read_text());records=d['project_closure']
for r in records:assert sha(REPO/r['path'])==r['sha256']
owned=[r for r in records if Path(r['path']).stem in d['authored_modules']];decls=[v for r in records for v in declarations_of(r['path'].removeprefix('lean-statements/'),(REPO/r['path']).read_bytes())];ownednames=sorted(v['name'] for v in decls if 'lean-statements/'+v['source'] in {r['path'] for r in owned});assert set(ownednames)==set(d['authored_declarations'])
endpoints=['headerSingle_after_decode','headerSingle_return','RoutineEmbedding.headerSingle_run_at','headerRange_prefix_start','headerRange_prefix_product','headerRange_entry_eq','headerRange_return_product','headerRange_return','headerRange_time_le','RoutineEmbedding.headerRange_run_at']
block={'key':'header_bank_entries','author_lock_path':str(p.relative_to(REPO)),'author_lock_sha256':digest,'author':d['author'],'records':records,'owned':owned,'declarations':decls,'owned_declarations':ownednames,'roots':d['targets'],'literal_endpoints':['NLA.Proofs.TR04.'+n for n in endpoints]}
config={'reviewer':'/root/recover_verification','self_authored_proof_sources':[],'scope':'Two frozen single-header and suffix-product instruction-bank entry components. Fresh21-source closure; actual arbitrary caller traces, exact entry registers, suffix-only memory assumptions, decoded product and additive actual charges. No complete approximation program, full Target, total complexity, Linux or Comparator claim.','blocks':[block],'union':records,'inventory_helper_provenance':{'path':str((PRIOR/'source_inventory.py').relative_to(REPO)),'sha256':sha(PRIOR/'source_inventory.py'),'change':'Exact copy.'}}
(BASE/'source-lock.json').write_text(json.dumps(config,indent=2)+'\n');shutil.copyfile(PRIOR/'replay.py',BASE/'replay.py');print('SNAPSHOT',len(records),'sources',len(ownednames),'owned names',len(decls),'all explicit names')
