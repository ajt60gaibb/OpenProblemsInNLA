#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,shutil,sys
BASE=Path(__file__).resolve().parent;REPO=BASE.parents[5];PRIOR=REPO/'docs/lean/proofs/TR-04/campaign-2026-10-25/independent-strict-math-review'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
shutil.copyfile(PRIOR/'source_inventory.py',BASE/'source_inventory.py');sys.path.insert(0,str(BASE));from source_inventory import declarations_of
specs=[('explicit_frames','explicit-frame-author-2026-10-26/source-lock.json','42db870b8fe6604b459b792475f956a1ab49cd9728054f67adcf4374c7f247a4','NLA.Proofs.TR04.TTStrictExplicitFamily'),('explicit_original','explicit-original-author-2026-10-26/source-lock.json','0dfc8277853ff5887255c28cca221cad0a9bd8b8501cc7cadbdefc1704080615','NLA.Proofs.TR04.TTStrictExplicitOriginal')]
svd='NLA.Proofs.TR04.SVD.';tt='NLA.Proofs.TR04.TensorFormat.TTStrict.'
endpoints={'explicit_frames':[svd+n for n in ['cyclicColumnIndex_val','cyclicColumnIndex_injective','cyclicColumnIndex_surjective','cyclicFrame_rank','cyclicFrame_projection','countedTieStructure_above','countedTieStructure_tied','countedTieStructure_take','TieStructure.explicitIndex_val','TieStructure.explicitFrame_projection']]+[tt+n for n in ['positiveFrames_column','positiveFrames_count','explicitFirstFrames_spec','explicit_strict_family']],'explicit_original':[tt+'Original.output_minimum_iff',tt+'Original.first_svd_explicit_strict_family']}
blocks=[];union={}
for key,rel,digest,root in specs:
 p=REPO/'docs/lean/proofs/TR-04/campaign-2026-10-23'/rel;assert sha(p)==digest;d=json.loads(p.read_text());records=[dict(r,path='lean-statements/'+r['path']) for r in d['sources']]
 for r in records:
  assert sha(REPO/r['path'])==r['sha256']
  if r['path'] in union:assert union[r['path']]['sha256']==r['sha256']
  union[r['path']]=r
 owned=[r for r in records if r['path'].removeprefix('lean-statements/') in d['authored_sources']];decls=[v for r in records for v in declarations_of(r['path'].removeprefix('lean-statements/'),(REPO/r['path']).read_bytes())];ownednames=sorted(v['name'] for v in decls if 'lean-statements/'+v['source'] in {r['path'] for r in owned})
 blocks.append({'key':key,'author_lock_path':str(p.relative_to(REPO)),'author_lock_sha256':digest,'author':'/root/recover_algebra','records':records,'owned':owned,'declarations':decls,'owned_declarations':ownednames,'roots':[root],'literal_endpoints':endpoints[key]})
 print(key,len(records),'sources',len(owned),'owned',len(ownednames),'authored names')
config={'reviewer':'/root/recover_verification','self_authored_proof_sources':[],'scope':'Five frozen explicit frame/family mathematical sources, including exact original-boundary corollary. Shared fresh51-source producer snapshot and two literal consumers. No complete finite RAM implementation, full Target, global polynomial complexity, Linux or Comparator acceptance claim.','blocks':blocks,'union':list(union.values()),'inventory_helper_provenance':{'prior_path':str((PRIOR/'source_inventory.py').relative_to(REPO)),'sha256':sha(PRIOR/'source_inventory.py'),'change':'Exact copy, including leading indentation support.'}}
(BASE/'source-lock.json').write_text(json.dumps(config,indent=2)+'\n')
s=(PRIOR/'replay.py').read_text().replace('len(frozen)==47','len(frozen)==51').replace('==48','==53').replace('/48 ','/53 ')
needle='body=tail[match.end():];stack=[];header=None'
assert needle in s;s=s.replace(needle,'body=tail[match.end():];stack=[];header=None;pending_top_level_lets=0')
needle="elif body[i:i+2]==':=' and not stack:header=body[:i].rstrip();break"
replacement="""elif not stack and re.match(r'let\\b',body[i:]) and (i==0 or not re.match(r\"[\\w']\",body[i-1])):
   pending_top_level_lets+=1
  elif body[i:i+2]==':=' and not stack:
   if pending_top_level_lets:
    pending_top_level_lets-=1
   else:
    header=body[:i].rstrip();break"""
assert needle in s;s=s.replace(needle,replacement);(BASE/'replay.py').write_text(s)
(BASE/'consumer-parser-provenance.json').write_text(json.dumps({'prior_driver':str((PRIOR/'replay.py').relative_to(REPO)),'prior_driver_sha256':sha(PRIOR/'replay.py'),'change':'Header delimiter recognizes reviewed top-level let assignments in proposition types and retains them verbatim before the theorem proof assignment. Binder application parser unchanged. All16 selected full headers are checked in final Lean consumers.','proof_inputs_changed':False},indent=2)+'\n')
print('UNION',len(union),'sources')
