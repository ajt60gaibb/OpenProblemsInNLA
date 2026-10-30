#!/usr/bin/env python3
"""Verify exact aggregate import wiring against ten sealed scoped acceptances, without Lean execution."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,subprocess
B=Path(__file__).resolve().parent;C=B.parent;REPO=C.parents[4]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();hb=lambda b:hashlib.sha256(b).hexdigest()
assert sha(B/'SOURCE_FREEZE.json')=='546c106ec03ac4e57881f44f906bd8fa675a7560522c2ac73d23b1a0718ef149'
f=json.loads((B/'SOURCE_FREEZE.json').read_text());assert f['git_ref_before']=='6525877378e43325134d35c9fdc2f621d7723757'
old=subprocess.check_output(['git','show',f['git_ref_before']+':'+f['file']],cwd=REPO);new=(REPO/f['file']).read_bytes();add=f['exact_added_utf8'].encode()
assert hb(old)==f['before_sha256']=='e6692925b7db03d7ef80d9f97c2ea48ef59ba12d1e43f696813426d2de240ca4'
assert hb(new)==f['after_sha256']=='728bdfee63cb2db719d475f57d910bdc3ad330afc179aad85f7c057ed3a15174'
assert new.count(add)==1 and new.replace(add,b'',1)==old
assert add==b'import NLA.Proofs.RE05.OneCopyError\nimport NLA.Proofs.RE05.OffsetContraction\nimport NLA.Proofs.RE05.GaussianQuadraticCovariance\n'
scopes=[('independent-deterministic-review','df155bba3d69cbc5aaa8dc5da108ddd7571ffd4664bd167aba92880bfe06026b'),('independent-query-bound-review','50d7c7efa1ab35a1c05caceb235b7b6f2c7fe3480a9d0b739e3e0824b8f8b25e'),('independent-median-review','3b4f801188b0b9e7b978dede02531a16bcd860e2cd609f1f244b0cb1e508b5a0'),('independent-spectral-split-review','a956f80cc6555c68bdf04d799efda88a93c7b580ecdf38a4dbc63b9f2ba55d75'),('independent-gaussian-moments-review','33454968fdffe4f45234641a3c1d19e6b58998c152744c1ed137f96db9cdb05e'),('independent-gaussian-wick-review','ce2a4bc2fcbbca28cefc44adc7c4078a7839347d11aa0f8e48c65891097ae55c'),('independent-regression-review','98c3300cfcd7300b6e7c2b084716ac7accce261a6f7e58ceb53469739073edd2'),('independent-one-copy-review','bac72855f4b4152519d4db55a7693faa9fd0544f38382e4b138d53b7456dfd11'),('independent-centered-offset-review','5f826cecaa333eaf285c016bbadf19d8ddcecf0465331b7c87b2bf242064e3cd'),('independent-gaussian-quadratic-geometry','7a5a7af21b1461ec34c9da46703ba9319dd5e3972866d9505937b767ea412a19')]
accepted={};receipts=[]
for dirname,h in scopes:
 p=C/dirname/'ACCEPTANCE.json';assert sha(p)==h;receipt=json.loads(p.read_text());assert receipt['passed']
 lock=json.loads((p.parent/'source-lock.json').read_text());owned={d['source'] for d in lock['owned_declarations']}
 for x in lock['union']:
  path=Path(x['path']);rel=str(path.relative_to('lean-statements'))
  if rel in owned:
   module=rel.removesuffix('.lean').replace('/','.');assert module not in accepted;accepted[module]={'path':str(path),'sha256':x['sha256']}
 receipts.append({'path':str(p.relative_to(REPO)),'sha256':h,'owned_source_count':len(owned)})
assert len(accepted)==36 and all(n.startswith('NLA.Proofs.RE05.') for n in accepted)
seen={}
def visit(m):
 p=REPO/'lean-statements'/(m.replace('.','/')+'.lean')
 if m in seen:return
 data=p.read_bytes();seen[m]={'path':str(p.relative_to(REPO)),'sha256':hb(data)}
 for ds in re.findall(r'^import\s+(.+)$',data.decode(),re.M):
  for dep in ds.split():
   if (REPO/'lean-statements'/(dep.replace('.','/')+'.lean')).is_file():visit(dep)
roots=[m for m in re.findall(r'^import\s+(NLA\.Proofs\.RE05\.\S+)$',new.decode(),re.M)]
assert len(roots)==8
for m in roots:visit(m)
actual={k:v for k,v in seen.items() if k.startswith('NLA.Proofs.RE05.')}
assert actual==accepted==f['resolved_RE05_modules'] and seen==f['resolved_project_sources'] and len(seen)==43
assert all(not any(tag in p for tag in ['RE05Tail','HighDimProb','WidthProbability','OneColumn','GramMoments']) for p in seen)
for rec in seen.values():assert hb(subprocess.check_output(['git','show',f['git_ref_before']+':'+rec['path']],cwd=REPO))==rec['sha256']
assert len(json.loads((REPO/'problem_ids.json').read_text()))==217
out={'passed':True,'recorded_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/recover_verification','scope':'Exact three-import aggregate wiring/accepted-set/Git-source binding only; zero new Lean commands and no combined proof/CI result.',
 'proposal_sha256':sha(B/'SOURCE_FREEZE.json'),'git_ref_before':f['git_ref_before'],'aggregate_before_sha256':hb(old),'aggregate_after_sha256':hb(new),'exact_added_utf8':f['exact_added_utf8'],'stripping_only_the_three_imports_recovers_exact_base_blob':True,
 'scoped_acceptances':receipts,'accepted_RE05_modules':36,'resolved_project_sources':43,'all43_source_blobs_identical_to_before_Git_ref':True,'accepted_set_equals_entire_RE05_import_closure':True,'mutable_and_isolated_sources_excluded':True,
 'new_Lean_commands':0,'new_CI_or_Comparator_acceptance':False,'full_RE05_Target_proved':False,'probability_success_proved':False,'ID_or_original_target_changes':False,'review_script_sha256':sha(Path(__file__))}
p=B/'INDEPENDENT_REVIEW.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'passed':True,'review_sha256':sha(p),'accepted_modules':36,'project_sources':43,'Lean_commands':0},indent=2))
