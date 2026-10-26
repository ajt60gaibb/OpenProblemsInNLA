#!/usr/bin/env python3
"""Verify/stage exact accepted TR04 evidence before descriptive promotion."""
import hashlib,json,pathlib,subprocess,datetime
R=pathlib.Path(__file__).resolve().parents[5];B=pathlib.Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
side=B/'independent-evidence-index/full-target-index-portability-review.json'
assert sha(side)=='9f51542498734f4490ef1f860ab7ad7c18bd2a4126906119ffbc97e4cb423dca'
s=json.loads(side.read_text());assert s['passed'];paths=set()
def add(p,h=None):
 p=R/p if isinstance(p,str) else p
 assert p.is_file() and not p.is_symlink(),p
 assert not any(x in p.relative_to(R).parts for x in ['.lake','__pycache__']),p
 assert p.suffix not in ['.olean','.ilean','.o','.pyc','.so','.a'],p
 if 'objects' in p.parts:
  assert p.name.endswith('.source-sha256.json') and p.stat().st_size<8192,p
  assert p.relative_to(R).as_posix() in s['artifact_hashes'],p
  assert len(json.loads(p.read_text())['sha256'])==64,p
 if h:assert sha(p)==h,(p,'hash mismatch')
 paths.add(p)
for p,h in s['artifact_hashes'].items():add(p,h)
add(side)
for name in ['independent-linux-candidate-algebra','linux-pr370-candidate','independent-promotion-review','independent-promotion-source-algebra','promotion-draft','remaining-solved-inventory-geometry']:
 for p in sorted((B/name).rglob('*')):
  if p.is_file() and not any(x in p.parts for x in ['.lake','__pycache__']):add(p)
for p in ['docs/lean/proofs/TR-04/README.md','docs/lean/proofs/TR-04/LINUX_CI_RECEIPT.md']:add(p)
add(pathlib.Path(__file__).resolve())
receipts={'full_source_acceptance':B/'independent-full-target-review/ACCEPTANCE.json','terminal_validation':B/'independent-full-target-review/TERMINAL_VALIDATION.json','actual_Linux':B/'independent-linux-candidate-algebra/APPROVAL.json','promotion_review_non_author':B/'independent-promotion-review/APPROVAL.json','promotion_review_algebra':B/'independent-promotion-source-algebra/APPROVAL.json'}
record={'recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Complete original TR04 Target accepted; before exact independently reviewed descriptive promotion','canonical_status_at_checkpoint':'Solved; promotion not applied','proof_candidate_commit':'027aaefbadf602ac460d0cf4cae7beed3181d712','canonical_inputs':205,'canonical_Lean':190,'exact_shared_copies':184,'proof_modules':179,'approved_scopes':42,'actual_Linux_run':40405628070,'actual_Linux_job':121862750146,'actual_executed_merge':'d9d0a8f163c2c0309e349cfbe839d53bece11643','actual_Linux_artifact':12691512992,'actual_artifact_audit_checks':795,'receipts':{k:{'path':str(p.relative_to(R)),'sha256':sha(p)} for k,p in receipts.items()},'input_artifacts':{str(p.relative_to(R)):sha(p) for p in sorted(paths)},'historical_false_parser_aggregate_preserved':True,'final_promotion_source_bound_Linux':'pending','reproduction_note':'This checkpoint retains the exact25 live original inputs. Replay historical checks in a checkout of this checkpoint; later descriptive promotion changes the problem README and package metadata, with original bytes archived.'}
out=B/'FULL_TARGET_ACCEPTANCE_CHECKPOINT_2026-10-26.json';out.write_text(json.dumps(record,indent=2)+'\n');add(out)
w=R/'docs/lean/proofs/TR-04/campaign-2026-10-25/whitespace-preservation.json';d=json.loads(w.read_text());entries={x['path']:x for x in d['files']};count=0
for p in sorted(paths):
 try:txt=p.read_text()
 except UnicodeDecodeError:continue
 lines=[i for i,line in enumerate(txt.splitlines(),1) if line and line[-1] in ' \t'];raw=txt.splitlines()
 for i in range(len(raw),0,-1):
  if raw[i-1]!='':break
  lines.append(i)
 lines=sorted(set(lines))
 if not lines:continue
 rp=str(p.relative_to(R));h=sha(p)
 if rp in entries:
  assert entries[rp]['sha256']==h,(rp,'changed frozen whitespace bytes')
  entries[rp]['lines']=sorted(set(lines)|set(entries[rp].get('lines',[entries[rp]['line']])))
 else:
  e={'path':rp,'sha256':h,'line':lines[0],'lines':lines,'reason':'Exact independently accepted full-target evidence, source snapshot, raw diagnostic or actual Linux log retained under frozen SHA; no proof/model/trust/ID exception.'};d['files'].append(e);entries[rp]=e;count+=1
w.write_text(json.dumps(d,indent=2)+'\n');add(w)
ordered=sorted(paths)
for n in range(0,len(ordered),150):subprocess.run(['git','add','-f','--',*[str(p.relative_to(R)) for p in ordered[n:n+150]]],cwd=R,check=True)
r=subprocess.run(['git','diff','--cached','--check'],cwd=R,text=True,capture_output=True);errors=[]
for line in r.stdout.splitlines():
 if ': trailing whitespace.' in line or ': new blank line at EOF.' in line:
  rp,num,_=line.split(':',2);e=entries.get(rp)
  if not e or sha(R/rp)!=e['sha256'] or int(num) not in e.get('lines',[e['line']]):errors.append(line)
 elif line and not line.startswith('+'):errors.append(line)
assert not errors,errors
print(json.dumps({'accepted_artifact_hashes_verified':len(s['artifact_hashes']),'total_whitelisted_paths':len(paths),'new_exact_whitespace_records':count,'compiled_objects_or_symlinks':False,'checkpoint_sha256':sha(out)},indent=2))
