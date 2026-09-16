from pathlib import Path
import subprocess,json,hashlib,datetime
repo=Path('/private/tmp/nla-formalization-ie14-20260915'); p=repo/'linear-systems-and-elimination/IE-14/lean'
out=Path('/private/tmp/nla-campaign-existing-review/IE14-packaging')
base='8708d191824d66bf8dccbbad60231708b81e32fa';boundary='58b516b6dbb7fa4e885b679d261bf779c263aad4'
sha=lambda b:hashlib.sha256(b).hexdigest();git=lambda *a:subprocess.check_output(['git','-C',str(repo),*a])
initial='linear-systems-and-elimination/IE-14/lean/reviews/initial/'
changed=git('diff','--name-only',base).decode().splitlines();untracked=git('ls-files','--others','--exclude-standard').decode().splitlines()
assert changed==[initial+'SHA256SUMS'],changed
assert untracked==[initial+'README.md'],untracked
old=git('show',base+':'+initial+'SHA256SUMS'); earlier=git('show',boundary+':'+initial+'SHA256SUMS');now=(p/'reviews/initial/SHA256SUMS').read_bytes()
assert old==earlier
assert now==old.replace(b'  NUMERICAL_TARGETS.md\n',b'  ../../NUMERICAL_TARGETS.md\n',1)
checks=[]; logs=[]
for manifest in sorted(p.rglob('SHA256SUMS')):
 if '.lake' in manifest.parts: continue
 entries=[]
 for row in manifest.read_text().splitlines():
  if not row.strip():continue
  h,rel=row.split('  ',1); f=(manifest.parent/rel).resolve(); assert f.is_relative_to(p.resolve()),f
  assert f.is_file(),f
  assert sha(f.read_bytes())==h,(f,h)
  tracked=git('ls-files','--error-unmatch',str(f.relative_to(repo))).decode().strip(); assert tracked
  assert sha(git('show',base+':'+str(f.relative_to(repo))))==h,(f,'base content changed')
  entries.append({'written_path':rel,'normalized_project_path':str(f.relative_to(p)),'sha256':h,'tracked_at_base':True})
 check=subprocess.run(['shasum','-a','256','-c','SHA256SUMS'],cwd=manifest.parent,text=True,capture_output=True)
 assert check.returncode==0,(manifest,check.stdout,check.stderr)
 logs.append(str(manifest.relative_to(p))+'\n'+check.stdout+check.stderr)
 checks.append({'manifest':str(manifest.relative_to(p)),'sha256':sha(manifest.read_bytes()),'entries':entries})
assert sum(len(c['entries']) for c in checks)==99
inputs={}
for name,rev in [('final-source-inputs.json','c04371f6005220866f4f069809002d319554e039'),('statement-freeze.json',boundary)]:
 d=json.loads((p/'reviews'/name).read_text())['input_sha256']; inputs[name]=d
 for rel,h in d.items():
  f=p/rel; assert sha(f.read_bytes())==h
  assert sha(git('show',rev+':'+str(f.relative_to(repo))))==h
reports={}
for rel in ['reviews/final-source-referee-1.md','reviews/final-source-referee-2.md','reviews/statement-referee-1.md','reviews/statement-referee-2.md']:
 f=p/rel;assert f.read_bytes()==git('show',base+':'+str(f.relative_to(repo)));reports[rel]=sha(f.read_bytes())
readme=p/'reviews/initial/README.md'
assert subprocess.run(['git','-C',str(repo),'check-ignore',str(readme.relative_to(repo))],capture_output=True).returncode==1
result={'verdict':'PASS packaging only; no proof or operational reapproval','reviewer':'OpenAI Codex AI agent /root/existing_verification_audit, independent referee 2','reviewed_base_commit':base,'historical_boundary':boundary,'changes_before_review_artifacts':{'tracked_modified':changed,'untracked_new':untracked},'old_manifest_sha256':sha(old),'new_manifest_sha256':sha(now),'new_readme_sha256':sha(readme.read_bytes()),'exact_change':'Only first manifest pathname NUMERICAL_TARGETS.md becomes ../../NUMERICAL_TARGETS.md; all seven digest strings unchanged; provenance README added.','manifests':checks,'archive_payload_references':99,'all_payloads_current_and_base_git_match':True,'frozen_input_checks':inputs,'earlier_reports_unchanged':reports,'no_linux_or_comparator_claim':True,'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(out/'audit.json').write_text(json.dumps(result,indent=2)+'\n');(out/'checksum-checks.log').write_text('\n'.join(logs))
print('PASS',len(checks),'manifests,99 payload references,23 candidate/10 frozen inputs unchanged; exact 2-file packaging change')
