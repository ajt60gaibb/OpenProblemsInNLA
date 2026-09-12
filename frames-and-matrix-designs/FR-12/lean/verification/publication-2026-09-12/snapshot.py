from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,subprocess
repo=Path('/tmp/nla-lean-fr12-worktree'); project=repo/'frames-and-matrix-designs/FR-12/lean'; work=Path('/tmp/nla-lean-formalization/fr12-publication')
git=lambda *a:subprocess.check_output(['git',*a],cwd=repo)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
revision='3e20bae9a07b1a33db8fdfb18bdebb9e590071a9'
assert git('rev-parse','HEAD').decode().strip()==revision
base=git('rev-parse','nla-upstream/main').decode().strip()
receipt=json.loads((project/'verification/linux-2026-09-12/artifacts/lean-FR-12/verify-20260912T205219Z-4137/result.json').read_text())
assert receipt['repository_commit']==revision and receipt['result']=='comparator-accepted'
inputs=receipt['input_sha256']; assert len(inputs)==137
assert set(inputs)==set(git('ls-tree','-r','--name-only',revision,'--','frames-and-matrix-designs/FR-12/lean').decode().replace('frames-and-matrix-designs/FR-12/lean/','').splitlines())
for name,h in inputs.items():assert sha(project/name)==h,name
linux=project/'verification/linux-2026-09-12';out=linux/'EVIDENCE-MANIFEST.json';ev=json.loads(out.read_text())
actual={str(p.relative_to(linux)) for p in linux.rglob('*') if p.is_file() and p!=out}
assert actual==set(ev['files']) and len(actual)==255
for name,r in ev['files'].items():assert sha(linux/name)==r['sha256'] and (linux/name).stat().st_size==r['bytes'],name
ops={str(p.relative_to(project)):sha(p) for p in linux.rglob('*') if p.is_file()};assert len(ops)==256
for p in ['frames-and-matrix-designs/FR-12/README.md','frames-and-matrix-designs/FR-12/solution.md','frames-and-matrix-designs/FR-12/solution.tex','frames-and-matrix-designs/FR-12/solution.pdf','problem_ids.json']:
 assert git('show',revision+':'+p)==git('show',base+':'+p),p
record={'created_utc':datetime.now(timezone.utc).isoformat(),'verified_revision':revision,'upstream_base':base,'verified_run':34718277411,'verified_inputs':inputs,'operational_files':ops,'canonical_and_original_sources_unchanged_between_candidate_and_upstream':True,'shared_harness_diff':git('diff',revision,base,'--','tools/lean/harness.py','tools/lean/source-lock.json').decode(),'preintegration_status':git('status','--short').decode(),'cache_cleanup':'Removed only generated FR-12 Mathlib .lake/build/ir intermediates to relieve disk exhaustion; proof sources/Git/evidence and .olean files untouched.'}
assert not record['shared_harness_diff']
(work/'before-integration.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'result':'PASS','base':base,'verified_inputs':len(inputs),'operational_files':len(ops)}))
