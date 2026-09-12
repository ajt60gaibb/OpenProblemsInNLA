from pathlib import Path
import hashlib,json,subprocess,zipfile,datetime
root=Path('/tmp/nla-lean-mi29-worktree');project=root/'matrix-inequalities-and-norms/MI-29/lean';e=project/'verification/publication-2026-09-12/referee-2';r=project/'verification/linux-2026-09-12';sha='c0c5eced77d2528f37d931200248fc54a190813e'
h=lambda b:hashlib.sha256(b).hexdigest()
protected=['NLA/MI29/Definitions.lean','Challenge.lean','NUMERICAL_TARGETS.md','NLA/MI29/Proof.lean','Solution.lean','comparator.json','lakefile.toml','lake-manifest.json','lean-toolchain']
checks={}
for f in protected:
 original=subprocess.check_output(['git','show',sha+':'+str((project/f).relative_to(root))],cwd=root)
 current=(project/f).read_bytes();assert original==current,f;checks[f]=h(current)
canonical=root/'matrix-inequalities-and-norms/MI-29/README.md';tail=canonical.read_bytes().split(b'## Problem statement',1)[1]
old=subprocess.check_output(['git','show',sha+':'+str(canonical.relative_to(root))],cwd=root)
assert old.split(b'## Problem statement',1)[1]==tail
remote=(e/'current-main-README.md').read_bytes();assert remote.split(b'## Problem statement',1)[1]==tail
registry=root/'problem_ids.json';assert registry.read_bytes()==subprocess.check_output(['git','show',sha+':problem_ids.json'],cwd=root)
assert registry.read_bytes()==(e/'current-main/problem_ids.json').read_bytes()
manifest=json.loads((r/'EVIDENCE-MANIFEST.json').read_text());assert all(h((r/f).read_bytes())==v for f,v in manifest['files'].items())
artifacts=json.loads((r/'artifact-metadata.json').read_text())['artifacts'];archives=[]
for a in artifacts:
 zpath=r/(a['name']+'.zip');assert 'sha256:'+h(zpath.read_bytes())==a['digest']
 count=0
 with zipfile.ZipFile(zpath) as z:
  assert z.testzip() is None
  for f in z.infolist():
   if f.is_dir():continue
   assert not Path(f.filename).is_absolute() and '..' not in Path(f.filename).parts
   assert z.read(f)==(r/'artifacts'/a['name']/f.filename).read_bytes();count+=1
 archives.append({'name':a['name'],'sha256':h(zpath.read_bytes()),'all_extracted_bytes_match':True,'files':count})
receipt=json.loads((r/'artifacts/lean-MI-29/verify-20260912T165105Z-4005/result.json').read_text())
tracked=subprocess.check_output(['git','ls-tree','-rz','--name-only',sha,'--',str(project.relative_to(root))],cwd=root).decode().split('\0')
tracked={str(Path(f).relative_to(project.relative_to(root))) for f in tracked if f}
assert tracked==set(receipt['input_sha256'])
for f,v in receipt['input_sha256'].items():
 b=subprocess.check_output(['git','show',sha+':'+str((project/f).relative_to(root))],cwd=root);assert h(b)==v,f
config=json.loads((project/'comparator.json').read_text());assert receipt['config']==config
log=(r/'artifacts/lean-MI-29/verify-20260912T165105Z-4005/comparator.log').read_text();assert 'Lean default kernel accepts the solution' in log and 'Your solution is okay!' in log and 'EXIT_STATUS=0' in log
assert all(x in log for x in config['theorem_names'])
assert len([l for l in log.splitlines() if 'depends on axioms:' in l])==15
assert all(l.endswith('[propext, Classical.choice, Quot.sound]') for l in log.splitlines() if 'depends on axioms:' in l)
jobs=json.loads((r/'jobs.json').read_text())['jobs'];assert len(jobs)==3 and all(j['conclusion']=='success' for j in jobs)
assert all(s['conclusion']=='success' for j in jobs for s in j['steps'])
render=json.loads((project/'verification/publication-2026-09-12/rendered-files.json').read_text())
for fname,key in [('problem.pdf','pdf_sha256'),('problem.tex','tex_sha256'),('README.md','canonical_sha256')]:assert h((project.parent/fname).read_bytes())==render[key],fname
images={str(f):h(f.read_bytes()) for f in sorted(Path('/tmp/nla-lean-formalization/pdf-mi29').glob('page-*.png'))};assert len(images)==3
result={'reviewed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verified_proof_commit':sha,'protected_nine_files_unchanged':checks,'canonical_target_and_following_bytes_sha256':h(tail),'identical_to_verified_commit_and_current_main':True,'registry_unchanged':True,'linux_manifest_files':len(manifest['files']),'all_linux_manifest_hashes_match':True,'archives':archives,'exact_receipt_input_set_and_git_blob_hashes_match':len(tracked),'five_export_config_matches_receipt':True,'real_comparator_success_and_default_kernel_replay_observed':True,'fifteen_standard_three_axiom_reports':True,'all_three_jobs_and_all_steps_succeeded':True,'current_pdf_and_tex_match_final_renderer_hashes':render,'visually_inspected_three_images':images}
(e/'independent-checks.json').write_text(json.dumps(result,indent=2)+'\n')
(e/'check.py').write_text(Path(__file__).read_text())
print(json.dumps({k:v for k,v in result.items() if k not in ['current_pdf_and_tex_match_final_renderer_hashes','visually_inspected_three_images','protected_nine_files_unchanged']},indent=2))
