from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,tempfile
root=Path(__file__).resolve().parents[2]
evidence=Path(__file__).resolve().parent
ie21=root.parents[1]/'IE-21/lean'
linux=Path('/private/tmp/nla-ie21-publication-20260922/linear-systems-and-elimination/IE-21/lean/verification/linux')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipt=json.loads((linux/'input-receipt.json').read_text())
result=json.loads((linux/'successful-verification/result.json').read_text())
assert result['result']=='comparator-accepted'
assert receipt['publication_commit']=='1eb284b84ecc0d3c958d022b3e020be7fa111391'
assert result['input_sha256']==receipt['input_sha256']
previous=json.loads((ie21/'reviews/ie21-final-fidelity-evidence/build-receipt.json').read_text())
dependency_build=Path(previous['build_directory'])
dependency_hashes=previous['source_hashes']
assert len(dependency_hashes)==31
olean_hashes={}
for f,digest in dependency_hashes.items():
 assert sha(ie21/f)==receipt['input_sha256'][f]==digest,f
 assert sha(linux/'source'/f)==digest,f
 olean=dependency_build/Path(f).with_suffix('.olean')
 assert olean.is_file(),olean
 olean_hashes[str(olean)]=sha(olean)
build=Path(tempfile.mkdtemp(prefix='nla-ie22-statements-infrastructure-review-',dir='/private/tmp'))
(build/'NLA').mkdir()
(build/'NLA/IE21').symlink_to(dependency_build/'NLA/IE21',target_is_directory=True)
packages=Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
lean=Path('/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean')
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(build),str(dependency_build),str(root)]+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()])
files=['NLA/IE22/Definitions.lean','Challenge.lean']
initial={f:sha(root/f) for f in files}
config=json.loads((root/'comparator.json').read_text())
names=['NLA.IE22.'+n for n in re.findall(r'^theorem (\w+)',(root/'Challenge.lean').read_text(),re.M)]
assert names==config['theorem_names'] and len(names)==len(set(names))==20
assert config['definition_names']==[]
assert set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
commands=[]
with (evidence/'typecheck.log').open('w') as log:
 log.write('Independent preproof IE-22 statement-only typecheck by Codex AI /root/infrastructure_audit. No IE-22 proof is implemented or certified. Twenty deliberate reference placeholders. Reused IE-21 dependency cache has separately authenticated source hashes; this is not fresh dependency compilation.\n')
 log.write(subprocess.check_output([str(lean),'--version'],text=True))
 for f in files:
  out=build/Path(f).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  cmd=[str(lean),'-o',str(out),f]
  log.write('COMMAND '+json.dumps(cmd)+'\n');log.flush()
  p=subprocess.run(cmd,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  log.write(p.stdout+'EXIT '+str(p.returncode)+'\n');log.flush()
  commands.append({'argv':cmd,'exit_code':p.returncode,'output':p.stdout})
  print(f,p.returncode,flush=True)
  if p.returncode:raise SystemExit(p.returncode)
assert 'warning:' not in commands[0]['output']
assert len(re.findall(r'warning: declaration uses `sorry`',commands[1]['output']))==20
assert all('warning: declaration uses `sorry`' in line for line in commands[1]['output'].splitlines())
assert all(sha(root/f)==digest for f,digest in initial.items())
record={'reviewer':'Codex AI /root/infrastructure_audit','completed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'Statement-only independent typecheck PASS; no IE-22 proof claim','reviewer_authorship':'No IE-22 boundary authorship. Reviewer authored six reused IE-21 Gaussian/spherical modules; not an independent final reviewer of the combined future package.','build_directory':str(build),'typechecked_source_sha256':initial,'selected_declarations':names,'selected_declaration_count':len(names),'intentional_placeholder_warnings':20,'commands':commands,'reused_IE21_source_sha256':dependency_hashes,'reused_IE21_olean_sha256':olean_hashes,'IE21_publication_commit':receipt['publication_commit'],'IE21_distinct_Linux_guest_commit':result['repository_commit'],'IE21_Linux_receipts_sha256':{str(p.relative_to(linux)):sha(p) for p in [linux/'input-receipt.json',linux/'successful-verification/result.json',linux/'OPERATIONAL-REVIEW.md']},'limitations':'Fresh reviewer output for the two new statement files, reused final-fidelity IE21 oleans and pinned Mathlib caches; no recompilation/authentication of all cached binaries in this check. IE22 is unproved and no Comparator/LeanCert run is claimed.','evidence_sha256':{f:sha(evidence/f) for f in ['typecheck.py','typecheck.log']}}
(evidence/'typecheck-receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS: two new statement files, exactly20 deliberate placeholders, all20 comparator targets, all31 IE21 source hashes tied to successful Linux input',flush=True)
