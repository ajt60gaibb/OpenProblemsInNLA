from pathlib import Path
import os,subprocess,tempfile,json,hashlib,re,datetime
project=Path(__file__).resolve().parents[2];review=Path(__file__).resolve().parent
ie21=project.parents[1]/'IE-21/lean'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
receipt=json.loads((ie21/'reviews/complete-author-evidence/receipt.json').read_text())
assert receipt['all_selected_targets_compiled'] and receipt['project_sources_built']==31
for f,h in receipt['source_hashes'].items():assert sha(ie21/f)==h,f
boundary=['NLA/IE22/Definitions.lean','Challenge.lean','NUMERICAL_TARGETS.md','comparator.json']
initial={f:sha(project/f) for f in boundary}
names=json.loads((project/'comparator.json').read_text())['theorem_names']
assert names==['NLA.IE22.'+n for n in re.findall(r'^theorem (\w+)',(project/'Challenge.lean').read_text(),re.M)] and len(names)==20
build=Path(tempfile.mkdtemp(prefix='nla-ie22-root-statement-',dir='/private/tmp'));(build/'NLA').mkdir();(build/'NLA/IE21').symlink_to(Path(receipt['build_directory'])/'NLA/IE21',target_is_directory=True)
packages=Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
lean='/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean'
env=dict(os.environ);env['LEAN_PATH']=os.pathsep.join([str(build),str(project)]+[str(x/'.lake/build/lib/lean') for x in sorted(packages.iterdir()) if x.is_dir()])
commands=[]
with (review/'typecheck.log').open('w') as log:
 log.write('Independent IE22 statement typecheck only; no mathematical result proved. Root authored priorIE21 proofs, noIE22boundary.\n')
 log.write(subprocess.check_output([lean,'--version'],text=True))
 for f in ['NLA/IE22/Definitions.lean','Challenge.lean']:
  out=build/Path(f).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  cmd=[lean,'-o',str(out),f]
  res=subprocess.run(cmd,cwd=project,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  log.write('COMMAND '+json.dumps(cmd)+'\n'+res.stdout+'EXIT '+str(res.returncode)+'\n');log.flush()
  commands.append({'command':cmd,'exit_code':res.returncode,'output':res.stdout});print(f,res.returncode,flush=True)
  assert res.returncode==0
assert 'warning:' not in commands[0]['output']
assert commands[1]['output'].count('declaration uses `sorry`')==20
assert initial=={f:sha(project/f) for f in boundary}
canonical=project.parents[5]/'linear-systems-and-elimination/IE-22/README.md'
assert canonical.is_file(),canonical
statement=canonical.read_text().split('## Problem statement\n',1)[1].split('## Connection to numerical linear algebra',1)[0].strip()
assert statement in (project/'NUMERICAL_TARGETS.md').read_text()
r={'role':'Independent preproof boundary reviewer; root authored priorIE21 proofs but none of newIE22boundary','timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'boundary_sha256':initial,'project_sources_typechecked':2,'intentional_reference_placeholders':20,'proved_IE22_targets':0,'commands':commands,'build_directory':str(build),'reused_IE21_build':receipt['build_directory'],'unchanged_IE21_source_sha256':receipt['source_hashes'],'complete_original_problem_statement_verbatim':True,'log_sha256':sha(review/'typecheck.log'),'limits':['Local cached dependencies; not authenticated Linux execution','Reference placeholders establish no theorem','Portable IE22 dependency packaging remains required before full verification']}
(review/'typecheck-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print('PASS syntax/types and verbatim originaltarget; no proofclaim')
