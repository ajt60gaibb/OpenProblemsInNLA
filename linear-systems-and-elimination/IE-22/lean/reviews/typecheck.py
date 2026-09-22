from pathlib import Path
import hashlib,json,os,re,subprocess,tempfile,datetime
root=Path(__file__).resolve().parents[1];review=Path(__file__).resolve().parent
ie21=root.parents[1]/'IE-21/lean';ib=json.loads((ie21/'reviews/ie21-final-fidelity-evidence/build-receipt.json').read_text())
for f,h in ib['source_hashes'].items():assert hashlib.sha256((ie21/f).read_bytes()).hexdigest()==h,f
build=Path(tempfile.mkdtemp(prefix='nla-ie22-statement-draft-',dir='/private/tmp'));(build/'NLA').mkdir();(build/'NLA/IE21').symlink_to(Path(ib['build_directory'])/'NLA/IE21',target_is_directory=True)
packages=Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages');lean='/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean'
env=dict(os.environ);env['LEAN_PATH']=os.pathsep.join([str(build),str(root)]+[str(x/'.lake/build/lib/lean') for x in sorted(packages.iterdir()) if x.is_dir()])
records=[]
with (review/'statement-typecheck.log').open('w') as log:
 log.write('IE-22 UNREVIEWED statement-only draft: no IE-22 theorem is proved. References use intentional sorry placeholders. Local cached dependency typecheck only.\n')
 log.write(subprocess.check_output([lean,'--version'],text=True))
 for f in ['NLA/IE22/Definitions.lean','Challenge.lean']:
  out=build/Path(f).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  cmd=[lean,'-o',str(out),f];log.write('COMMAND '+json.dumps(cmd)+'\n');log.flush()
  res=subprocess.run(cmd,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  log.write(res.stdout+'EXIT '+str(res.returncode)+'\n');log.flush();print(f,res.returncode,flush=True)
  records.append({'file':f,'exit_code':res.returncode,'output':res.stdout})
  if res.returncode:raise SystemExit(res.returncode)
assert 'warning:' not in records[0]['output']
assert records[1]['output'].count("declaration uses `sorry`")==20
review.joinpath('statement-typecheck-receipt.json').write_text(json.dumps({'completed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'unreviewed statement syntax/types only; zero IE-22 results proved','typechecked_target_count':20,'intentional_Challenge_placeholder_count':20,'local_dependency_build':ib['build_directory'],'dependency_source_sha256':ib['source_hashes'],'build_directory':str(build),'results':records,'source_sha256':{f:hashlib.sha256((root/f).read_bytes()).hexdigest() for f in ['NLA/IE22/Definitions.lean','Challenge.lean']},'log_sha256':hashlib.sha256((review/'statement-typecheck.log').read_bytes()).hexdigest()},indent=2)+'\n')
print('PASS draft Definitions and 20 intentional reference statements; no proof claim',flush=True)
