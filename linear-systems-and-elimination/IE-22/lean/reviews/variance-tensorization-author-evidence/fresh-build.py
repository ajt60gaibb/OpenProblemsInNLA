from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,tempfile
root=Path(__file__).resolve().parents[2];evidence=Path(__file__).resolve().parent
build=Path(tempfile.mkdtemp(prefix='nla-ie22-tensorization-final-',dir='/private/tmp'))
packages=Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
lean=Path('/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source='NLA/IE22/VarianceTensorization.lean'
audit='reviews/variance-tensorization-author-evidence/ExactHelperTypesAndAxioms.lean'
inputs={f:sha(root/f) for f in [source,audit,'lake-manifest.json','lean-toolchain']}
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(build)]+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()])
commands=[];outputs=[]
for f in [source,audit]:
 out=build/Path(f).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 cmd=[str(lean),'-o',str(out),f]
 p=subprocess.run(cmd,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 commands.append({'argv':cmd,'exit_code':p.returncode});outputs.append(p.stdout)
 with (evidence/'fresh-build.log').open('a') as log:log.write('COMMAND '+json.dumps(cmd)+'\n'+p.stdout+'EXIT_STATUS='+str(p.returncode)+'\n')
 assert p.returncode==0 and not re.search(r'(^|\n).*\b(?:warning|error):',p.stdout),p.stdout
 assert all(sha(root/g)==h for g,h in inputs.items())
reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]+)\]",''.join(outputs))
names=['bounded_variance_prod_decomposition','bounded_variance_integral_le','bounded_variance_prod_le','bounded_variance_pi','gaussian_variance_tensorization','gaussian_coordinate_variance_integrable','bounded_integral_coordinate_resampling','gaussian_integral_coordinate_resampling']
assert [n for n,_ in reports]==['NLA.IE22.'+n for n in names]
assert all(set(a.split(', '))=={'propext','Classical.choice','Quot.sound'} for _,a in reports)
r={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'role':'Author evidence by Codex AI /root/ie21_final_correctness; not independent review of this IE22 module','result':'PASS: fresh module build, all8 exact helper statements, all8 axiom closures','source_sha256':inputs,'build_directory':str(build),'compiler':str(lean),'compiler_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),'LEAN_PATH':env['LEAN_PATH'],'commands':commands,'axiom_closures':{n:a.split(', ') for n,a in reports},'source_imports':[line for line in (root/source).read_text().splitlines() if line.startswith('import ')],'fresh_project_objects':True,'IE21_or_other_IE22_project_objects_imported':False,'warning_count':0,'error_count':0,'limitations':['Pinned upstream dependency olean cache reused; dependencies not rebuilt or remotely reauthenticated here.','No authentic Linux LeanCert/Comparator run performed; this is a bounded foundation, not the complete IE22 target.','Independent nonauthor review remains required.']}
(evidence/'fresh-build-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
