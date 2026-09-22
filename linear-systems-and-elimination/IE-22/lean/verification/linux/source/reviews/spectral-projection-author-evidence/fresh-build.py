from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,tempfile
root=Path(__file__).resolve().parents[2];evidence=Path(__file__).resolve().parent
build=Path(tempfile.mkdtemp(prefix='nla-ie22-spectral-final-',dir='/private/tmp'))
previous=root.parents[1]/'IE-21/lean'
r=json.loads((previous/'reviews/ie21-final-fidelity-evidence/build-receipt.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
boundary=json.loads((root/'reviews/statement-freeze.json').read_text())['mathematical_boundary_sha256']
for f,d in boundary.items():assert sha(root/f)==d
vendored=json.loads((root/'reviews/IE21-DEPENDENCY.json').read_text())['source_sha256']
for f,d in vendored.items():assert sha(root/f)==d
(build/'NLA').mkdir(exist_ok=True)
(build/'NLA/IE21').symlink_to(Path(r['build_directory'])/'NLA/IE21',target_is_directory=True)
packages=Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
lean=Path('/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean')
source='NLA/IE22/SpectralProjection.lean'
audit='reviews/spectral-projection-author-evidence/ExactSelectedTypesAndAxioms.lean'
inputs={f:sha(root/f) for f in ['NLA/IE22/Definitions.lean',source,audit,'Challenge.lean','NUMERICAL_TARGETS.md','comparator.json','lake-manifest.json','lean-toolchain','reviews/statement-freeze.json'] if (root/f).exists()}
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(build)]+[str(p/'.lake/build/lib/lean') for p in sorted(packages.iterdir()) if p.is_dir()])
commands=[];outputs=[]
for f in ['NLA/IE22/Definitions.lean',source,audit]:
 out=build/Path(f).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 cmd=[str(lean),'-o',str(out),f]
 p=subprocess.run(cmd,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 commands.append({'argv':cmd,'exit_code':p.returncode});outputs.append(p.stdout)
 with (evidence/'fresh-build.log').open('a') as log:log.write('COMMAND '+json.dumps(cmd)+'\n'+p.stdout+'EXIT_STATUS='+str(p.returncode)+'\n')
 assert p.returncode==0 and not re.search(r'(^|\n).*\b(?:warning|error):',p.stdout),p.stdout
 assert all(sha(root/g)==h for g,h in inputs.items())
reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]+)\]",''.join(outputs))
names=['matrixMap_eq_row_inner','projected_matrixMap','projected_row_norm_le','projection_semantics','orthonormalSynthesis','gram_trace_row_norms','spectral_projection']
assert [n for n,_ in reports]==['NLA.IE22.'+n for n in names]
assert all(set(a.split(', '))=={'propext','Classical.choice','Quot.sound'} for _,a in reports)
r={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'role':'Author evidence by Codex AI /root/ie21_final_correctness; not independent review of IE22','result':'PASS: fresh Definitions and SpectralProjection builds, both exact frozen selected statements, all seven helper axiom closures','source_sha256':inputs,'vendored_IE21_source_sha256':vendored,'build_directory':str(build),'compiler':str(lean),'compiler_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),'LEAN_PATH':env['LEAN_PATH'],'commands':commands,'axiom_closures':{n:a.split(', ') for n,a in reports},'source_imports':[line for line in (root/source).read_text().splitlines() if line.startswith('import ')],'fresh_IE22_project_objects':True,'verified_IE21_objects_reused':True,'warning_count':0,'error_count':0,'limitations':['Pinned upstream dependency olean cache and previously checked unchanged IE21 dependency objects reused; these dependencies were not rebuilt here.','No authentic Linux LeanCert/Comparator run performed; this is a bounded proof module, not the complete IE22 target.','Independent nonauthor review remains required.']}
(evidence/'fresh-build-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
