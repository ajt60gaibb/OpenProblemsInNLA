from pathlib import Path
import hashlib,json,re,subprocess,os,tempfile,datetime
root=Path(__file__).resolve().parents[2]; ev=Path(__file__).resolve().parent
build=Path(tempfile.mkdtemp(prefix='nla-ie21-final-fidelity-',dir='/private/tmp'))
lean=Path('/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean')
packages=Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
env=dict(os.environ);env['LEAN_PATH']=os.pathsep.join([str(build),str(root)]+[str(x/'.lake/build/lib/lean') for x in sorted(packages.iterdir()) if x.is_dir()])
sources={str(x.relative_to(root)).removesuffix('.lean').replace('/','.'):x for x in (root/'NLA/IE21').glob('*.lean')}
config=json.loads((root/'comparator.json').read_text());names=config['theorem_names'];assert len(names)==23
order=[];active=set()
def visit(n):
 if n in order:return
 assert n not in active
 active.add(n)
 for p in re.findall(r'^import\s+(NLA\.IE21\.\w+)\s*$',sources[n].read_text(),re.M):visit(p)
 active.remove(n);order.append(n)
visit('NLA.IE21.FiniteSize');assert set(order)==set(sources)
hashes={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources.values()}
challenge=(root/'Challenge.lean').read_text()
headers=re.findall(r'\btheorem\s+(\w+)\s+([\s\S]*?)\s*:= by sorry',challenge)
assert ['NLA.IE21.'+n for n,_ in headers]==names
checks=[]
for name,sig in headers:
 depth=0;colon=None
 for i,c in enumerate(sig):
  if c in '([{':depth+=1
  elif c in ')]}':depth-=1
  elif c==':' and depth==0:colon=i;break
 assert colon is not None,name
 checks.append('example : ∀ '+sig[:colon].strip()+',\n  '+sig[colon+1:].strip()+' := @NLA.IE21.'+name+'\n')
audit=ev/'ExactSignaturesAndAxioms.lean';audit.write_text('import NLA.IE21.FiniteSize\nset_option autoImplicit false\nnoncomputable section\nopen MeasureTheory ProbabilityTheory Filter Set\nopen scoped BigOperators ENNReal RealInnerProductSpace Topology\nnamespace NLA.IE21\n'+ '\n'.join(checks)+ ''.join('#print axioms '+n+'\n' for n in names)+'end NLA.IE21\n')
results=[]
with (ev/'typecheck.log').open('w') as log:
 log.write('Independent nonauthor source rebuild and exact frozen signatures; local cached dependencies, no authentic LeanCert or Comparator claim.\n')
 log.write(subprocess.check_output([str(lean),'--version'],text=True))
 for n in order+['ExactSignaturesAndAxioms']:
  p=sources[n] if n in sources else audit
  cmd=[str(lean)]
  if n in sources:
   out=build/Path(n.replace('.','/')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);cmd+=['-o',str(out)]
  cmd+=[str(p.relative_to(root))]
  log.write('COMMAND '+json.dumps(cmd)+'\n');log.flush()
  r=subprocess.run(cmd,cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  log.write(r.stdout+'EXIT '+str(r.returncode)+'\n');log.flush()
  results.append({'source':str(p.relative_to(root)),'exit_code':r.returncode,'output':r.stdout})
  print(n,r.returncode,flush=True)
  if r.returncode:raise SystemExit(r.returncode)
assert hashes=={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources.values()},'Sources changed during independent rebuild'
closures={n:[a.strip() for a in ax.split(',') if a.strip()] for n,ax in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",results[-1]['output'])}
assert set(closures)==set(names)
assert all(set(ax)<=set(config['permitted_axioms']) for ax in closures.values())
record={'completed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'role':'Codex AI independent nonauthor final fidelity referee','project_sources_rebuilt':len(order),'selected_exact_signature_checks':len(headers),'selected_axiom_closures':closures,'source_hashes':hashes,'build_directory':str(build),'commands':results,'limits':['Local cached dependencies; not fresh source authentication','No authentic LeanCert assertions or Linux Comparator executed in this local review'],'evidence_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),audit,ev/'typecheck.log']}}
(ev/'build-receipt.json').write_text(json.dumps(record,indent=2)+'\n');print('PASS all 31 sources, 23 exact signature checks, 23 permitted axiom closures',flush=True)
