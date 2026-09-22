"""Independent nonauthor IE-21 proof rebuild and frozen-type audit; no authentic Linux claim."""
from pathlib import Path
import os,re,hashlib,subprocess,tempfile,json,datetime
review=Path(__file__).resolve().parent;project=review.parents[1]
compiler=Path('/private/tmp/nla-campaign-toolchain/lean-4.33.1-darwin_aarch64/bin/lean')
cache=Path('/private/tmp/nla-formalization-campaign-20260915/linear-systems-and-elimination/IE-15/lean/.lake/packages')
out=Path(tempfile.mkdtemp(prefix='ie21-independent-correctness-',dir='/private/tmp'))
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,[out,project]+sorted(cache.glob('*/.lake/build/lib/lean'))))
source={'.'.join(p.relative_to(project).with_suffix('').parts):p for p in project.glob('NLA/IE21/*.lean')}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inputs={str(p.relative_to(project)):sha(p) for p in source.values()}
inputs.update({p:sha(project/p) for p in ['Challenge.lean','NUMERICAL_TARGETS.md','comparator.json','lakefile.toml','lake-manifest.json','lean-toolchain']})
(review/'initial-input-hashes.json').write_text(json.dumps(inputs,indent=2)+'\n')
freeze=json.loads((project/'reviews/statement-freeze.json').read_text())['mathematical_boundary_sha256']
assert all(inputs[k]==v for k,v in freeze.items())
order=[];active=set()
def visit(k):
 if k in order:return
 assert k not in active
 active.add(k)
 for imp in re.findall(r'^import\s+(\S+)',source[k].read_text(),re.M):
  assert imp!='Challenge'
  if imp.startswith('NLA.'):visit(imp)
 active.remove(k);order.append(k)
for k in sorted(source):visit(k)
records=[]
with (review/'typecheck.log').open('w') as log:
 log.write(subprocess.check_output([str(compiler),'--version'],text=True))
 for k in order+['ExactTypesAndAxioms']:
  p=source[k] if k in source else review/'ExactTypesAndAxioms.lean'
  cmd=[str(compiler)]
  if k in source:
   dest=out/Path(*k.split('.')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);cmd+=['-o',str(dest)]
  cmd.append(str(p.relative_to(project)))
  log.write('COMMAND '+json.dumps(cmd)+'\n');log.flush()
  x=subprocess.run(cmd,cwd=project,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  log.write(x.stdout+'EXIT '+str(x.returncode)+'\n');log.flush();print(k,x.returncode,flush=True)
  records.append({'module':k,'command':cmd,'exit_code':x.returncode,'output':x.stdout})
  if x.returncode:raise SystemExit(x.returncode)
  assert not re.search(r'\b(?:warning|error):',x.stdout),x.stdout
assert all(sha(project/k)==v for k,v in inputs.items())
config=json.loads((project/'comparator.json').read_text())
closures={n:re.findall(r'\S+',a.replace(',',' ')) for n,a in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",records[-1]['output'])}
assert set(closures)==set(config['theorem_names'])
assert all(set(x)<=set(config['permitted_axioms']) for x in closures.values())
r={'reviewer':'Codex AI independent nonauthor correctness referee','timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'result':'PASS local independent proof rebuild and all23 exact frozen types; authentic Linux gates pending','build_directory':str(out),'module_count':len(order),'source_hashes':inputs,'selected_axiom_closures':closures,'commands':records,'toolchain_version':subprocess.check_output([str(compiler),'--version'],text=True).strip(),'compiler_sha256':sha(compiler),'reviewer_evidence_sha256':{p.name:sha(p) for p in [Path(__file__),(review/'ExactTypesAndAxioms.lean'),review/'typecheck.log']},'limits':['Dependency artifacts are shared cached artifacts; project artifacts are rebuilt in a fresh reviewer-only directory.','Authentic LeanCert kernel trust and actual Linux Lean4 Comparator are separate pending gates.','This is AI agent review, not external human peer review or official Tau Ceti endorsement.']}
(review/'rebuild-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print('PASS',flush=True)
