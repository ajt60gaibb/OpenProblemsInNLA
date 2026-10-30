#!/usr/bin/env python3
"""Fresh non-author exact closed d043 Gaussian support replay; no CI/fullTarget claim."""
import argparse,hashlib,json,os,re,subprocess,tempfile
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--lean',type=Path,default=Path('/private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean'));p.add_argument('--packages',type=Path,default=Path('/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages'));a=p.parse_args();repo=a.repo.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
C='d043142e4d7dd45c8a8aee5d10f989f44c356cb9';META='21b660e25e313fe6f1d43b57d1338522bf50ea38';D='docs/lean/proofs/RE-06/campaign-2026-10-26/gaussian-author/';sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda q,ref=C:subprocess.check_output(['git','show',ref+':'+q],cwd=repo);freeze=json.loads(read(D+'SOURCE_FREEZE.json'));binding=json.loads(read(D+'CLOSED_SOURCE_BINDING.json',META));manifest=json.loads(read('lean-statements/lake-manifest.json'));checks=[];records=[];objects={};error=None;source={};mods=[]
def ck(n,v,**x):
 checks.append(dict(name=n,passed=bool(v),**x))
 if not v:raise AssertionError(n)
def walk(m):
 if m in source:return
 text=read('lean-statements/'+m.replace('.','/')+'.lean').decode();source[m]=text
 for line in text.splitlines():
  if line.startswith('import '):
   for dep in line.split()[1:]:
    if dep.startswith(('NLA.','Reviewed.')):walk(dep)
 mods.append(m)
for q in freeze['files']:walk(q.removeprefix('lean-statements/').removesuffix('.lean').replace('/','.'))
ck('exact23-complete-Gaussian-closure',len(mods)==23 and {'lean-statements/'+m.replace('.','/')+'.lean' for m in mods}=={x['path'] for x in binding['files']})
for m in ['NLA.Statements.Infrastructure','NLA.Statements.RE06','Reviewed.RE06']:walk(m)
ck('26-exact-replay-sources-with-original-boundary',len(mods)==26)
for e in binding['files']:ck('exact-binding-source:'+e['path'],sha(source[e['path'].removeprefix('lean-statements/').removesuffix('.lean').replace('/','.')].encode())==e['sha256'])
selected=[];definitions=[]
for m in mods:
 if not m.startswith('NLA.Proofs.'):continue
 ns=[]
 for raw in source[m].splitlines():
  line=raw.strip()
  if line.startswith('namespace '):ns.append(line[len('namespace '):].strip())
  elif line.startswith('end ') and ns:ns.pop()
  else:
   found=re.match(r'(theorem|(?:noncomputable )?def|abbrev)\s+([A-Za-z_][A-Za-z0-9_\']*)',line)
   if found:
    name='.'.join(ns+[found[2]])
    (selected if found[1]=='theorem' else definitions).append(name)
ck('source-declarations-unique',len(selected)==len(set(selected)) and len(definitions)==len(set(definitions)))
aud=(Path(__file__).resolve().parent/'InventoryGaussianAudit.lean.txt').read_text();literals=re.findall(r'^theorem (literal_[A-Za-z0-9_]+)',aud,re.M);ck('15-handwritten-literal-consumers',len(literals)==15)
all_selected=selected+['Inventory.RE06.Gaussian.'+n for n in literals]
for n in all_selected:aud+='\n#inventory_theorem '+n+'\n#assert_trust kernel '+n+'\n#print axioms '+n+'\n'
for n in definitions:aud+='\n#assert_trust kernel '+n+'\n#print axioms '+n+'\n'
aud+='''
open Lean Elab Command in
elab "#inventory_absent " n:ident : command => do
  if (← getEnv).contains n.getId then throwErrorAt n "unexpected full public proof"
#inventory_absent NLA.Proofs.RE06.successful
#inventory_absent NLA.Proofs.RE06.original_claim
#inventory_absent NLA.Proofs.RE06.explicit_claim
#inventory_absent NLA.Proofs.RE06.target
''';source['Inventory.Audit']=aud
base='import Inventory.Audit\nset_option leancert.trust "kernel"\nopen scoped BigOperators NNReal ENNReal\nopen MeasureTheory ProbabilityTheory NLA.Computation.NonadaptiveMatrixQuery NLA.Proofs.RE06\n'
lower='''{n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (q offset r : ℕ) (hr : r<n) (η : ℝ) (hη0 : 0<η) (hη1 : η≤1) : GaussianLaw.real {ω | squaredFrobenius (B*gaussianBlock n q offset ω) 0 < (q : ℝ)*(1-η)*residualTailEnergy B r} ≤ Real.exp (-(q : ℝ)*(r : ℝ)*η/4)'''
warm='''{n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ) (q offset r : ℕ) (hq : 0<q) (hr : r<n) (η : ℝ) (hη0 : 0<η) (hη1 : η<1) : GaussianLaw.real {ω | ((1+η)/(1-η))*(optimum A F)^2 < residualTailEnergy (A-F (gaussianWarmIndex F A q offset ω)) r} ≤ (m+2 : ℝ)*Real.exp (-(q : ℝ)*(r : ℝ)*η/4)+Real.exp (-(q : ℝ)*η^2/8)'''
negative={}
for name,typ in [('Lower',lower),('Warm',warm)]:
 negative['Inventory.Hole'+name]=('sorryax',base+'theorem counterfeit '+typ+' := by sorry\n#assert_trust kernel counterfeit\n')
 negative['Inventory.Oracle'+name]=('oracle',base+'axiom oracle : False\ntheorem counterfeit '+typ+' := False.elim oracle\n#assert_trust kernel counterfeit\n')
for name,orig in [('Energy','residualGaussian_energy'),('Warm','gaussianWarmIndex_tail_bound')]:negative['Inventory.Def'+name]=('inventory expects genuine theorem',base+'def counterfeit := @'+orig+'\n#inventory_theorem counterfeit\n')
negative['Inventory.DropUnscaledFactor']=('type mismatch',base+'''example : ∀ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (q offset r : ℕ) (hr : r<n) (η : ℝ), 0<η → η≤1 → GaussianLaw.real {ω | squaredFrobenius (B*gaussianBlock n q offset ω) 0 < (1-η)*residualTailEnergy B r} ≤ Real.exp (-(q : ℝ)*(r : ℝ)*η/4) := @residualGaussian_lower_tail
''')
negative['Inventory.DropStreamInjectivity']=('type mismatch',base+'''example : ∀ {ι : Type} [Fintype ι] (f : ι→ℕ), HasLaw (fun ω : ℕ→ℝ => fun i => ω (f i)) (Measure.pi (fun _ : ι => gaussianReal 0 1)) GaussianLaw := @finite_stream_selection_hasLaw
''')
source.update({n:v[1] for n,v in negative.items()})
def deps():
 ans={}
 for e in manifest['packages']:
  r=a.packages/e['name'];h=subprocess.check_output(['git','-C',str(r),'rev-parse','HEAD']).decode().strip();status=subprocess.check_output(['git','-C',str(r),'status','--porcelain','--untracked-files=normal']).decode();ck('exact-clean-dependency:'+e['name'],h==e['rev'] and status=='');ans[e['name']]=h
 return ans
before={};after={};version=''
try:
 before=deps();version=subprocess.check_output([str(a.lean),'--version']).decode().strip();ck('official-Lean4331-commit','4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version)
 with tempfile.TemporaryDirectory(prefix='nla-re06-Gaussian-inventory-',dir='/private/tmp') as tmp:
  tmp=Path(tmp);sr=tmp/'source';ob=tmp/'objects';sr.mkdir();ob.mkdir()
  for m,b in source.items():
   f=sr/(m.replace('.','/')+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_text(b);dest=out/'sources'/(m.replace('.','/')+'.lean.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(f.read_bytes())
  env=os.environ.copy();env['LEAN_PATH']=':'.join([str(ob)]+[str(a.packages/e['name']/'.lake/build/lib/lean') for e in manifest['packages']]+[str(a.lean.parent.parent/'lib/lean')]);env.pop('LEAN_SRC_PATH',None)
  for m in mods+['Inventory.Audit']+list(negative):
   f=sr/(m.replace('.','/')+'.lean');obj=ob/(m.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);argv=[str(a.lean),'-R',str(sr),'-o',str(obj),str(f)];run=subprocess.run(argv,cwd=sr,env=env,capture_output=True,text=True,timeout=900);log=run.stdout+run.stderr;(out/(m+'.log')).write_text(log)
   passed=run.returncode!=0 and negative[m][0] in log.lower() if m in negative else run.returncode==0
   if m in negative and ('Hole' in m or 'Oracle' in m):passed=passed and 'error: #assert_trust:' in log
   records.append(dict(module=m,command=argv,source_sha256=sha(f.read_bytes()),log_sha256=sha(log.encode()),exit_code=run.returncode,expected_negative=m in negative,warning_count=log.count('warning:'),passed=passed));print(m,'PASS' if passed else 'FAIL',flush=True);ck('actual-Lean-outcome:'+m,passed)
   if obj.exists():objects[m]=dict(sha256=sha(obj.read_bytes()),bytes=obj.stat().st_size)
   if m=='Inventory.Audit':
    axioms=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log);ck('every-selected-genuine-theorem-and-definition-kernel-standard-axioms',len(axioms)==len(all_selected)+len(definitions) and [n for n,x in axioms]==all_selected+definitions and all(set(z.strip() for z in x.split(',') if z.strip())<={'propext','Classical.choice','Quot.sound'} for n,x in axioms))
 after=deps();ck('clean-pins-before-and-after',before==after)
except Exception as e:error=str(e)
j=dict(reviewer='/root/inventory',authored_RE06_proof_sources=[],commit=C,binding_metadata_commit=META,scope='Independent exact26-source closure (23Gaussian plus3original boundary) and15literal consumers, no unconditional success/fullTarget/CI/Comparator.',passed=error is None and len(records)==35 and all(x['passed'] for x in records),error=error,check_count=len(checks),checks=checks,commands=records,expected_commands=35,actual_Gaussian_closure_sources=23,extra_original_boundary_sources=3,literal_consumers=15,actual_negative_commands=8,selected_theorems=all_selected,source_theorem_count=len(selected),kernel_checked_definitions=definitions,own_fresh_project_objects=True,own_objects_removed_after_replay=True,object_sha256=objects,lean_version=version,lean_binary_sha256=sha(a.lean.read_bytes()),dependency_heads_before=before,dependency_heads_after=after,driver_sha256=sha(Path(__file__).read_bytes()))
(out/'RESULT.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps({k:j[k] for k in ['passed','error','check_count','source_theorem_count']}));raise SystemExit(0 if j['passed'] else 1)
