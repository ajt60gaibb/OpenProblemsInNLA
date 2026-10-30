#!/usr/bin/env python3
"""Fresh independent exact RE06 transcript/Frobenius support replay.
Actual literal consumers and rejection controls; no unconditional success/Target/CI claim.
"""
import argparse,hashlib,json,os,re,subprocess,tempfile
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--lean',type=Path,default=Path('/private/tmp/nla-oct23-lean-runtime/lean-4.33.1-darwin_aarch64/bin/lean'));p.add_argument('--packages',type=Path,default=Path('/Users/ajt253/.codex/worktrees/pf05-lean-proof/OpenProblemsInNLA/nonnegative-and-positive-factorizations/PF-05/lean/.lake/packages'));a=p.parse_args();repo=a.repo.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
C='a271ab2e3ef066187c4c7c26ca10c3f40bcf2ba9';read=lambda q:subprocess.check_output(['git','show',C+':'+q],cwd=repo);sha=lambda b:hashlib.sha256(b).hexdigest();manifest=json.loads(read('lean-statements/lake-manifest.json'));checks=[];records=[];error=None;objects={}
def ck(n,v,**x):
 checks.append(dict(name=n,passed=bool(v),**x))
 if not v:raise AssertionError(n)
def deps():
 d={}
 for e in manifest['packages']:
  r=a.packages/e['name'];h=subprocess.check_output(['git','-C',str(r),'rev-parse','HEAD']).decode().strip();s=subprocess.check_output(['git','-C',str(r),'status','--porcelain','--untracked-files=normal']).decode();ck('exact-clean-pinned-dependency:'+e['name'],h==e['rev'] and s=='');d[e['name']]=h
 return d
mods=['NLA.Computation.SVDMachine','NLA.Computation.NonadaptiveMatrixQuery','NLA.Statements.Infrastructure','NLA.Statements.RE06','Reviewed.RE06','NLA.Proofs.RE06.Transcript','NLA.Proofs.RE06.Frobenius','NLA.Proofs.RE06.TranscriptAudit'];source={m:read('lean-statements/'+m.replace('.','/')+'.lean').decode() for m in mods};selected=[]
for m in mods[5:]:
 ns=[]
 for raw in source[m].splitlines():
  line=raw.strip()
  if line.startswith('namespace '):ns.append(line[len('namespace '):].strip())
  elif line.startswith('end ') and ns:ns.pop()
  else:
   match=re.match(r'theorem\s+([A-Za-z_][A-Za-z0-9_\']*)',line)
   if match:selected.append('.'.join(ns+[match[1]]))
ck('exact28-source-theorems27support-plus-identity',len(selected)==28 and len(set(selected))==28)
aud='''import NLA.Proofs.RE06.TranscriptAudit
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Matrix.Norms.Frobenius
open NLA.Computation.NonadaptiveMatrixQuery NLA.Proofs.RE06
open Lean Elab Command in
elab "#inventory_theorem " n:ident : command => do
  let d ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  match (← getEnv).find? d with
  | some (.thmInfo _) => pure ()
  | _ => throwErrorAt n "inventory expects genuine theorem"
namespace Inventory.RE06.Transcript
theorem literal_minimum {m : ℕ} (score : Fin (m+2) → ℝ) (j : Fin (m+2)) :
    score (minimumIndex score) ≤ score j := minimumIndex_score_le score j
theorem literal_full_stored {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (P : Plan n)
    (hP : P.full = true) (i j : Fin n) :
    storedVector (oracleAnswers A P) j.val i = A i j := storedVector_full A P hP i j
theorem literal_full_error {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (ω : ℕ → ℝ) (hP : (makePlan n m ε ω).full = true) :
    frobenius A (run F A ε ω) = optimum A F := run_full_error F A ε ω hP
theorem literal_full_success {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hf : n ≤ firstWidth m ε+secondWidth m ε+thirdWidth m ε) :
    Successful F A ε := successful_full_branch F A ε hε hf
theorem literal_sketch0 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (P : Plan n)
    (hP : P.full = false) (j : Fin P.s) : storedVector (oracleAnswers A P) j.val =
    fun i => (A*P.G0) i j := storedVector_sketch0 A P hP j
theorem literal_sketch1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (P : Plan n)
    (hP : P.full = false) (j : Fin P.k) : storedVector (oracleAnswers A P) (P.s+j.val) =
    fun i => (A*P.G1) i j := storedVector_sketch1 A P hP j
theorem literal_sketchH {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (P : Plan n)
    (hP : P.full = false) (j : Fin P.ell) : storedVector (oracleAnswers A P) (P.s+P.k+j.val) =
    fun i => (A.transpose*P.H) i j := storedVector_sketchH A P hP j
theorem literal_warm {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ) (P : Plan n) :
    sketchWarmIndex F A P = minimumIndex (fun b => squaredFrobenius (A*P.G0) (F b*P.G0)) := rfl
theorem literal_repair {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ) (P : Plan n) :
    sketchRepair F A P = let b0 := sketchWarmIndex F A P; let Y := (A-F b0)*P.G1;
      F b0+Y*pseudoInverse (P.H.transpose*Y)*(P.H.transpose*(A-F b0)) := rfl
theorem literal_postprocess {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Plan n) (hP : P.full = false) : postprocess F P (oracleAnswers A P) =
    minimumIndex (fun b => squaredFrobenius (sketchRepair F A P) (F b)) := postprocess_sketch F A P hP
theorem literal_norm {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) ℝ) :
    frobenius X Y = ‖X-Y‖ := frobenius_eq_norm_sub X Y
theorem literal_triangle {a b : ℕ} (X Y Z : Matrix (Fin a) (Fin b) ℝ) :
    frobenius X Z ≤ frobenius X Y+frobenius Y Z := frobenius_triangle X Y Z
theorem literal_nearest {n m : ℕ} (F : Family n m) (A X : Matrix (Fin n) (Fin n) ℝ) :
    frobenius A (F (minimumIndex (fun b => squaredFrobenius X (F b)))) ≤
      optimum A F+2*frobenius A X := nearest_family_error F A X
theorem literal_run_error {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (ω : ℕ → ℝ) (hP : (makePlan n m ε ω).full = false) :
    frobenius A (run F A ε ω) ≤ optimum A F+2*frobenius A (sketchRepair F A (makePlan n m ε ω)) := run_sketch_error F A ε ω hP
theorem literal_repair_transfer {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ)
    (ε η : ℝ) (ω : ℕ → ℝ) (hP : (makePlan n m ε ω).full = false)
    (hRepair : frobenius A (sketchRepair F A (makePlan n m ε ω)) ≤ (1+2*η)*optimum A F) :
    frobenius A (run F A ε ω) ≤ (3+4*η)*optimum A F := run_sketch_error_of_repair F A ε η ω hP hRepair
theorem literal_live_identity : NLA.Statements.RE06.Target = NLA.ReviewedStatements.RE06.Target := rfl
end Inventory.RE06.Transcript
'''
literals=re.findall(r'^theorem (literal_[A-Za-z0-9_]+)',aud,re.M);ck('16-handwritten-literal-consumers',len(literals)==16)
all_selected=selected+['Inventory.RE06.Transcript.'+n for n in literals]
for n in all_selected:aud+='\n#inventory_theorem '+n+'\n#assert_trust kernel '+n+'\n#print axioms '+n+'\n'
aud+='''
open Lean Elab Command in
elab "#inventory_absent " n:ident : command => do
  if (← getEnv).contains n.getId then throwErrorAt n "unexpected unconditional public result"
#inventory_absent NLA.Proofs.RE06.successful
#inventory_absent NLA.Proofs.RE06.original_claim
#inventory_absent NLA.Proofs.RE06.explicit_claim
#inventory_absent NLA.Proofs.RE06.target
''';source['Inventory.Audit']=aud
full='''(n m : ℕ) (F : NLA.Computation.NonadaptiveMatrixQuery.Family n m)
(A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (he : 0≤ε)
(hf : n ≤ NLA.Computation.NonadaptiveMatrixQuery.firstWidth m ε+NLA.Computation.NonadaptiveMatrixQuery.secondWidth m ε+NLA.Computation.NonadaptiveMatrixQuery.thirdWidth m ε) :
 NLA.Computation.NonadaptiveMatrixQuery.Successful F A ε'''
repair='''(n m : ℕ) (F : NLA.Computation.NonadaptiveMatrixQuery.Family n m) (A : Matrix (Fin n) (Fin n) ℝ)
(ε η : ℝ) (ω : ℕ→ℝ) (hP : (NLA.Computation.NonadaptiveMatrixQuery.makePlan n m ε ω).full = false)
(hr : NLA.Computation.NonadaptiveMatrixQuery.frobenius A (NLA.Proofs.RE06.sketchRepair F A (NLA.Computation.NonadaptiveMatrixQuery.makePlan n m ε ω)) ≤ (1+2*η)*NLA.Computation.NonadaptiveMatrixQuery.optimum A F) :
 NLA.Computation.NonadaptiveMatrixQuery.frobenius A (NLA.Computation.NonadaptiveMatrixQuery.run F A ε ω) ≤ (3+4*η)*NLA.Computation.NonadaptiveMatrixQuery.optimum A F'''
base='import Inventory.Audit\nset_option leancert.trust "kernel"\n';negative={}
for name,typ in [('Full',full),('Repair',repair)]:
 negative['Inventory.Hole'+name]=('sorryAx',base+'theorem counterfeit '+typ+' := by sorry\n#assert_trust kernel counterfeit\n')
 negative['Inventory.Oracle'+name]=('oracle',base+'axiom oracle : False\ntheorem counterfeit '+typ+' := False.elim oracle\n#assert_trust kernel counterfeit\n')
for name,orig in [('Full','successful_full_branch'),('Repair','run_sketch_error_of_repair')]:
 negative['Inventory.Def'+name]=('inventory expects genuine theorem',base+'def counterfeit := @NLA.Proofs.RE06.'+orig+'\n#inventory_theorem counterfeit\n')
negative['Inventory.DropFullPremise']=('type mismatch',base+'''example : ∀ (n m : ℕ) (F : NLA.Computation.NonadaptiveMatrixQuery.Family n m) (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ), 0≤ε → NLA.Computation.NonadaptiveMatrixQuery.Successful F A ε := @NLA.Proofs.RE06.successful_full_branch
''')
negative['Inventory.DropRepairPremise']=('type mismatch',base+'''example : ∀ (n m : ℕ) (F : NLA.Computation.NonadaptiveMatrixQuery.Family n m) (A : Matrix (Fin n) (Fin n) ℝ) (ε η : ℝ) (ω : ℕ→ℝ), (NLA.Computation.NonadaptiveMatrixQuery.makePlan n m ε ω).full=false → NLA.Computation.NonadaptiveMatrixQuery.frobenius A (NLA.Computation.NonadaptiveMatrixQuery.run F A ε ω) ≤ (3+4*η)*NLA.Computation.NonadaptiveMatrixQuery.optimum A F := @NLA.Proofs.RE06.run_sketch_error_of_repair
''')
source.update({n:v[1] for n,v in negative.items()});before={};after={};version=''
try:
 before=deps();version=subprocess.check_output([str(a.lean),'--version']).decode().strip();ck('official-Lean4331-commit','4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version)
 with tempfile.TemporaryDirectory(prefix='nla-re06-transcript-inventory-',dir='/private/tmp') as tmp:
  tmp=Path(tmp);sr=tmp/'source';ob=tmp/'objects';sr.mkdir();ob.mkdir()
  for m,b in source.items():
   f=sr/(m.replace('.','/')+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_text(b);kept=out/'sources'/(m.replace('.','/')+'.lean.txt');kept.parent.mkdir(parents=True,exist_ok=True);kept.write_bytes(f.read_bytes())
  env=os.environ.copy();env['LEAN_PATH']=':'.join([str(ob)]+[str(a.packages/e['name']/'.lake/build/lib/lean') for e in manifest['packages']]+[str(a.lean.parent.parent/'lib/lean')]);env.pop('LEAN_SRC_PATH',None)
  for m in mods+['Inventory.Audit']+list(negative):
   f=sr/(m.replace('.','/')+'.lean');obj=ob/(m.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);argv=[str(a.lean),'-R',str(sr),'-o',str(obj),str(f)];run=subprocess.run(argv,cwd=sr,env=env,capture_output=True,text=True,timeout=600);log=run.stdout+run.stderr;(out/(m+'.log')).write_text(log)
   passed=run.returncode!=0 and negative[m][0].lower() in log.lower() if m in negative else run.returncode==0
   if m in negative and ('Hole' in m or 'Oracle' in m):passed=passed and 'error: #assert_trust:' in log
   records.append(dict(module=m,command=argv,source_sha256=sha(f.read_bytes()),log_sha256=sha(log.encode()),exit_code=run.returncode,expected_negative=m in negative,passed=passed));print(m,'PASS' if passed else 'FAIL',flush=True);ck('actual-Lean-outcome:'+m,passed)
   if obj.exists():objects[m]=dict(sha256=sha(obj.read_bytes()),bytes=obj.stat().st_size)
   if m=='Inventory.Audit':
    axioms=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log);ck('all44actual-kind-kernel-standard-axiom-audits',len(axioms)==44 and [n for n,x in axioms]==all_selected and all(set(z.strip() for z in x.split(',') if z.strip())<={'propext','Classical.choice','Quot.sound'} for n,x in axioms))
 after=deps();ck('dependency-pins-clean-before-and-after',before==after)
except Exception as e:error=str(e)
j=dict(reviewer='/root/inventory',authored_RE06_proof_sources=[],commit=C,scope='Independent fresh own replay of actual transcript/Frobenius conditional support, not unconditional success/fullTarget/CI/Comparator.',passed=error is None and len(records)==17 and all(x['passed'] for x in records),error=error,check_count=len(checks),checks=checks,commands=records,expected_commands=17,source_builds=8,own_literal_audit_builds=1,actual_negative_commands=8,selected_theorems=all_selected,handwritten_literal_consumers=16,lean_version=version,lean_binary_sha256=sha(a.lean.read_bytes()),dependency_heads_before=before,dependency_heads_after=after,object_sha256=objects,own_fresh_objects=True,objects_removed_after_replay=True,driver_sha256=sha(Path(__file__).read_bytes()))
(out/'RESULT.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps({k:j[k] for k in ['passed','error','check_count']}));raise SystemExit(0 if j['passed'] else 1)
