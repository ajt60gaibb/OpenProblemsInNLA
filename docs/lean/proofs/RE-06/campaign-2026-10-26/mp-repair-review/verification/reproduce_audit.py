#!/usr/bin/env python3
"""Audit the reviewer's own hash-bound fresh Gaussian prefix and run real controls."""
import argparse,datetime,hashlib,json,os,re,subprocess
from pathlib import Path
STD={'propext','Classical.choice','Quot.sound'}
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
 p=argparse.ArgumentParser()
 for n in ['repo','lean','packages','output']:p.add_argument('--'+n,type=Path,required=True)
 a=p.parse_args();s=json.loads((a.output/'SOURCE_RESULT.json').read_text());assert s['pass']
 build=Path(s['private_build']);src=build/'source';obj=build/'objects';checks=[];commands=[]
 def ck(n,v,**d):
  checks.append({'check':n,'pass':bool(v),**d})
  if not v:raise RuntimeError('Failed check: '+n)
 def blob(path):return subprocess.check_output(['git','-C',str(a.repo),'show',s['source_commit']+':'+path])
 ck('own_fresh63_source_result',s['reviewer']=='/root/verification' and s['source_commit']=='05ceb708f444ed36d34afe2eb1f2d98b0b059a0c' and len(s['commands'])==63 and len(s['source_records'])==63)
 ck('same_compiler_binary',sha(a.lean.read_bytes())==s['compiler_sha256'])
 for c in s['commands']:
  f=src/(c['module'].replace('.','/')+'.lean');o=obj/(c['module'].replace('.','/')+'.olean')
  ck('own_fresh_source_object:'+c['module'],c['exit_code']==0 and sha(f.read_bytes())==c['source_sha256'] and sha(o.read_bytes())==c['object_sha256'])
 manifest=json.loads(blob('lean-statements/lake-manifest.json'))
 def pins():
  out=[]
  for e in manifest['packages']:
   d=a.packages/e['name'];head=subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD'],text=True).strip();status=subprocess.check_output(['git','-C',str(d),'status','--porcelain','--untracked-files=no'],text=True);out.append({'name':e['name'],'expected':e['rev'],'actual':head,'tracked_clean':not status,'pass':head==e['rev'] and not status})
  return out
 before=pins();ck('continuous_ten_clean_dependency_pins',before==s['dependency_pins_after'] and all(e['pass'] for e in before))
 env=os.environ.copy();env['LEAN_PATH']=s['LEAN_PATH']
 def run(n,b,expected=0,needle=None):
  f=src/(n.replace('.','/')+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b);o=obj/(n.replace('.','/')+'.olean');o.parent.mkdir(parents=True,exist_ok=True)
  saved=a.output/'sources'/(n.replace('.','/')+'.lean.txt');saved.parent.mkdir(parents=True,exist_ok=True);saved.write_bytes(b)
  argv=[str(a.lean),'-R',str(src),'-o',str(o),str(f)];r=subprocess.run(argv,cwd=src,env=env,capture_output=True,text=True,timeout=420);log=r.stdout+r.stderr;(a.output/'logs'/(n+'.log')).write_text(log)
  c={'module':n,'argv':argv,'exit_code':r.returncode,'expected_exit':expected,'source_sha256':sha(b),'object_sha256':sha(o.read_bytes()) if o.exists() else None,'log_sha256':sha(log.encode())};commands.append(c);print(n,r.returncode,flush=True);ck('compiler:'+n,r.returncode==expected and (needle is None or needle in log),**c);return log
 # Reconstruct both bounded import closures independently from the frozen Git copies.
 recordmap={e['path']:e for e in s['source_records']}
 for key,expected_size in [('global-measurable-author',33),('actual-repair-author',52)]:
  wanted=set(s['scope_closures'][key]);seen=set()
  def visit(path):
   if path in seen:return
   seen.add(path)
   for child in re.findall(r'^import\s+([\w.]+)\s*$',blob(path).decode(),re.M):
    if child.startswith(('NLA.','Reviewed.')):visit('lean-statements/'+child.replace('.','/')+'.lean')
  for path in wanted:visit(path)
  ck('literal_closed_import_scope:'+key,seen==wanted and len(seen)==expected_size)
 newsets={};counts={}
 for key in ['pseudoinverse-author','fullrank-author','global-measurable-author','repair-author','actual-repair-author']:
  f=json.loads((a.output/(key+'-SOURCE_FREEZE.json')).read_text())
  new={e['path'] for e in f['files'] if e.get('new_in_chunk',True) and 'Audit.lean' not in e['path']}
  names={d['name'] for d in s['declarations'] if d['kind']=='theorem' and 'lean-statements/'+d['module'].replace('.','/')+'.lean' in new};newsets[key]=sorted(names);counts[key]=len(names)
  expected=f.get('new_actual_support_theorems',f.get('new_support_theorems'));ck('exact_frozen_support_count:'+key,len(names)==expected)
 guards=(a.output/'guards.txt').read_text();ca=(a.output/'consumers_a.lean.txt').read_text();cb=(a.output/'consumers_b.lean.txt').read_text()
 own=['IndependentA.'+n for n in re.findall(r'^\s*theorem (\w+)',ca,re.M)]+['IndependentB.'+n for n in re.findall(r'^\s*theorem (\w+)',cb,re.M)]
 audit='\n'.join('import '+e['module'] for e in s['source_records'])+'\nset_option leancert.trust "kernel"\n'+guards+'\n'
 for d in s['declarations']:audit+='#review_kind '+('thm' if d['kind']=='theorem' else 'defn')+' '+d['name']+'\n#assert_trust kernel '+d['name']+'\n#print axioms '+d['name']+'\n'
 audit+=ca+'\n'+cb
 for n in own:audit+='#review_kind thm '+n+'\n#assert_trust kernel '+n+'\n#print axioms '+n+'\n'
 for n in ['successful','original_claim','explicit_claim','target']:audit+='#review_absent NLA.Proofs.RE06.'+n+'\n'
 log=run('Independent.MPRepairAudit',audit.encode());closures={n:{x.strip() for x in v.split(',') if x.strip()} for n,v in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)}
 for n in re.findall(r"'([^']+)' does not depend on any axioms",log):closures[n]=set()
 expected={d['name'] for d in s['declarations']}|set(own)
 ck('all_actual_kinds_kernel_std3_only',set(closures)==expected and all(v<=STD for v in closures.values()),closures={n:sorted(v) for n,v in closures.items()})
 for n in ['NLA.Proofs.RE06.Pseudo.actual_isMP','NLA.Proofs.RE06.Pseudo.measurable_actual','NLA.Proofs.RE06.GaussianMoment.normSq_inverse_integral','NLA.Proofs.RE06.Repair.actual_svd_repair_majorant','NLA.Proofs.RE06.Repair.measurableSet_repairFailureSet']:
  ck('critical_exact_std3:'+n,closures[n]==STD)
 imports='import Independent.MPRepairAudit\nset_option leancert.trust "kernel"\nopen MeasureTheory ProbabilityTheory\nopen NLA.Computation.NonadaptiveMatrixQuery NLA.Proofs.RE06 NLA.Proofs.RE06.Repair\n'
 run('Negative.MPHole',(imports+'theorem MPHole {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) : Pseudo.IsMP B (pseudoInverse B) := by sorry\n#assert_trust kernel MPHole\n').encode(),1,'sorryAx')
 log=run('Negative.FrozenChallenge',blob('docs/lean/proofs/RE-06/campaign-2026-10-26/preproof/Challenge.lean'),1,'sorryAx');ck('six_actual_reference_holes_reject',log.count('depends on sorry or unrecognized axioms')==6)
 run('Negative.DefinitionKind',(imports+guards+'noncomputable def CounterfeitMajorant := @Repair.actual_svd_repair_majorant\n#review_kind thm CounterfeitMajorant\n').encode(),1,'review requires actual theorem')
 run('Negative.CustomAxiom',(imports+'axiom MPOracle {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) : Pseudo.IsMP B (pseudoInverse B)\ntheorem TaintedMP {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) : Pseudo.IsMP B (pseudoInverse B) := MPOracle B\n#assert_trust kernel TaintedMP\n').encode(),1,'custom: MPOracle')
 fixtures={
 'MissingReverseRank':"""example {a r b : ℕ} (C : Matrix (Fin a) (Fin r) ℝ) (R : Matrix (Fin r) (Fin b) ℝ) :
   pseudoInverse (C*R)=pseudoInverse R*pseudoInverse C := Pseudo.reverse_order C R
 """,
 'MissingNormDimension':"""example : (∫ x : Fin 2 → ℝ, (GaussianMoment.normSq x)⁻¹
   ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) = 1 / ((2 : ℝ)-2) :=
   GaussianMoment.normSq_inverse_integral 2
 """,
 'MissingFullrankDimension':"""example (d p offset : ℕ) : ∀ᵐ ω ∂GaussianLaw,
   (gaussianBlock d p offset ω*(gaussianBlock d p offset ω).transpose).det ≠ 0 :=
   GaussianMoment.stream_block_gram_det_ne_zero_ae d p offset
 """,
 'MissingHeadRank':"""example {n k ell : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (hr : r ≤ n)
   (G : Matrix (Fin n) (Fin k) ℝ) (Ht : Matrix (Fin ell) (Fin n) ℝ) :
   squaredFrobenius (C-(C*G)*pseudoInverse (Ht*(C*G))*(Ht*C)) 0 ≤
   residualTailEnergy C r+actualExcessMajorant C r hr G Ht := actual_svd_repair_majorant C r hr G Ht
 """,
 'MissingUniformRepair':"""example {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ)
   (ε η δ : ℝ) (hsketch : firstWidth m ε+secondWidth m ε+thirdWidth m ε < n) :
   NullMeasurableSet {ω | (1+η)*residualTailEnergy (A-F (sketchWarmIndex F A (makePlan n m ε ω))) (rootWidth m) <
     squaredFrobenius A (sketchRepair F A (makePlan n m ε ω))} GaussianLaw ∧
   GaussianLaw.real {ω | (1+η)*residualTailEnergy (A-F (sketchWarmIndex F A (makePlan n m ε ω))) (rootWidth m) <
     squaredFrobenius A (sketchRepair F A (makePlan n m ε ω))} ≤ δ :=
   actual_selected_repair_failure_le F A ε η δ hsketch
 """}
 for name,b in fixtures.items():
  log=run('Negative.'+name,(imports+b).encode(),1);ck('premise_rejection:'+name,'Type mismatch' in log or 'type mismatch' in log)
 after=pins();ck('ten_clean_pins_continuous_after',after==before and all(e['pass'] for e in after))
 for c in s['commands']:
  f=src/(c['module'].replace('.','/')+'.lean');o=obj/(c['module'].replace('.','/')+'.olean');ck('original_private_object_unchanged:'+c['module'],sha(f.read_bytes())==c['source_sha256'] and sha(o.read_bytes())==c['object_sha256'])
 r={'pass':all(c['pass'] for c in checks),'reviewer':'/root/verification','non_author':True,'UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_commit':s['source_commit'],'freeze_epochs':s['freeze_epochs'],'scope_support_names':newsets,'scope_support_counts':counts,'source_result_sha256':sha((a.output/'SOURCE_RESULT.json').read_bytes()),'scope':'Separate A95 and B18+41 support scopes, shared fresh63 source prefix; no rectangular inverse moment, full success/Target or CI claim','checks':checks,'commands':commands,'own_consumers':own,'dependency_pins_before':before,'dependency_pins_after':after,'private_build':str(build),'script_sha256':sha(Path(__file__).read_bytes()),'guards_sha256':sha((a.output/'guards.txt').read_bytes()),'consumers_a_sha256':sha((a.output/'consumers_a.lean.txt').read_bytes()),'consumers_b_sha256':sha((a.output/'consumers_b.lean.txt').read_bytes()),'new_Linux_execution':False,'Comparator_execution':False}
 (a.output/'AUDIT_RESULT.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'pass':r['pass'],'audit_checks':len(checks),'audit_commands':len(commands),'actual_declarations':len(s['declarations']),'own_consumers':len(own)}),flush=True)
if __name__=='__main__':main()
