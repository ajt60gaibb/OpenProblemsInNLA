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
 ck('own_fresh26_source_result',s['reviewer']=='/root/verification' and s['source_commit']=='d043142e4d7dd45c8a8aee5d10f989f44c356cb9' and len(s['commands'])==26 and len(s['source_records'])==26)
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
 guards=(a.output/'guards.txt').read_text();consumers=(a.output/'consumers.lean.txt').read_text();own=re.findall(r'^theorem (\w+)',consumers,re.M)
 audit='\n'.join('import '+e['module'] for e in s['source_records'])+'\nset_option leancert.trust "kernel"\n'+guards+'\n'
 for d in s['declarations']:audit+='#review_kind '+('thm' if d['kind']=='theorem' else 'defn')+' '+d['name']+'\n#assert_trust kernel '+d['name']+'\n#print axioms '+d['name']+'\n'
 audit+=consumers
 for n in own:audit+='#review_kind thm Independent.'+n+'\n#assert_trust kernel Independent.'+n+'\n#print axioms Independent.'+n+'\n'
 for n in ['successful','original_claim','explicit_claim','target']:audit+='#review_absent NLA.Proofs.RE06.'+n+'\n'
 log=run('Independent.GaussianAudit',audit.encode());closures={n:{x.strip() for x in v.split(',') if x.strip()} for n,v in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)}
 for n in re.findall(r"'([^']+)' does not depend on any axioms",log):closures[n]=set()
 expected={d['name'] for d in s['declarations']}|{'Independent.'+n for n in own}
 ck('all_actual_kinds_kernel_std3_only',set(closures)==expected and all(v<=STD for v in closures.values()),closures={n:sorted(v) for n,v in closures.items()})
 for n in ['sketchWarmIndex_tail_bound','residualGaussian_energy','gaussianThreeBlocks_hasLaw','gaussian_square_exp_integral']:ck('critical_exact_std3:'+n,closures['NLA.Proofs.RE06.'+n]==STD)
 imports='import NLA.Proofs.RE06.GaussianWarmStartResidual\nset_option leancert.trust "kernel"\nopen scoped BigOperators\nopen MeasureTheory ProbabilityTheory\nopen NLA.Computation.NonadaptiveMatrixQuery NLA.Proofs.RE06\n'
 scalar='(t : ℝ) (ht : t < 1 / 2) : (∫ x : ℝ, Real.exp (t*x^2) ∂gaussianReal 0 1) = (Real.sqrt (1-2*t))⁻¹'
 run('Negative.QuadraticHole',(imports+'theorem QuadraticHole '+scalar+' := by sorry\n#assert_trust kernel QuadraticHole\n').encode(),1,'sorryAx')
 log=run('Negative.FrozenChallenge',blob('docs/lean/proofs/RE-06/campaign-2026-10-26/preproof/Challenge.lean'),1,'sorryAx');ck('all_six_reference_holes_reject',log.count('depends on sorry or unrecognized axioms')==6)
 run('Negative.DefinitionKind',(imports+guards+'noncomputable def CounterfeitWarm := @NLA.Proofs.RE06.sketchWarmIndex_tail_bound\n#review_kind thm CounterfeitWarm\n').encode(),1,'review requires actual theorem')
 run('Negative.CustomAxiom',(imports+'axiom GaussianOracle '+scalar+'\ntheorem TaintedGaussian '+scalar+' := GaussianOracle t ht\n#assert_trust kernel TaintedGaussian\n').encode(),1,'custom: GaussianOracle')
 wrong='''example {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (q offset : ℕ)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    GaussianLaw.real {ω | (1+η)*squaredFrobenius B 0 <
      squaredFrobenius (B * gaussianBlock n q offset ω) 0} ≤
      Real.exp (-(q : ℝ)*η^2/8) := residualGaussian_upper_tail B q offset η hη0 hη1
'''
 log=run('Negative.MissingUnscaledFactor',(imports+wrong).encode(),1);ck('normalization_change_rejected','Type mismatch' in log or 'type mismatch' in log)
 overlap='''example : HasLaw (fun ω : ℕ → ℝ => fun _i : Fin 2 => ω 0)
    (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) GaussianLaw :=
  finite_stream_selection_hasLaw (fun _i : Fin 2 => 0)
'''
 log=run('Negative.MissingInjectivity',(imports+overlap).encode(),1);ck('coordinate_injectivity_cannot_be_dropped','Type mismatch' in log or 'type mismatch' in log)
 domain='''example : (∫ x : ℝ, Real.exp ((1 : ℝ)*x^2) ∂gaussianReal 0 1) =
    (Real.sqrt (1-2*(1 : ℝ)))⁻¹ := gaussian_square_exp_integral 1
'''
 log=run('Negative.MissingMGFDomain',(imports+domain).encode(),1);ck('quadratic_MGF_domain_cannot_be_dropped','Type mismatch' in log or 'type mismatch' in log)
 after=pins();ck('ten_clean_pins_continuous_after',after==before and all(e['pass'] for e in after))
 for c in s['commands']:
  f=src/(c['module'].replace('.','/')+'.lean');o=obj/(c['module'].replace('.','/')+'.olean');ck('original_private_object_unchanged:'+c['module'],sha(f.read_bytes())==c['source_sha256'] and sha(o.read_bytes())==c['object_sha256'])
 r={'pass':all(c['pass'] for c in checks),'reviewer':'/root/verification','non_author':True,'UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_commit':s['source_commit'],'binding_metadata_commit':s['binding_metadata_commit'],'source_result_sha256':sha((a.output/'SOURCE_RESULT.json').read_bytes()),'scope':'16 frozen Gaussian support modules with own complete fresh closure; no full success/Target/CI claim','checks':checks,'commands':commands,'own_consumers':own,'dependency_pins_before':before,'dependency_pins_after':after,'private_build':str(build),'script_sha256':sha(Path(__file__).read_bytes()),'guards_sha256':sha((a.output/'guards.txt').read_bytes()),'consumers_sha256':sha((a.output/'consumers.lean.txt').read_bytes()),'new_Linux_execution':False,'Comparator_execution':False}
 (a.output/'AUDIT_RESULT.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'pass':r['pass'],'audit_checks':len(checks),'audit_commands':len(commands),'actual_declarations':len(s['declarations']),'own_consumers':len(own)}),flush=True)
if __name__=='__main__':main()
