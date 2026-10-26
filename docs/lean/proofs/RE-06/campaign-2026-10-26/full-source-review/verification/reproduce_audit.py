#!/usr/bin/env python3
"""Independent full RE06 source audit and expected-phase negative commands.

Uses only the reviewer's SOURCE_RESULT prefix, including its explicitly bound
own-object intersection. It also works after a wholly fresh 87-source replay.
"""
import argparse, datetime, hashlib, json, os, re, subprocess
from pathlib import Path

REF = '181c365dc426875aaa61984c901478b1b7c696e6'
PRE = 'docs/lean/proofs/RE-06/campaign-2026-10-26/preproof/'
STD = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(b): return hashlib.sha256(b).hexdigest()

def main():
    p=argparse.ArgumentParser()
    for n in ['repo','lean','packages','output']: p.add_argument('--'+n,type=Path,required=True)
    a=p.parse_args(); sb=(a.output/'SOURCE_RESULT.json').read_bytes();s=json.loads(sb)
    build=Path(s['private_build']);src=build/'source';obj=build/'objects';checks=[];commands=[]
    def ck(n,v,**d):
        checks.append({'check':n,'pass':bool(v),**d})
        if not v: raise RuntimeError('Failed check: '+n)
    def blob(path): return subprocess.check_output(['git','-C',str(a.repo),'show',REF+':'+path])
    ck('own_closed87_source_result',s['pass'] and s['reviewer']=='/root/verification' and s['source_commit']==REF and len(s['source_records'])==87)
    ck('honest_source_execution_partition',len(s['commands'])+len(s['reuse_records'])==87 and len({e['module'] for e in s['commands']+s['reuse_records']})==87)
    ck('same_compiler_binary',sha(a.lean.read_bytes())==s['compiler_sha256'])
    objects={e['module']:e for e in s['commands']+s['reuse_records']}
    for r in s['source_records']:
        n=r['module'];f=src/(n.replace('.','/')+'.lean');o=obj/(n.replace('.','/')+'.olean');c=objects[n]
        ck('source_git_object_before:'+n,f.read_bytes()==blob(r['path']) and sha(f.read_bytes())==r['sha256']==c['source_sha256'] and sha(o.read_bytes())==c['object_sha256'] and c.get('exit_code',0)==0)
    manifest=json.loads(blob('lean-statements/lake-manifest.json'))
    def pins():
        result=[]
        for e in manifest['packages']:
            d=a.packages/e['name'];head=subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD'],text=True).strip();status=subprocess.check_output(['git','-C',str(d),'status','--porcelain','--untracked-files=no'],text=True)
            result.append({'name':e['name'],'expected':e['rev'],'actual':head,'tracked_clean':not status,'pass':head==e['rev'] and not status})
        return result
    before=pins();ck('ten_continuous_clean_dependency_pins',before==s['dependency_pins_after'] and len(before)==10 and all(e['pass'] for e in before))
    env=os.environ.copy();env['LEAN_PATH']=s['LEAN_PATH']
    def run(n,b,expected=0,needle=None):
        f=src/(n.replace('.','/')+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b);o=obj/(n.replace('.','/')+'.olean');o.parent.mkdir(parents=True,exist_ok=True)
        saved=a.output/'sources'/(n.replace('.','/')+'.lean.txt');saved.parent.mkdir(parents=True,exist_ok=True);saved.write_bytes(b)
        argv=[str(a.lean),'-R',str(src),'-o',str(o),str(f)];r=subprocess.run(argv,cwd=src,env=env,capture_output=True,text=True,timeout=420);log=r.stdout+r.stderr;(a.output/'logs'/(n+'.log')).write_text(log)
        c={'module':n,'argv':argv,'exit_code':r.returncode,'expected_exit':expected,'source_sha256':sha(b),'object_sha256':sha(o.read_bytes()) if o.exists() else None,'log_sha256':sha(log.encode())};commands.append(c);print(n,r.returncode,flush=True)
        ck('compiler:'+n,r.returncode==expected and (needle is None or needle in log),**c);return log
    guards='''open Lean Elab Command
elab "#review_kind " kind:ident target:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  match ← liftCoreM <| getConstInfo n with
  | .thmInfo _ => unless kind.getId == `thm do throwError "expected definition"
  | .defnInfo _ => unless kind.getId == `defn do throwError "review requires actual theorem"
  | _ => throwError "unexpected declaration kind"
'''
    (a.output/'guards.txt').write_text(guards)
    exports=json.loads(blob(PRE+'EXPORTS.json'))['exports'];(a.output/'FROZEN_EXPORTS.json').write_bytes(blob(PRE+'EXPORTS.json'))
    ck('six_frozen_exports',len(exports)==6 and [e['name'] for e in exports]==['svd_total','query_bound','successful','original_claim','explicit_claim','target'])
    args={'svd_total':'','query_bound':'n m hn ε hε0 hεh','successful':'n m hn F hF A ε hε0 hεh','original_claim':'','explicit_claim':'','target':''}
    consumers='namespace IndependentFull\n'
    for e in exports:
        consumers+='theorem consume_'+e['name']+' '+e['binders']+' :\n    '+e['type']+' := by\n  exact NLA.Proofs.RE06.'+e['name']+' '+args[e['name']]+'\n\n'
    consumers+='''theorem live_reviewed_identity : NLA.Statements.RE06.Target =
    NLA.ReviewedStatements.RE06.Target := rfl
theorem consume_reviewed_target : NLA.ReviewedStatements.RE06.Target := by
  rw [← live_reviewed_identity]
  exact NLA.Proofs.RE06.target
end IndependentFull
'''
    (a.output/'consumers.lean.txt').write_text(consumers)
    own=['IndependentFull.consume_'+e['name'] for e in exports]+['IndependentFull.live_reviewed_identity','IndependentFull.consume_reviewed_target']
    audit='\n'.join('import '+e['module'] for e in s['source_records'])+'\nset_option autoImplicit false\nset_option leancert.trust "kernel"\n'+guards+'\n'+consumers+'\n'
    for d in s['declarations']:
        audit+='#review_kind '+('thm' if d['kind']=='theorem' else 'defn')+' '+d['name']+'\n#assert_trust kernel '+d['name']+'\n#print axioms '+d['name']+'\n'
    for n in own: audit+='#review_kind thm '+n+'\n#assert_trust kernel '+n+'\n#print axioms '+n+'\n'
    log=run('Independent.FullTargetAudit',audit.encode());closures={n:{x.strip() for x in v.split(',') if x.strip()} for n,v in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)}
    for n in re.findall(r"'([^']+)' does not depend on any axioms",log): closures[n]=set()
    expected={d['name'] for d in s['declarations']}|set(own)
    ck('all_actual_kinds_kernel_std3_allowlist',len(expected)==len(s['declarations'])+8 and set(closures)==expected and all(v<=STD for v in closures.values()),closures={n:sorted(v) for n,v in closures.items()})
    for e in exports: ck('actual_public_exact_standard3:'+e['name'],closures['NLA.Proofs.RE06.'+e['name']]==STD)
    for n in own: ck('own_literal_consumer_exact_standard3:'+n,closures[n]==STD)
    for n in ['NLA.Proofs.RE06.GaussianMoment.pseudoinverse_frobeniusSq_integral','NLA.Proofs.RE06.Repair.actual_regression_moment','NLA.Proofs.RE06.stream_rangefinder_tail_moment','NLA.Proofs.RE06.GaussianMoment.actual_excess_majorant_moment']:
        ck('actual_analytic_endpoint_std3:'+n,closures[n]==STD)
    imports='import Independent.FullTargetAudit\nset_option autoImplicit false\nset_option leancert.trust "kernel"\nopen MeasureTheory ProbabilityTheory\nopen NLA.Computation.NonadaptiveMatrixQuery NLA.Proofs.RE06 NLA.Proofs.RE06.Repair\n'
    log=run('Negative.FrozenChallenge',blob(PRE+'Challenge.lean'),1,'sorryAx');ck('all_six_actual_frozen_reference_holes_reject',log.count('depends on sorry or unrecognized axioms')==6)
    for e in exports:
        fixture=imports+'theorem Hole '+e['binders']+' : '+e['type']+' := by sorry\n#assert_trust kernel Hole\n'
        run('Negative.IndividualHole_'+e['name'],fixture.encode(),1,'sorryAx')
    run('Negative.DefinitionKind',(imports+guards+'noncomputable def CounterfeitTarget := @NLA.Proofs.RE06.target\n#assert_trust kernel CounterfeitTarget\n#review_kind thm CounterfeitTarget\n').encode(),1,'review requires actual theorem')
    run('Negative.CustomAxiom',(imports+'axiom TargetOracle : NLA.Statements.RE06.Target\ntheorem TaintedTarget : NLA.Statements.RE06.Target := TargetOracle\n#review_kind thm TaintedTarget\n#assert_trust kernel TaintedTarget\n').replace('#review_kind thm TaintedTarget\n','').encode(),1,'custom: TargetOracle')
    success=next(e for e in exports if e['name']=='successful');query=next(e for e in exports if e['name']=='query_bound')
    fixture=imports+guards+'theorem ConditionalSuccessful '+success['binders']+' (hAnalytic : '+success['type']+') : '+success['type']+' := hAnalytic\n#review_kind thm ConditionalSuccessful\n#assert_trust kernel ConditionalSuccessful\nexample '+success['binders']+' : '+success['type']+' := ConditionalSuccessful '+args['successful']+'\n'
    log=run('Negative.AddedPublicAnalyticPremise',fixture.encode(),1);ck('added_public_premise_rejects_at_literal_consumer','Type mismatch' in log or 'type mismatch' in log)
    fixtures={
      'DroppedInjectivityArgument': 'example '+success['binders']+' : '+success['type']+' := NLA.Proofs.RE06.successful n m hn F A ε hε0 hεh\n',
      'WrongQueryConstant': 'example '+query['binders']+' : '+query['type'].replace('4000000','3999999')+' := NLA.Proofs.RE06.query_bound '+args['query_bound']+'\n',
      'WrongQueryExponent': 'example '+query['binders']+' : '+query['type'][:-1]+'1 := NLA.Proofs.RE06.query_bound '+args['query_bound']+'\n',
      'MissingRectangularInverseGap': '''example (d p : ℕ) :
  (∫ x : Fin d × Fin p → ℝ, Pseudo.frobeniusSq (pseudoInverse (GaussianMoment.entryMatrix x))
    ∂Measure.pi (fun _ : Fin d × Fin p => gaussianReal 0 1)) =
      (d : ℝ) / ((p : ℝ)-(d : ℝ)-1) := GaussianMoment.pseudoinverse_frobeniusSq_integral d p
'''}
    for n,b in fixtures.items():
        log=run('Negative.'+n,(imports+b).encode(),1);ck('intended_signature_dimension_rejection:'+n,'Type mismatch' in log or 'type mismatch' in log)
    after=pins();ck('ten_pins_continuous_after',after==before and all(e['pass'] for e in after))
    for r in s['source_records']:
        n=r['module'];f=src/(n.replace('.','/')+'.lean');o=obj/(n.replace('.','/')+'.olean')
        ck('original_source_object_unchanged:'+n,sha(f.read_bytes())==r['sha256'] and sha(o.read_bytes())==objects[n]['object_sha256'])
    result={'pass':all(c['pass'] for c in checks),'reviewer':'/root/verification','non_author':True,'UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_commit':REF,'source_result_sha256':sha(sb),'scope':'Independent full original RE06 source approval audit only; no canonical package, Linux, or Comparator execution','fresh_source_commands':len(s['commands']),'own_exact_intersection_objects':len(s['reuse_records']),'source_declarations':len(s['declarations']),'source_theorems':sum(d['kind']=='theorem' for d in s['declarations']),'source_definitions':sum(d['kind']=='definition' for d in s['declarations']),'own_consumers':own,'checks':checks,'commands':commands,'dependency_pins_before':before,'dependency_pins_after':after,'private_build':str(build),'script_sha256':sha(Path(__file__).read_bytes()),'guards_sha256':sha(guards.encode()),'consumers_sha256':sha(consumers.encode()),'new_Linux_execution':False,'Comparator_execution':False}
    (a.output/'AUDIT_RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'pass':result['pass'],'audit_checks':len(checks),'audit_commands':len(commands),'actual_declarations':len(s['declarations']),'own_consumers':len(own)}),flush=True)

if __name__=='__main__': main()
