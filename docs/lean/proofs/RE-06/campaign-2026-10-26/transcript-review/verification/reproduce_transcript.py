#!/usr/bin/env python3
"""Independent non-author replay of the immutable RE06 transcript support."""
import argparse, datetime, hashlib, json, os, re, subprocess
from pathlib import Path

REF = 'a271ab2e3ef066187c4c7c26ca10c3f40bcf2ba9'
BASE = '099805ef1ce7347d373e47cccc3b2d7cf580a99e'
PRE = 'docs/lean/proofs/RE-06/campaign-2026-10-26/preproof/'
DOC = 'docs/lean/proofs/RE-06/campaign-2026-10-26/transcript-author/'
STD = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(b): return hashlib.sha256(b).hexdigest()

GUARDS = '''open Lean Elab Command
elab "#review_kind " kind:ident target:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  match ← liftCoreM <| getConstInfo n with
  | .thmInfo _ => unless kind.getId == `thm do throwError "expected definition"
  | .defnInfo _ => unless kind.getId == `defn do throwError "review requires actual theorem"
  | _ => throwError "unexpected declaration kind"
elab "#review_absent " target:ident : command => do
  if (← getEnv).contains target.getId then throwError "unexpected public endpoint"
'''

CONSUMERS = '''open scoped Matrix.Norms.Frobenius
open NLA.Computation.NonadaptiveMatrixQuery
namespace Independent
theorem ExactMinimum {m : ℕ} (score : Fin (m+2) → ℝ) (j : Fin (m+2)) :
    score (minimumIndex score) ≤ score j := NLA.Proofs.RE06.minimumIndex_score_le score j
theorem ExactFullRun {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (ω : ℕ → ℝ) (hP : (makePlan n m ε ω).full = true) :
    frobenius A (run F A ε ω) = optimum A F := NLA.Proofs.RE06.run_full_error F A ε ω hP
theorem ExactFullSuccess {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hfull : n ≤ firstWidth m ε + secondWidth m ε + thirdWidth m ε) :
    Successful F A ε := NLA.Proofs.RE06.successful_full_branch F A ε hε hfull
theorem ExactSketchH {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (P : Plan n)
    (hP : P.full = false) (j : Fin P.ell) :
    storedVector (oracleAnswers A P) (P.s+P.k+j.val) = (fun i => (A.transpose * P.H) i j) :=
  NLA.Proofs.RE06.storedVector_sketchH A P hP j
theorem ExactPostprocess {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Plan n) (hP : P.full = false) :
    postprocess F P (oracleAnswers A P) = minimumIndex (fun b => squaredFrobenius
      (NLA.Proofs.RE06.sketchRepair F A P) (F b)) := NLA.Proofs.RE06.postprocess_sketch F A P hP
theorem ExactFrobeniusNorm {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) ℝ) :
    frobenius X Y = ‖X-Y‖ := NLA.Proofs.RE06.frobenius_eq_norm_sub X Y
theorem ExactNearest {n m : ℕ} (F : Family n m) (A X : Matrix (Fin n) (Fin n) ℝ) :
    frobenius A (F (minimumIndex (fun b => squaredFrobenius X (F b)))) ≤
      optimum A F + 2 * frobenius A X := NLA.Proofs.RE06.nearest_family_error F A X
theorem ExactSketchRun {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (ω : ℕ → ℝ) (hP : (makePlan n m ε ω).full = false) :
    frobenius A (run F A ε ω) ≤ optimum A F +
      2 * frobenius A (NLA.Proofs.RE06.sketchRepair F A (makePlan n m ε ω)) :=
  NLA.Proofs.RE06.run_sketch_error F A ε ω hP
theorem ExactConditionalRepair {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ)
    (ε η : ℝ) (ω : ℕ → ℝ) (hP : (makePlan n m ε ω).full = false)
    (hRepair : frobenius A (NLA.Proofs.RE06.sketchRepair F A (makePlan n m ε ω)) ≤
      (1+2*η) * optimum A F) :
    frobenius A (run F A ε ω) ≤ (3+4*η) * optimum A F :=
  NLA.Proofs.RE06.run_sketch_error_of_repair F A ε η ω hP hRepair
theorem ExactWarmDefinition {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Plan n) : NLA.Proofs.RE06.sketchWarmIndex F A P =
    minimumIndex (fun b => squaredFrobenius (A * P.G0) (F b * P.G0)) := rfl
theorem ExactRepairDefinition {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ)
    (P : Plan n) : NLA.Proofs.RE06.sketchRepair F A P =
    (let b0 := NLA.Proofs.RE06.sketchWarmIndex F A P
     let Y := (A-F b0) * P.G1
     F b0 + Y * pseudoInverse (P.H.transpose * Y) * (P.H.transpose * (A-F b0))) := rfl
theorem ExactFrozenIdentity : NLA.Statements.RE06.Target = NLA.ReviewedStatements.RE06.Target := rfl
end Independent
'''

def main():
    p=argparse.ArgumentParser()
    for key in ['repo','lean','packages','build','output']: p.add_argument('--'+key,type=Path,required=True)
    p.add_argument('--reuse-repo',type=Path)
    a=p.parse_args();a.build.mkdir(parents=True,exist_ok=False);a.output.mkdir(parents=True,exist_ok=True)
    src=a.build/'source';obj=a.build/'objects'
    for d in [src,obj,a.output/'sources',a.output/'logs']:d.mkdir(parents=True,exist_ok=True)
    def git(*v,repo=a.repo):return subprocess.check_output(['git','-C',str(repo),*v])
    def blob(path,ref=REF,repo=a.repo):return git('show',ref+':'+path,repo=repo)
    checks=[];commands=[]
    def ck(n,v,**d):
        checks.append({'check':n,'pass':bool(v),**d})
        if not v:raise RuntimeError('Failed check: '+n)
    fb=blob(DOC+'SOURCE_FREEZE.json');freeze=json.loads(fb);(a.output/'SOURCE_FREEZE.json').write_bytes(fb)
    ck('exact_three_source_freeze',sha(fb)=='eff7205186985ea505618b0e1b23233096f94f2feeb01dca0f31de5194e75029' and len(freeze['proof_files'])==3)
    ck('honest_deterministic_only_scope',freeze['support_theorems']==27 and not freeze['unconditional_public_success_proved'] and not freeze['full_Target_proved'] and not freeze['independent_approval'] and not freeze['Linux_CI'] and not freeze['Comparator'])
    ck('preproof_authorization_ancestor',freeze['authorization_commit']=='bb0dd13e3321bb35af762936a75c2c3a8a8363c6' and subprocess.run(['git','-C',str(a.repo),'merge-base','--is-ancestor',freeze['authorization_commit'],REF]).returncode==0)
    lock=json.loads(blob(PRE+'INPUT_LOCK.json'));ck('same_49_original_lock',sha(blob(PRE+'INPUT_LOCK.json'))=='fda0f85d913233b3c62b707b46bf0edd2fca9ba8ba34a618b57d6bc7bb4e222a' and len(lock['files'])==49)
    for e in lock['files']:
        b=blob(e['path']);ck('original:'+e['path'],b==blob(e['path'],BASE)==blob(PRE+'originals/'+e['path']) and sha(b)==e['sha256'] and len(b)==e['bytes'])
    packet=json.loads(blob(PRE+'PACKET_LOCK.json'));ck('unchanged_preproof_packet_lock',sha(blob(PRE+'PACKET_LOCK.json'))=='f318ade71c4e97a2952052ee94c76ca254e558bc0f9bbc15b72d90a738106bc9')
    for e in packet['files']:
        b=blob(PRE+e['path']);ck('packet:'+e['path'],sha(b)==e['sha256'] and len(b)==e['bytes'])
    registry=json.loads(blob('problem_ids.json'));ck('217_fixed_IDs_and_RE06_Solved',len(registry)==217 and registry['RE-06']=='randomized-and-low-rank-approximation/RE-06/README.md' and b'**Status:** Solved' in blob(registry['RE-06']))
    reuse=json.loads(blob(PRE+'REUSE_LOCK.json'));reuse_repo=a.reuse_repo or Path(reuse['source_repository_read_only'])
    for e in reuse['files']:
        b=blob(e['path'],reuse['source_commit'],repo=reuse_repo);ck('retained_reuse:'+e['path'],b==blob(PRE+'supplementary-reuse/'+e['path']) and sha(b)==e['sha256'] and len(b)==e['bytes'])
    for e in freeze['proof_files']:
        b=blob(e['path']);ck('frozen_source:'+e['path'],sha(b)==e['sha256'] and len(b)==e['bytes'])
    modules={};order=[];records=[];decls=[]
    def visit(n):
        if n in modules:return
        path='lean-statements/'+n.replace('.','/')+'.lean';b=blob(path)
        for child in re.findall(r'^import\s+([\w.]+)\s*$',b.decode(),re.M):
            if child.startswith(('NLA.','Reviewed.')):visit(child)
        modules[n]=b;order.append(n);records.append({'module':n,'path':path,'sha256':sha(b),'bytes':len(b)})
    for e in freeze['proof_files']:visit(e['path'][len('lean-statements/'):-5].replace('/','.'))
    ck('eight_source_closure_only',len(modules)==8 and {n for n in modules if '.Proofs.' in n}=={'NLA.Proofs.RE06.Transcript','NLA.Proofs.RE06.Frobenius','NLA.Proofs.RE06.TranscriptAudit'})
    for n,b in modules.items():
        if '.Proofs.' not in n:continue
        code=re.sub(r'/\-.*?\-/','',b.decode(),flags=re.S);code=re.sub(r'--[^\n]*','',code)
        ck('kernel_source_without_holes_or_bypass:'+n,'set_option leancert.trust "kernel"' in code and not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b|skipKernelTC',code))
        spaces=[]
        for raw in code.splitlines():
            line=raw.strip();ns=re.fullmatch(r'namespace\s+([\w.]+)',line)
            if ns:spaces.append(ns[1]);continue
            if re.fullmatch(r'end(?:\s+\S+)?',line):
                if spaces:spaces.pop()
                continue
            d=re.match(r'^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+([^\s({:]+)',line)
            if d:decls.append({'name':'.'.join(spaces+[d[2]]),'kind':'theorem' if d[1] in ['theorem','lemma'] else 'definition','module':n})
    ck('27_actual_support_headers_and_two_helpers',set('NLA.Proofs.RE06.'+n for n in freeze['theorems'])=={d['name'] for d in decls if d['kind']=='theorem' and d['module']!='NLA.Proofs.RE06.TranscriptAudit'} and set(freeze['conservative_helper_definitions'])=={d['name'] for d in decls if d['kind']=='definition'})
    manifest=json.loads(blob('lean-statements/lake-manifest.json'))
    def pins():
        out=[]
        for e in manifest['packages']:
            d=a.packages/e['name'];head=git('rev-parse','HEAD',repo=d).decode().strip();status=git('status','--porcelain','--untracked-files=no',repo=d).decode();out.append({'name':e['name'],'expected':e['rev'],'actual':head,'tracked_clean':not status,'pass':head==e['rev'] and not status})
        return out
    before=pins();ck('ten_clean_pinned_dependencies_before',len(before)==10 and all(e['pass'] for e in before))
    version=subprocess.check_output([str(a.lean),'--version'],text=True).strip();ck('pinned_Lean4331',blob('lean-statements/lean-toolchain')==b'leanprover/lean4:v4.33.1\n' and '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version)
    env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[obj]+[a.packages/e['name']/'.lake/build/lib/lean' for e in manifest['packages']]+[a.lean.parent.parent/'lib/lean']))
    def run(n,b,expected=0,needle=None):
        f=src/(n.replace('.','/')+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b)
        cpy=a.output/'sources'/(n.replace('.','/')+'.lean.txt');cpy.parent.mkdir(parents=True,exist_ok=True);cpy.write_bytes(b)
        o=obj/(n.replace('.','/')+'.olean');o.parent.mkdir(parents=True,exist_ok=True);argv=[str(a.lean),'-R',str(src),'-o',str(o),str(f)]
        result=subprocess.run(argv,cwd=src,env=env,capture_output=True,text=True,timeout=420);log=result.stdout+result.stderr;(a.output/'logs'/(n+'.log')).write_text(log)
        c={'module':n,'argv':argv,'exit_code':result.returncode,'expected_exit':expected,'source_sha256':sha(b),'object_sha256':sha(o.read_bytes()) if o.exists() else None,'log_sha256':sha(log.encode())};commands.append(c);print(n,result.returncode,flush=True)
        ck('compiler:'+n,result.returncode==expected and (needle is None or needle in log),**c);return log
    for n in order:run(n,modules[n])
    audit='\n'.join('import '+n for n in order)+'\nset_option leancert.trust "kernel"\n'+GUARDS
    for d in decls:audit+='#review_kind '+('thm' if d['kind']=='theorem' else 'defn')+' '+d['name']+'\n#assert_trust kernel '+d['name']+'\n#print axioms '+d['name']+'\n'
    audit+=CONSUMERS
    consumers=re.findall(r'^theorem (\w+)',CONSUMERS,re.M)
    for n in consumers:audit+='#review_kind thm Independent.'+n+'\n#assert_trust kernel Independent.'+n+'\n#print axioms Independent.'+n+'\n'
    for n in ['svd_total','query_bound','successful','original_claim','explicit_claim','target']:audit+='#review_absent NLA.Proofs.RE06.'+n+'\n'
    log=run('Independent.Audit',audit.encode());closures={n:{x.strip() for x in v.split(',') if x.strip()} for n,v in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)}
    for n in re.findall(r"'([^']+)' does not depend on any axioms",log):closures[n]=set()
    expected={d['name'] for d in decls}|{'Independent.'+n for n in consumers}
    ck('all_actual_kinds_kernel_and_std3_only',set(closures)==expected and all(v<=STD for v in closures.values()),closures={n:sorted(v) for n,v in closures.items()})
    for n in ['successful_full_branch','postprocess_sketch','run_sketch_error_of_repair']:ck('actual_exact_std3:'+n,closures['NLA.Proofs.RE06.'+n]==STD)
    imports='import NLA.Proofs.RE06.TranscriptAudit\nset_option leancert.trust "kernel"\nopen NLA.Computation.NonadaptiveMatrixQuery\n'
    full_head='''{n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hfull : n ≤ firstWidth m ε + secondWidth m ε + thirdWidth m ε) : Successful F A ε'''
    run('Negative.FullBranchHole',(imports+'theorem ExactFullBranchHole '+full_head+' := by sorry\n#assert_trust kernel ExactFullBranchHole\n').encode(),1,'sorryAx')
    log=run('Negative.FrozenChallenge',blob(PRE+'Challenge.lean'),1,'sorryAx');ck('six_reference_holes_rejected',log.count('depends on sorry or unrecognized axioms')==6)
    run('Negative.DefinitionKind',(imports+GUARDS+'noncomputable def CounterfeitNearest := @NLA.Proofs.RE06.nearest_family_error\n#review_kind thm CounterfeitNearest\n').encode(),1,'review requires actual theorem')
    run('Negative.CustomAxiom',(imports+'axiom TranscriptOracle '+full_head+'\ntheorem TaintedFull '+full_head+' := TranscriptOracle F A ε hε hfull\n#assert_trust kernel TaintedFull\n').encode(),1,'custom: TranscriptOracle')
    wrong_offset='''example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (P : Plan n) (hP : P.full = false)
    (j : Fin P.ell) : storedVector (oracleAnswers A P) (P.s+j.val) =
      (fun i => (A.transpose * P.H) i j) := NLA.Proofs.RE06.storedVector_sketchH A P hP j
'''
    log=run('Negative.WrongOffset',(imports+wrong_offset).encode(),1);ck('changed_actual_H_offset_type_mismatch','Type mismatch' in log or 'type mismatch' in log)
    missing_premise='''example {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ)
    (ε η : ℝ) (ω : ℕ → ℝ) (hP : (makePlan n m ε ω).full = false) :
    frobenius A (run F A ε ω) ≤ (3+4*η) * optimum A F :=
  NLA.Proofs.RE06.run_sketch_error_of_repair F A ε η ω hP
'''
    log=run('Negative.MissingRepairPremise',(imports+missing_premise).encode(),1);ck('conditional_premise_cannot_be_dropped','Type mismatch' in log or 'type mismatch' in log)
    after=pins();ck('ten_dependency_pins_unchanged_after',before==after and all(e['pass'] for e in after));ck('all_eight_private_sources_unchanged',all((src/(n.replace('.','/')+'.lean')).read_bytes()==b for n,b in modules.items()))
    result={'pass':all(e['pass'] for e in checks),'reviewer':'/root/verification','non_author':True,'UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_commit':REF,'scope':'Only 27 deterministic Transcript/Frobenius support theorems and two conservative helpers; no public endpoint, full Target or CI approval','checks':checks,'commands':commands,'source_records':records,'declarations':decls,'own_consumers':consumers,'compiler_version':version,'compiler_sha256':sha(a.lean.read_bytes()),'dependency_pins_before':before,'dependency_pins_after':after,'private_build':str(a.build),'LEAN_PATH':env['LEAN_PATH'],'script_sha256':sha(Path(__file__).read_bytes()),'new_Linux_execution':False,'Comparator_execution':False}
    (a.output/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'pass':result['pass'],'checks':len(checks),'commands':len(commands),'source_declarations':len(decls),'own_consumers':len(consumers)}),flush=True)

if __name__=='__main__':main()
