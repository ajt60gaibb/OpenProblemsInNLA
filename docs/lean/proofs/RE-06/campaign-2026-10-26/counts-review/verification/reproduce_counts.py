#!/usr/bin/env python3
"""Non-author immutable RE06 two-export source review; fresh own12-source closure."""
import argparse,datetime,hashlib,json,os,re,subprocess
from pathlib import Path
REF='b48de1c1510ec2677ce8300d015e00cdc202065d';BASE='099805ef1ce7347d373e47cccc3b2d7cf580a99e';PRE='docs/lean/proofs/RE-06/campaign-2026-10-26/preproof/';DOC='docs/lean/proofs/RE-06/campaign-2026-10-26/counts-author/';STD={'propext','Classical.choice','Quot.sound'}
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--lean',type=Path,required=True);p.add_argument('--packages',type=Path,required=True);p.add_argument('--build',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();a.build.mkdir(parents=True,exist_ok=False);a.output.mkdir(parents=True,exist_ok=True);src=a.build/'source';obj=a.build/'objects'
 for d in [src,obj,a.output/'sources',a.output/'logs']:d.mkdir(parents=True,exist_ok=True)
 def git(*v,repo=a.repo):return subprocess.check_output(['git','-C',str(repo),*v])
 def blob(path,ref=REF,repo=a.repo):return git('show',ref+':'+path,repo=repo)
 checks=[];commands=[]
 def ck(n,v,**d):
  checks.append({'check':n,'pass':bool(v),**d})
  if not v:raise RuntimeError('Failed check: '+n)
 frozenbytes=blob(DOC+'SOURCE_FREEZE.json');freeze=json.loads(frozenbytes);(a.output/'SOURCE_FREEZE.json').write_bytes(frozenbytes)
 ck('honest_two_export_scope',freeze['public_exports_completed']==['NLA.Proofs.RE06.svd_total','NLA.Proofs.RE06.query_bound'] and freeze['public_exports_remaining']==['NLA.Proofs.RE06.successful','NLA.Proofs.RE06.original_claim','NLA.Proofs.RE06.explicit_claim','NLA.Proofs.RE06.target'] and freeze['whole_problem_verified'] is False and freeze['canonical_status']=='Solved')
 ck('two_review_authorization_precedes_proof',subprocess.run(['git','-C',str(a.repo),'merge-base','--is-ancestor',freeze['authorization_commit'],REF]).returncode==0 and freeze['authorization_commit']=='bb0dd13e3321bb35af762936a75c2c3a8a8363c6')
 lock=json.loads(blob(PRE+'INPUT_LOCK.json'));ck('same_49_original_lock',sha(blob(PRE+'INPUT_LOCK.json'))=='fda0f85d913233b3c62b707b46bf0edd2fca9ba8ba34a618b57d6bc7bb4e222a' and len(lock['files'])==49)
 for e in lock['files']:
  b=blob(e['path']);ck('original:'+e['path'],b==blob(e['path'],BASE)==blob(PRE+'originals/'+e['path']) and sha(b)==e['sha256'] and len(b)==e['bytes'])
 packet=json.loads(blob(PRE+'PACKET_LOCK.json'));ck('same_exact_preapproved_packet_lock',sha(blob(PRE+'PACKET_LOCK.json'))=='f318ade71c4e97a2952052ee94c76ca254e558bc0f9bbc15b72d90a738106bc9')
 for e in packet['files']:ck('preproof_packet:'+e['path'],sha(blob(PRE+e['path']))==e['sha256'] and len(blob(PRE+e['path']))==e['bytes'])
 registry=json.loads(blob('problem_ids.json'));ck('217_fixed_IDs_and_Solved_canonical_RE06',len(registry)==217 and registry['RE-06']=='randomized-and-low-rank-approximation/RE-06/README.md' and b'**Status:** Solved' in blob(registry['RE-06']))
 reuse=json.loads(blob(PRE+'REUSE_LOCK.json'));reuse_repo=Path(reuse['source_repository_read_only'])
 for e in reuse['files']:
  b=blob(e['path'],reuse['source_commit'],repo=reuse_repo);ck('reuse_snapshot:'+e['path'],b==blob(PRE+'supplementary-reuse/'+e['path']) and sha(b)==e['sha256'] and len(b)==e['bytes'])
 for e in freeze['files']:ck('seven_source_freeze:'+e['path'],sha(blob(e['path']))==e['sha256'] and len(blob(e['path']))==e['bytes'])
 ck('two_TR04_reuse_source_bytes_exact',all(blob(e['path'])==blob(e['path'],reuse['source_commit'],repo=reuse_repo) for e in freeze['files'] if e['role']=='byte-exact reviewed reuse'))
 ck('exact_five_frozen_RE06_module_set',set(git('ls-tree','-r','--name-only',REF,'--','lean-statements/NLA/Proofs/RE06').decode().splitlines())=={e['path'] for e in freeze['files'] if '/RE06/' in e['path']})
 modules={};order=[];records=[];decls=[]
 def visit(n):
  if n in modules:return
  path='lean-statements/'+n.replace('.','/')+'.lean';b=blob(path)
  for child in re.findall(r'^import\s+([\w.]+)\s*$',b.decode(),re.M):
   if child.startswith(('NLA.','Reviewed.')):visit(child)
  modules[n]=b;order.append(n);records.append({'module':n,'path':path,'sha256':sha(b),'bytes':len(b)})
 for e in freeze['files']:visit(e['path'][len('lean-statements/'):-5].replace('/','.'))
 visit('NLA.Statements.RE06');visit('Reviewed.RE06');ck('fresh12_project_sources',len(modules)==12)
 for n,b in modules.items():
  if '.Proofs.' not in n:continue
  code=re.sub(r'/\-.*?\-/','',b.decode(),flags=re.S);code=re.sub(r'--[^\n]*','',code)
  ck('kernel_mode_no_holes_or_bypass:'+n,'set_option leancert.trust "kernel"' in b.decode() and not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b|skipKernelTC',code))
  spaces=[]
  for line in code.splitlines():
   ns=re.match(r'^namespace\s+([\w.]+)\s*$',line)
   if ns:spaces.append(ns[1]);continue
   if re.match(r'^end(?:\s+\S+)?\s*$',line):
    if spaces:spaces.pop()
    continue
   d=re.match(r'^(?:@\[[^\n]*\]\s*)?(theorem|lemma|def|abbrev)\s+([^\s({:]+)',line)
   if d:decls.append({'name':'.'.join(spaces+[d[2]]),'kind':'theorem' if d[1] in ['theorem','lemma'] else 'definition','module':n})
 manifest=json.loads(blob('lean-statements/lake-manifest.json'))
 def pins():
  out=[]
  for e in manifest['packages']:
   d=a.packages/e['name'];head=git('rev-parse','HEAD',repo=d).decode().strip();status=git('status','--porcelain','--untracked-files=no',repo=d).decode();out.append({'name':e['name'],'expected':e['rev'],'actual':head,'tracked_clean':not status,'pass':head==e['rev'] and not status})
  return out
 before=pins();ck('ten_clean_pinned_dependencies_before',len(before)==10 and all(e['pass'] for e in before));version=subprocess.check_output([str(a.lean),'--version'],text=True).strip();ck('pinned_Lean4331',blob('lean-statements/lean-toolchain')==b'leanprover/lean4:v4.33.1\n' and '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version)
 env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[obj]+[a.packages/e['name']/'.lake/build/lib/lean' for e in manifest['packages']]+[a.lean.parent.parent/'lib/lean']))
 def run(n,b,expected=0,needle=None):
  f=src/(n.replace('.','/')+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b);copy=a.output/'sources'/(n.replace('.','/')+'.lean.txt');copy.parent.mkdir(parents=True,exist_ok=True);copy.write_bytes(b);o=obj/(n.replace('.','/')+'.olean');o.parent.mkdir(parents=True,exist_ok=True);argv=[str(a.lean),'-R',str(src),'-o',str(o),str(f)];r=subprocess.run(argv,cwd=src,env=env,capture_output=True,text=True,timeout=420);log=r.stdout+r.stderr;(a.output/'logs'/(n+'.log')).write_text(log);c={'module':n,'argv':argv,'exit_code':r.returncode,'expected_exit':expected,'source_sha256':sha(b),'object_sha256':sha(o.read_bytes()) if o.exists() else None,'log_sha256':sha(log.encode())};commands.append(c);print(n,r.returncode,flush=True);ck('compiler:'+n,r.returncode==expected and (needle is None or needle in log),**c);return log
 for n in order:run(n,modules[n])
 guards='''open Lean Elab Command
elab "#review_kind " kind:ident target:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  match ← liftCoreM <| getConstInfo n with
  | .thmInfo _ => unless kind.getId == `thm do throwError "expected definition"
  | .defnInfo _ => unless kind.getId == `defn do throwError "review requires actual theorem"
  | _ => throwError "unexpected declaration kind"
elab "#review_absent " target:ident : command => do
  if (← getEnv).contains target.getId then throwError "unexpected full scope declaration"
'''
 audit='\n'.join('import '+n for n in order)+'\nset_option leancert.trust "kernel"\n'+guards
 audit+='\n'.join('#review_kind '+('thm' if d['kind']=='theorem' else 'defn')+' '+d['name']+'\n#assert_trust kernel '+d['name']+'\n#print axioms '+d['name'] for d in decls)+'\n'
 exports=json.loads(blob(PRE+'EXPORTS.json'))['exports'];chosen=[e for e in exports if e['name'] in ['svd_total','query_bound']]
 for e in chosen:
  args='' if e['name']=='svd_total' else ' n m hn ε hε0 hεh';name='IndependentExact_'+e['name'];audit+='theorem '+name+' '+e['binders']+' : '+e['type']+' := NLA.Proofs.RE06.'+e['name']+args+'\n#review_kind thm '+name+'\n#assert_trust kernel '+name+'\n#print axioms '+name+'\n'
 audit+='theorem IndependentFrozenIdentity : NLA.Statements.RE06.Target = NLA.ReviewedStatements.RE06.Target := rfl\n#review_kind thm IndependentFrozenIdentity\n#assert_trust kernel IndependentFrozenIdentity\n#print axioms IndependentFrozenIdentity\n'
 for n in ['successful','original_claim','explicit_claim','target']:audit+='#review_absent NLA.Proofs.RE06.'+n+'\n'
 # Runtime cases test actual finite planning at zero/positive dimensions and zero stream, not success assumptions.
 audit+='''open NLA.Computation.NonadaptiveMatrixQuery
example (n m : ℕ) (ε : ℝ) (ω : ℕ → ℝ) :
    (queryList (makePlan n m ε ω)).length = min n (firstWidth m ε+secondWidth m ε+thirdWidth m ε) := NLA.Proofs.RE06.Counts.makePlan_query_count n m ε ω
example (m : ℕ) (ε : ℝ) : (queryList (makePlan 0 m ε (fun _ => 0))).length = 0 := by rw [NLA.Proofs.RE06.Counts.makePlan_query_count]; simp
example : logWidth 0 = 2 := by decide
example : rootWidth 0 = 2 := by
  have hL : logWidth 0 = 2 := by decide
  simp [rootWidth, hL, Nat.sqrt_two]
'''
 log=run('Independent.Audit',audit.encode());closures={n:{x.strip() for x in v.split(',') if x.strip()} for n,v in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)}
 for n in re.findall(r"'([^']+)' does not depend on any axioms",log):closures[n]=set()
 expected={d['name'] for d in decls}|{'IndependentExact_svd_total','IndependentExact_query_bound','IndependentFrozenIdentity'};ck('all_actual_kinds_kernel_and_standard_axioms',set(closures)==expected and all(v<=STD for v in closures.values()),closures={n:sorted(v) for n,v in closures.items()});ck('two_actual_exports_exact_std3',all(closures['NLA.Proofs.RE06.'+e['name']]==STD for e in chosen));ck('13_count_supports_present',sum(d['kind']=='theorem' and d['name'].startswith('NLA.Proofs.RE06.Counts.') for d in decls)==13)
 challenge=blob(PRE+'Challenge.lean');log=run('Negative.FullChallenge',challenge,1,'sorryAx');ck('six_original_reference_holes_reject',log.count('depends on sorry or unrecognized axioms')==6)
 for e in chosen:
  b=('import NLA.Statements.RE06\nset_option leancert.trust "kernel"\nnamespace NLA.Proofs.RE06\ntheorem '+e['name']+' '+e['binders']+' : '+e['type']+' := by sorry\n#assert_trust kernel '+e['name']+'\nend NLA.Proofs.RE06\n').encode();run('Negative.Hole_'+e['name'],b,1,'sorryAx')
 fake='import NLA.Proofs.RE06.CountAudit\n'+guards+'def CounterfeitSVD : NLA.Computation.NonadaptiveMatrixQuery.SVDTotal := NLA.Proofs.RE06.svd_total\n#review_kind thm CounterfeitSVD\n';run('Negative.DefinitionKind',fake.encode(),1,'review requires actual theorem')
 taint='import NLA.Statements.RE06\nset_option leancert.trust "kernel"\naxiom CountOracle : NLA.Computation.NonadaptiveMatrixQuery.SVDTotal\ntheorem TaintedSVD : NLA.Computation.NonadaptiveMatrixQuery.SVDTotal := CountOracle\n#assert_trust kernel TaintedSVD\n';run('Negative.CustomAxiom',taint.encode(),1,'CountOracle')
 e=next(e for e in chosen if e['name']=='query_bound')
 for n,typ in [('WrongCoefficient',e['type'].replace('4000000','3999999')),('WrongExponent',e['type'].replace('4000000 0','4000000 1'))]:
  b=('import NLA.Proofs.RE06.QueryBound\nexample '+e['binders']+' : '+typ+' := NLA.Proofs.RE06.query_bound n m hn ε hε0 hεh\n').encode();log=run('Negative.'+n,b,1);ck('exact_type_change_rejected:'+n,'Type mismatch' in log or 'type mismatch' in log)
 after=pins();ck('ten_pins_unchanged_after',before==after and all(e['pass'] for e in after));ck('all12_private_sources_unchanged',all((src/(n.replace('.','/')+'.lean')).read_bytes()==b for n,b in modules.items()))
 report={'pass':all(e['pass'] for e in checks),'reviewer':'/root/verification','UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_commit':REF,'scope':'Only literal svd_total/query_bound and13 count supports; no successful/original/explicit/fullTarget or CI claim','source_modules':12,'new_RE06_sources':5,'byte_exact_TR04_reuse_sources':2,'checks':checks,'commands':commands,'declarations':decls,'source_records':records,'compiler_version':version,'compiler_sha256':sha(a.lean.read_bytes()),'dependency_pins_before':before,'dependency_pins_after':after,'private_build':str(a.build),'LEAN_PATH':env['LEAN_PATH'],'script_sha256':sha(Path(__file__).read_bytes()),'new_Linux_execution':False};(a.output/'result.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'pass':report['pass'],'checks':len(checks),'commands':len(commands),'declarations':len(decls)}),flush=True)
if __name__=='__main__':main()
