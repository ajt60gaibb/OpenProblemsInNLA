#!/usr/bin/env python3
"""Independent immutable canonical isotropic-only package replay and Comparator library run."""
import argparse,datetime,hashlib,json,os,re,subprocess
from pathlib import Path
REF='6c607ab14af2b8b2b8075f0b3f1798e037c10899'; PROOF='4692336f0e1a50d5e261bba68277875da30fba51'; BASE='5487945e5a72abd952b0c89915915de8cc9b3e65'; PREFIX='tensor-computations/TR-26/lean/'
STANDARD={'propext','Classical.choice','Quot.sound'}
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--lean',type=Path,required=True);p.add_argument('--packages',type=Path,required=True);p.add_argument('--build',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--resume-first-replay',type=Path);p.add_argument('--resume-auxiliary',type=Path);a=p.parse_args()
 a.output.mkdir(parents=True,exist_ok=True);a.build.mkdir(parents=True,exist_ok=a.resume_first_replay is not None)
 src=a.build/'source';obj=a.build/'objects';toolsrc=a.build/'tool-source';toolobj=a.build/'tool-objects'
 for d in [src,obj,toolsrc,toolobj,a.output/'logs',a.output/'consumers',a.output/'tool-sources']:d.mkdir(parents=True,exist_ok=True)
 def git(*args):return subprocess.check_output(['git','-C',str(a.repo),*args])
 def blob(path,ref=REF):return git('show',ref+':'+path)
 checks=[];commands=[]
 def ck(name,value,**extra):
  checks.append({'check':name,'pass':bool(value),**extra})
  if not value:raise RuntimeError('Failed check: '+name)
 tree=git('ls-tree','-r',REF,'--',PREFIX).decode().splitlines();files={}
 for line in tree:
  mode,kind,rest=line.split(' ',2);oid,path=rest.split('\t');rel=path[len(PREFIX):]
  ck('plain_file:'+rel,mode=='100644' and kind=='blob' and not Path(rel).is_absolute() and '..' not in Path(rel).parts)
  b=blob(path);files[rel]=b;f=src/rel;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b)
 lock=json.loads(files['PACKAGE_LOCK.json']);ck('complete353_lock_plus_self',len(files)==354 and len(lock['files'])==353 and set(files)==set(lock['files'])|{'PACKAGE_LOCK.json'})
 for name,e in lock['files'].items():ck('lock:'+name,sha(files[name])==e['sha256'] and len(files[name])==e['bytes'])
 mapping=json.loads(files['SOURCE_MAP.json']);ck('117_provenance_copies',len(mapping['copies'])==117)
 for e in mapping['copies']:
  b=blob(e['source_path'],e['source_ref']);ck('source_copy:'+e['path'],b==files[e['path']] and sha(b)==e['sha256'] and len(b)==e['bytes'])
 shared=[e for e in mapping['copies'] if e['path'].startswith(('NLA/','Reviewed/')) and e['path'].endswith('.lean')]
 ck('36_exact_shared_runtime_copies',len(shared)==36 and all(e['source_ref']==PROOF for e in shared))
 bindings=json.loads(files['reviews/SOURCE_REVIEW_BINDINGS.json']);ck('221_retained_review_files',len(bindings['files'])==221)
 for e in bindings['files']:ck('review_binding:'+e['path'],sha(files[e['path']])==e['sha256'] and len(files[e['path']])==e['bytes'])
 old=a.repo/'reviews/2026-10-23-solved-lean/tr26-isotropic-review/verification'
 for name in ['REVIEW.md','result.json','APPROVAL.json']:
  ck('verbatim_independent_review:'+name,files['reviews/isotropic/verification/'+name]==(old/name).read_bytes())
 packet='docs/lean/proofs/TR-26/campaign-2026-10-26/preproof/'
 pre=json.loads(blob(packet+'INPUT_LOCK.json'));ck('24_originals',len(pre['reviewed_inputs'])==24)
 for e in pre['reviewed_inputs']:
  b=blob(e['path']);ck('original:'+e['path'],b==blob(e['path'],BASE)==blob(packet+'frozen/'+e['path']) and sha(b)==e['sha256'] and len(b)==e['bytes'])
 ck('canonical_readme_and_registry_unchanged',blob('tensor-computations/TR-26/README.md')==blob('tensor-computations/TR-26/README.md',PROOF) and blob('problem_ids.json')==blob('problem_ids.json',PROOF))
 head_delta=git('diff','--name-only',REF,'04045bad').decode().splitlines();ck('04045bad_only_external_inventory_delta',head_delta==['docs/lean/statements/inventory.json'])
 config=json.loads(files['comparator.json']);ck('single_exact_comparator_export',config['theorem_names']==['NLA.Proofs.TR26.isotropic_degree'] and config['definition_names']==[] and set(config['permitted_axioms'])==STANDARD and config['challenge_module']=='Challenge' and config['solution_module']=='Solution')
 meta=json.loads(files['formalization.yaml']);ck('partial_metadata_scope',meta['status']['whole_problem_verified'] is False and meta['status']['canonical_status']=='Solved')
 runtime={n[:-5].replace('/','.'):b for n,b in files.items() if n.endswith('.lean') and not n.startswith('reviews/')}
 ck('40_runtime_sources_and36_archived_snapshots',len(runtime)==40 and sum(n.endswith('.lean') for n in files)==76)
 order=[];seen=set();external=set()
 def visit(n):
  if n in seen:return
  seen.add(n)
  for child in re.findall(r'^import\s+([\w.]+)\s*$',runtime[n].decode(),re.M):
   if child in runtime:visit(child)
   else:external.add(child)
  order.append(n)
 for n in sorted(runtime):visit(n)
 ck('runtime_imports_confined_to_package_or_pinned_dependencies',all(n.startswith(('Mathlib','LeanCert','Lean')) for n in external))
 manifest=json.loads(files['lake-manifest.json'])
 def pins():
  out=[]
  for e in manifest['packages']:
   d=a.packages/e['name'];head=gitdep(d,'rev-parse','HEAD').strip();status=gitdep(d,'status','--porcelain','--untracked-files=no');out.append({'name':e['name'],'expected':e['rev'],'actual':head,'tracked_clean':not status,'pass':head==e['rev'] and not status})
  return out
 def gitdep(path,*args):return subprocess.check_output(['git','-C',str(path),*args],text=True)
 before=pins();ck('10_pinned_clean_dependencies_before',len(before)==10 and all(e['pass'] for e in before))
 version=subprocess.check_output([str(a.lean),'--version'],text=True).strip();ck('pinned_Lean4_33_1',files['lean-toolchain']==b'leanprover/lean4:v4.33.1\n' and '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version)
 deps=[a.packages/e['name']/'.lake/build/lib/lean' for e in manifest['packages']];env=os.environ.copy();env['PATH']=str(a.lean.parent)+os.pathsep+env.get('PATH','');env['LEAN_PATH']=':'.join(map(str,[obj]+deps+[a.lean.parent.parent/'lib/lean']))
 cached_aux={e['module']:e for e in json.loads(a.resume_auxiliary.read_bytes())['commands']} if a.resume_auxiliary else {}
 def run(n,b,root=src,objects=obj,expected=0,needle=None,run_main=False):
  f=root/(n.replace('.','/')+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b);dest=objects/(n.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
  argv=[str(a.lean),'--run',str(f)] if run_main else [str(a.lean),'-R',str(root),'-o',str(dest),str(f)]
  if n in cached_aux:
   old=cached_aux[n];log=(a.output/old['log']).read_text();ck('retained_actual_auxiliary:'+n,old['source_sha256']==sha(b) and old['log_sha256']==sha(log.encode()) and old['argv']==argv and old['exit_code']==expected and (needle is None or needle in log) and (old['object_sha256'] is None or old['object_sha256']==sha(dest.read_bytes())));commands.append(old);return log
  r=subprocess.run(argv,cwd=root,env=env,capture_output=True,text=True,timeout=420);log=r.stdout+r.stderr;lf=a.output/'logs'/(n+'.log');lf.write_text(log)
  c={'module':n,'argv':argv,'exit_code':r.returncode,'expected_exit':expected,'source_sha256':sha(b),'log_sha256':sha(log.encode()),'log':str(lf.relative_to(a.output))};commands.append(c);print(n,r.returncode,flush=True)
  ck('compiler:'+n,r.returncode==expected and (needle is None or needle in log),**c)
  return log
 if a.resume_first_replay:
  prior=json.loads(a.resume_first_replay.read_bytes());ck('exact_first40_own_source_replay',prior['package_commit']==REF and prior['compiler_sha256']==sha(a.lean.read_bytes()) and prior['private_build']==str(a.build) and {e['module'] for e in prior['commands']}==set(runtime))
  for e in prior['commands']:
   n=e['module'];o=obj/(n.replace('.','/')+'.olean');ck('own_source_replay_retained:'+n,e['exit_code']==0 and e['source_sha256']==sha(runtime[n]) and e['object_sha256']==sha(o.read_bytes()) and e['log_sha256']==sha((a.output/e['log']).read_bytes()));commands.append(e)
 else:
  for n in order:run(n,runtime[n])
 decls=json.loads(files['reviews/isotropic/verification/result.json'])['declarations']
 audit='import EndpointAudit\n'+files['EndpointAudit.lean'].decode().split('open Lean',1)[0].split('set_option',1)[0].replace('import Solution','').replace('import Reviewed.TR26','')+'\nset_option leancert.trust "kernel"\n'
 # EndpointAudit already checks exact type, actual selected theorem kind, absence and frozen Target identity.
 audit='import EndpointAudit\n'+'\n'.join('import '+n for n in order if n.startswith('NLA.Proofs.'))+'\nset_option leancert.trust "kernel"\n'
 audit+='''open Lean Elab Command
elab "#review_kind " kind:ident target:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  match ← liftCoreM <| getConstInfo n with
  | .thmInfo _ => unless kind.getId == `theorem do throwError "expected definition"
  | .defnInfo _ => unless kind.getId == `definition do throwError "expected theorem"
  | _ => throwError "unexpected declaration kind"
'''
 audit+='\n'.join('#review_kind '+('«theorem»' if d['kind']=='theorem' else 'definition')+' '+d['name']+'\n#assert_trust kernel '+d['name']+'\n#print axioms '+d['name'] for d in decls)+'\n'
 log=run('IndependentAllDeclarations',audit.encode());closures={}
 for n,v in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S):closures[n]=[x.strip() for x in v.split(',') if x.strip()]
 for n in re.findall(r"'([^']+)' does not depend on any axioms",log):closures[n]=[]
 ck('288_actual_declaration_kinds_kernel_and_standard_axioms',len(decls)==288 and set(closures)=={d['name'] for d in decls} and all(set(v)<=STANDARD for v in closures.values()),closures=closures)
 endpoint='NLA.Proofs.TR26.isotropic_degree';ck('endpoint_exact_std3',set(closures[endpoint])==STANDARD)
 (a.output/'consumers'/'IndependentAllDeclarations.lean.txt').write_text(audit)
 controls=[('ChallengeTrustRejection','sorryAx'),('DefinitionKindRejection','requires an actual theorem'),('CustomAxiomRejection','PackageOracle')]
 for n,needle in controls:run(n,files['controls/'+n+'.lean.txt'],root=a.build/'controls',expected=1,needle=needle)
 tool_lock_bytes=blob('tools/lean/source-lock.json');tool_lock=json.loads(tool_lock_bytes);(a.output/'source-lock.json').write_bytes(tool_lock_bytes)
 tool_records=[];archive='eigenvalues-and-inverse-problems/IS-03/lean/verification/linux-2026-09-12/source/forsythe/'
 for n,destination in [('Export.Parse','.tools/lean4export/Export/Parse.lean'),('Comparator.Util','.tools/comparator/Comparator/Util.lean'),('Comparator.Axioms','.tools/comparator/Comparator/Axioms.lean'),('Comparator.Compare','.tools/comparator/Comparator/Compare.lean')]:
  e=next(e for e in tool_lock['files'] if e['destination']==destination);b=blob(archive+destination);ck('pinned_tool:'+n,sha(b)==e['sha256'] and len(b)==e['bytes']);f=a.output/'tool-sources'/(n.replace('.','/')+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b);tool_records.append({'module':n,**e});env['LEAN_PATH']=':'.join(map(str,[toolobj,obj]+deps+[a.lean.parent.parent/'lib/lean']));run(n,b,root=toolsrc,objects=toolobj)
 runner='''import Lean
import Comparator.Compare
open Lean
def imported (moduleName : Name) : IO Export.ExportedEnv := do
  let env ← importModules #[{ module := moduleName }] {} 0
  let consts := env.constants.toList
  return { constMap := Std.HashMap.ofList consts, constOrder := (consts.map Prod.fst).toArray }
def requireSuccess (label : String) (result : Except String Unit) : IO Unit := do
  match result with
  | .ok _ => IO.println s!"PASS {label}"
  | .error err => throw <| IO.userError s!"{label}: unexpected rejection: {err}"
def requireRejection (label needle : String) (result : Except String Unit) : IO Unit := do
  match result with
  | .ok _ => throw <| IO.userError s!"{label}: unexpectedly accepted"
  | .error err =>
    if (err.splitOn needle).length < 2 then
      throw <| IO.userError s!"{label}: unexpected rejection reason: {err}"
    IO.println s!"PASS {label}: {err}"
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let challenge ← imported `Challenge
  let solution ← imported `Solution
  requireSuccess "actual exact isotropic signature" <|
    Comparator.compareAt challenge solution #[`NLA.Proofs.TR26.isotropic_degree] #[] #[]
  requireSuccess "actual transitive standard-three axiom audit" <|
    Comparator.checkAxioms solution #[`NLA.Proofs.TR26.isotropic_degree] #[] #[`propext, `Classical.choice, `Quot.sound]
  requireRejection "actual reference sorry rejection" "Illegal axiom detected: 'sorryAx'" <|
    Comparator.checkAxioms challenge #[`NLA.Proofs.TR26.isotropic_degree] #[] #[`propext, `Classical.choice, `Quot.sound]
'''
 (a.output/'consumers'/'ActualComparatorLibrary.lean.txt').write_text(runner);run('ActualComparatorLibrary',runner.encode(),root=toolsrc,objects=toolobj,run_main=True)
 after=pins();ck('10_pinned_clean_dependencies_after',all(e['pass'] for e in after));ck('all354_private_package_bytes_unchanged',all((src/n).read_bytes()==b for n,b in files.items()))
 result={'pass':all(e['pass'] for e in checks),'reviewer':'/root/verification','UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'package_commit':REF,'proof_source_ref':PROOF,'scope':'Canonical isotropic-only package; not full Target, Linux isolation, exporter or raw kernel replay','whole_problem_verified':False,'Linux_CI_run':False,'Comparator_library_executed':True,'Comparator_CLI_executed':False,'raw_kernel_replay':False,'checks':checks,'commands':commands,'dependency_pins_before':before,'dependency_pins_after':after,'compiler_version':version,'compiler_sha256':sha(a.lean.read_bytes()),'package_inputs':[{'path':n,'bytes':len(b),'sha256':sha(b)} for n,b in files.items()],'runtime_order':order,'external_imports':sorted(external),'tool_pins':tool_records,'Forsythe_commit':tool_lock['commit'],'private_build':str(a.build),'script_sha256':sha(Path(__file__).read_bytes())}
 (a.output/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'pass':result['pass'],'checks':len(checks),'commands':len(commands)}),flush=True)
if __name__=='__main__':main()
