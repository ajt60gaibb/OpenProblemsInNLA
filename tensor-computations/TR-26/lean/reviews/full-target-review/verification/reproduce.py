#!/usr/bin/env python3
"""Independent immutable TR26 full exact Target audit; reuse ONLY own fresh equal source objects."""
import argparse,concurrent.futures,datetime,hashlib,json,os,re,shutil,subprocess,threading
from pathlib import Path
REF='ecc597cb68b65b473aecce9ac635e27d35c09694'; OLD='6c607ab14af2b8b2b8075f0b3f1798e037c10899'; BASE='5487945e5a72abd952b0c89915915de8cc9b3e65'; DOC='docs/lean/proofs/TR-26/campaign-2026-10-26/';STANDARD={'propext','Classical.choice','Quot.sound'}
def sha(b):return hashlib.sha256(b).hexdigest()
def clean_lean(text):
    out=[];i=0;depth=0
    while i<len(text):
        if depth:
            if text.startswith("/-",i):depth+=1;out.extend("  ");i+=2
            elif text.startswith("-/",i):depth-=1;out.extend("  ");i+=2
            else:out.append("\n" if text[i]=="\n" else " ");i+=1
        elif text.startswith("/-",i):depth=1;out.extend("  ");i+=2
        elif text.startswith("--",i):
            j=text.find("\n",i);j=len(text) if j<0 else j;out.extend(" "*(j-i));i=j
        elif text[i]=='"':
            out.append(" ");i+=1
            while i<len(text):
                if text[i]=="\\":out.extend("  ");i+=2
                elif text[i]=='"':out.append(" ");i+=1;break
                else:out.append("\n" if text[i]=="\n" else " ");i+=1
        else:out.append(text[i]);i+=1
    assert depth==0
    return "".join(out)
def main():
 p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--lean',type=Path,required=True);p.add_argument('--packages',type=Path,required=True);p.add_argument('--prior',type=Path,required=True);p.add_argument('--build',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--jobs',type=int,default=3);a=p.parse_args()
 a.output.mkdir(parents=True,exist_ok=True);a.build.mkdir(parents=True,exist_ok=False);src=a.build/'source';obj=a.build/'objects'
 for d in [src,obj,a.output/'sources',a.output/'logs',a.output/'consumers']:d.mkdir(parents=True,exist_ok=True)
 def git(*v):return subprocess.check_output(['git','-C',str(a.repo),*v])
 def blob(path,ref=REF):return git('show',ref+':'+path)
 checks=[];commands=[];mutex=threading.Lock()
 def ck(name,value,**extra):
  with mutex:checks.append({'check':name,'pass':bool(value),**extra})
  if not value:raise RuntimeError('Failed check: '+name)
 freeze_bytes=blob(DOC+'FULL_TARGET_SOURCE_FREEZE.json');freeze=json.loads(freeze_bytes);(a.output/'FULL_TARGET_SOURCE_FREEZE.json').write_bytes(freeze_bytes)
 ck('exact_frozen77_source_checkpoint',sha(freeze_bytes)=='30259d66f399459826180f682b02ac5c8766e1df80d277f6c633f56650bc0805' and len(freeze['proof_inputs'])==77 and freeze['trust_mode']=='kernel' and set(freeze['allowed_axioms'])==STANDARD)
 ck('exact_all77_module_set',set(git('ls-tree','-r','--name-only',REF,'--','lean-statements/NLA/Proofs/TR26').decode().splitlines())=={e['path'] for e in freeze['proof_inputs']})
 modulebytes={};source_records=[];decls=[]
 for e in freeze['shared_inputs']+freeze['proof_inputs']:
  path=e['path'];b=blob(path);ck('source_lock:'+path,sha(b)==e['sha256'] and len(b)==e['bytes']);rel=path[len('lean-statements/'):];n=rel[:-5].replace('/','.');modulebytes[n]=b
  for root in [src,a.output/'sources']:
   f=root/rel;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b)
  source_records.append({'module':n,**e,'imports':re.findall(r'^import\s+([\w.]+)\s*$',b.decode(),re.M)})
  if n.startswith('NLA.Proofs.'):
   code=clean_lean(b.decode());ck('no_holes_custom_axioms_unsafe_or_kernel_bypass:'+n,not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b|skipKernelTC|debug\.skip',code) and 'set_option leancert.trust "kernel"' in b.decode())
   namespaces=[]
   for line in code.splitlines():
    ns=re.match(r'^namespace\s+([\w.]+)\s*$',line)
    if ns:namespaces.append(ns[1]);continue
    if re.match(r'^end(?:\s+\S+)?\s*$',line):
     if namespaces:namespaces.pop()
     continue
    dec=re.match(r'^(?:@\[[^\n]*\]\s*)?(theorem|lemma|def|abbrev)\s+([^\s({:]+)',line)
    if dec:
     kind,label=dec.groups();decls.append({'module':n,'name':'.'.join(namespaces+[label]),'kind':'theorem' if kind in ['theorem','lemma'] else 'definition'})
 ck('80_source_closure',len(modulebytes)==80)
 ck('no_PencilProbe',not any('PencilProbe' in n for n in modulebytes))
 prior=a.prior.read_bytes();pr=json.loads(prior);ck('prior_own_fresh_package_replay_passed',pr['pass'] and pr['reviewer']=='/root/verification' and pr['package_commit']==OLD)
 previous_build=Path(pr['private_build']);reused=[]
 source_before={e['path']:e for e in pr['package_inputs']}
 for n,b in modulebytes.items():
  rel=n.replace('.','/')+'.lean'
  if rel not in source_before:continue
  oldrec=source_before[rel];ck('own_reuse_exact_source:'+n,sha(b)==oldrec['sha256'] and len(b)==oldrec['bytes'] and (previous_build/'source'/rel).read_bytes()==b)
  previous_obj=previous_build/'objects'/Path(rel).with_suffix('.olean');ob=previous_obj.read_bytes();dest=obj/Path(rel).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(ob)
  ck('own_reuse_object_hash:'+n,sha(dest.read_bytes())==sha(ob));reused.append({'module':n,'source_sha256':sha(b),'object_sha256':sha(ob),'from':str(previous_obj),'to':str(dest),'prior_commands':[e for e in pr['commands'] if e['module']==n]})
 ck('exact36_own_fresh_objects_reused',len(reused)==36 and all(len(e['prior_commands'])==1 and e['prior_commands'][0]['exit_code']==0 for e in reused))
 lockbytes=blob(DOC+'preproof/INPUT_LOCK.json');lock=json.loads(lockbytes);ck('exact24_original_input_lock',sha(lockbytes)=='59314bd19a35f47dadd9a672517d4f9053682b4454b79c571cb915231342a91c' and len(lock['reviewed_inputs'])==24)
 originals=[]
 for e in lock['reviewed_inputs']:
  b=blob(e['path']);v=b==blob(e['path'],BASE)==blob(DOC+'preproof/frozen/'+e['path']) and sha(b)==e['sha256'] and len(b)==e['bytes'];ck('original:'+e['path'],v);originals.append({**e,'pass':v})
 oldpkg=json.loads(blob('tensor-computations/TR-26/lean/PACKAGE_LOCK.json'));ck('all353_partial_package_inputs_unchanged',len(oldpkg['files'])==353 and all(sha(blob('tensor-computations/TR-26/lean/'+n))==e['sha256'] and len(blob('tensor-computations/TR-26/lean/'+n))==e['bytes'] for n,e in oldpkg['files'].items()) and blob('tensor-computations/TR-26/lean/PACKAGE_LOCK.json')==blob('tensor-computations/TR-26/lean/PACKAGE_LOCK.json',OLD))
 previous=json.loads(blob(DOC+'SUPPORT_CHECKPOINT_03.json'));ck('all53_prior_support_sources_unchanged',len(previous['proof_inputs'])==53 and all(sha(blob(e['path']))==e['sha256'] and len(blob(e['path']))==e['bytes'] for e in previous['proof_inputs']))
 receiptchecks=[]
 for e in freeze['proof_inputs']:
  if not e.get('accepted_receipt'):continue
  b=blob(e['accepted_receipt']);receiptchecks.append({'path':e['accepted_receipt'],'sha256':sha(b),'pass':sha(b)==e['accepted_receipt_sha256']});ck('retained_author_receipt_hash:'+e['path'],receiptchecks[-1]['pass'])
 ck('24_new_author_receipt_bindings_only_no_independent_claim',len(receiptchecks)==24)
 manifest=json.loads(blob('lean-statements/lake-manifest.json'))
 def pins():
  out=[]
  for e in manifest['packages']:
   d=a.packages/e['name'];head=subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD'],text=True).strip();status=subprocess.check_output(['git','-C',str(d),'status','--porcelain','--untracked-files=no'],text=True);out.append({'name':e['name'],'expected':e['rev'],'actual':head,'tracked_clean':not status,'pass':head==e['rev'] and not status})
  return out
 before=pins();ck('ten_pins_clean_before_and_equal_own_prior',len(before)==10 and all(e['pass'] for e in before) and before==pr['dependency_pins_after'])
 version=subprocess.check_output([str(a.lean),'--version'],text=True).strip();ck('same_pinned_compiler_as_own_prior',sha(a.lean.read_bytes())==pr['compiler_sha256'] and version==pr['compiler_version'] and blob('lean-statements/lean-toolchain')==b'leanprover/lean4:v4.33.1\n')
 env=os.environ.copy();deps=[a.packages/e['name']/'.lake/build/lib/lean' for e in manifest['packages']];env['LEAN_PATH']=':'.join(map(str,[obj]+deps+[a.lean.parent.parent/'lib/lean']))
 def run(n,b,expected=0,needle=None):
  f=src/(n.replace('.','/')+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(b);dest=obj/(n.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True);argv=[str(a.lean),'-R',str(src),'-o',str(dest),str(f)]
  r=subprocess.run(argv,cwd=src,env=env,capture_output=True,text=True,timeout=600);log=r.stdout+r.stderr;lf=a.output/'logs'/(n+'.log');lf.write_text(log);rec={'module':n,'argv':argv,'exit_code':r.returncode,'expected_exit':expected,'source_sha256':sha(b),'object_sha256':sha(dest.read_bytes()) if dest.exists() else None,'log':str(lf.relative_to(a.output)),'log_sha256':sha(log.encode())}
  with mutex:commands.append(rec)
  print(n,r.returncode,flush=True);ck('compiler:'+n,r.returncode==expected and (needle is None or needle in log),**rec)
  return log
 complete={e['module'] for e in reused};remaining=set(modulebytes)-complete;imports={e['module']:e['imports'] for e in source_records}
 reachable=set()
 def reach(n):
  if n in reachable:return
  reachable.add(n)
  for c in imports[n]:
   if c in modulebytes:reach(c)
 reach('NLA.Proofs.TR26.MainTarget')
 (a.output/'TARGET_IMPORT_CLOSURE.json').write_text(json.dumps({'source_commit':REF,'root':'NLA.Proofs.TR26.MainTarget','own_modules':sorted(reachable),'own_module_count':len(reachable),'additional_audited_modules':sorted(set(modulebytes)-reachable),'external_imports':sorted({c for n in reachable for c in imports[n] if c not in modulebytes})},indent=2)+'\n')
 ck('external_imports_only_pinned',all(c.startswith(('Mathlib','LeanCert','Lean')) for n in modulebytes for c in imports[n] if c not in modulebytes))
 with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
  active={}
  while remaining or active:
   ready=sorted(n for n in remaining if all(c not in modulebytes or c in complete for c in imports[n]))
   for n in ready[:a.jobs-len(active)]:active[pool.submit(run,n,modulebytes[n])]=n;remaining.remove(n)
   if not active:raise RuntimeError('Cyclic or unresolved own imports')
   done,_=concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED)
   for f in done:f.result();complete.add(active.pop(f))
 ck('all80_source_objects_present',len(complete)==80)
 author_audit=blob(freeze['audit_input']['path']);ck('exact_frozen_author_audit',sha(author_audit)==freeze['audit_input']['sha256']);run('FrozenFullTargetAudit',author_audit);(a.output/'consumers'/'FrozenFullTargetAudit.lean.txt').write_bytes(author_audit)
 guards='''open Lean Elab Command
elab "#review_kind " kind:ident target:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  match ← liftCoreM <| getConstInfo n with
  | .thmInfo _ => unless kind.getId == `theorem do throwError "expected definition"
  | .defnInfo _ => unless kind.getId == `definition do throwError "review requires an actual theorem"
  | _ => throwError "unexpected declaration kind"
'''
 audit='\n'.join('import '+n for n in sorted(modulebytes))+'\nset_option leancert.trust "kernel"\n'+guards+'\n'.join('#review_kind '+('«theorem»' if d['kind']=='theorem' else 'definition')+' '+d['name']+'\n#assert_trust kernel '+d['name']+'\n#print axioms '+d['name'] for d in decls)+'\n'
 challenge=blob(DOC+'preproof/Challenge.lean');ck('exact_frozen_preapproved_Challenge',sha(challenge)=='122ad60aaddf59e91dacd627637cf7237b8614d83b6d2eead381a76a698d7aba')
 audit+='\nopen NLA.Statements.TR26\n'
 for name in ['nonisotropic_degree','isotropic_degree','target']:
  header=challenge.decode().split('theorem '+name,1)[1].split(':= by',1)[0];audit+='example'+header+':= NLA.Proofs.TR26.'+name+(' d hd' if name!='target' else '')+'\n'
 audit+='example : NLA.Statements.TR26.Target = NLA.ReviewedStatements.TR26.Target := rfl\n'
 audit+='example : NLA.ReviewedStatements.TR26.HasReducedDegree 2 6 (NLA.ReviewedStatements.TR26.NonisotropicClosure 2) := NLA.Proofs.TR26.nonisotropic_degree 2 (by decide)\nexample : NLA.ReviewedStatements.TR26.HasReducedDegree 2 4 (NLA.ReviewedStatements.TR26.IsotropicImage 2) := NLA.Proofs.TR26.isotropic_degree 2 (by decide)\n'
 log=run('IndependentFullExactAudit',audit.encode());(a.output/'consumers'/'IndependentFullExactAudit.lean.txt').write_text(audit);closures={}
 for n,v in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S):closures[n]=[x.strip() for x in v.split(',') if x.strip()]
 for n in re.findall(r"'([^']+)' does not depend on any axioms",log):closures[n]=[]
 ck('all_actual_declaration_kinds_kernel_and_standard_axioms',set(closures)=={d['name'] for d in decls} and all(set(v)<=STANDARD for v in closures.values()),closures=closures)
 ck('three_endpoints_actual_theorems_exact_std3',all(set(closures['NLA.Proofs.TR26.'+n])==STANDARD and any(d['name']=='NLA.Proofs.TR26.'+n and d['kind']=='theorem' for d in decls) for n in ['nonisotropic_degree','isotropic_degree','target']))
 run('ReferenceChallenge',challenge)
 holes='import ReferenceChallenge\nset_option leancert.trust "kernel"\n'+''.join('#assert_trust kernel NLA.Proofs.TR26.'+n+'\n' for n in ['nonisotropic_degree','isotropic_degree','target']);log=run('ReferenceHoleRejection',holes.encode(),1,'sorryAx');ck('all3_actual_reference_holes_rejected',log.count('depends on sorry or unrecognized axioms')==3)
 fake='import NLA.Proofs.TR26.MainTarget\n'+guards+'def CounterfeitTarget : NLA.Statements.TR26.Target := NLA.Proofs.TR26.target\n#review_kind «theorem» CounterfeitTarget\n';run('DefinitionKindRejection',fake.encode(),1,'requires an actual theorem')
 taint='import NLA.Statements.TR26\nset_option leancert.trust "kernel"\naxiom CounterfeitOracle : NLA.Statements.TR26.Target\ntheorem CounterfeitTarget : NLA.Statements.TR26.Target := CounterfeitOracle\n#assert_trust kernel CounterfeitTarget\n';run('CustomAxiomRejection',taint.encode(),1,'CounterfeitOracle')
 after=pins();ck('same_ten_pins_clean_after',before==after and all(e['pass'] for e in after));ck('all80_source_bytes_unchanged',all((src/(n.replace('.','/')+'.lean')).read_bytes()==b for n,b in modulebytes.items()));ck('all36_own_reused_objects_unchanged',all(sha(Path(e['to']).read_bytes())==e['object_sha256'] and sha(Path(e['from']).read_bytes())==e['object_sha256'] for e in reused))
 result={'pass':all(e['pass'] for e in checks),'reviewer':'/root/verification','UTC':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_commit':REF,'scope':'Both literal degree endpoints and exact unchanged full Target; full canonical packaging/Linux/Comparator/exporter remain separate','Linux_CI_run':False,'Comparator_executed':False,'raw_kernel_replay':False,'source_modules':80,'newly_compiled_source_modules':44,'own_fresh_reused_source_modules':36,'prior_own_package_result_sha256':sha(prior),'prior_own_package_result':str(a.prior),'reuse_records':reused,'checks':checks,'commands':commands,'source_records':source_records,'declarations':decls,'dependency_pins_before':before,'dependency_pins_after':after,'compiler_version':version,'compiler_sha256':sha(a.lean.read_bytes()),'LEAN_PATH':env['LEAN_PATH'],'private_build':str(a.build),'script_sha256':sha(Path(__file__).read_bytes())}
 (a.output/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'pass':result['pass'],'checks':len(checks),'commands':len(commands),'declarations':len(decls),'new':44,'own_reused':36}),flush=True)
if __name__=='__main__':main()
