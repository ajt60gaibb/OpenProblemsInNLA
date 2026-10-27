#!/usr/bin/env python3
"""Independent immutable TR26 full-target source replay; no source mutation.

Uses the supplied pinned compiler/dependency build, creates its own source and
output objects, and deliberately rejects separate invalid proof consumers.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo',type=Path,required=True)
p.add_argument('--lean',type=Path,required=True)
p.add_argument('--packages',type=Path,required=True)
p.add_argument('--build',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args()
for k,v in vars(a).items(): setattr(a,k,v.resolve())
a.build.mkdir(parents=True,exist_ok=False);a.output.mkdir(parents=True,exist_ok=False)
C='ecc597cb68b65b473aecce9ac635e27d35c09694'
D='docs/lean/proofs/TR-26/campaign-2026-10-26/'
sha=lambda b:hashlib.sha256(b).hexdigest()
git=lambda *v:subprocess.check_output(['git',*v],cwd=a.repo)
read=lambda q:git('show',C+':'+q)
checkpoint_data=read(D+'FULL_TARGET_SOURCE_FREEZE.json');checkpoint=json.loads(checkpoint_data)
checks=[]
def check(n,b,**x):
 checks.append(dict(name=n,passed=bool(b),**x))
 assert b,n
check('exact77authored-module-checkpoint',len(checkpoint['proof_inputs'])==77)
inputs={}
for x in checkpoint['proof_inputs']:
 b=read(x['path']);check('checkpoint-source:'+x['path'],sha(b)==x['sha256'] and len(b)==x['bytes'])
 inputs[x['path'].removeprefix('lean-statements/')[:-5].replace('/','.')]=dict(path=x['path'],bytes=b)
for module in ['NLA.Statements.Infrastructure','NLA.Statements.TR26','Reviewed.TR26']:
 path='lean-statements/'+module.replace('.','/')+'.lean';inputs[module]=dict(path=path,bytes=read(path))
pre=json.loads(read(D+'preproof/INPUT_LOCK.json'))
check('exact-frozen-preproof-lock',sha(read(D+'preproof/INPUT_LOCK.json'))=='59314bd19a35f47dadd9a672517d4f9053682b4454b79c571cb915231342a91c')
for x in pre['reviewed_inputs']:
 b=read(D+'preproof/frozen/'+x['path']);check('all24originals-retained:'+x['path'],sha(b)==x['sha256'] and len(b)==x['bytes'] and b==read(x['path']))
check('canonical-status-remains-Solved',b'**Status:** Solved' in read('tensor-computations/TR-26/README.md'))
manifest=json.loads(read('lean-statements/lake-manifest.json'));pins=[]
for x in manifest['packages']:
 path=a.packages/x['name'];head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=path).decode().strip();dirty=subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=path).decode()
 check('dependency-pin-and-tracked-clean:'+x['name'],head==x['rev'] and dirty=='');pins.append(dict(name=x['name'],rev=head,tracked_clean=dirty==''))
source=a.build/'source';out=a.build/'out';source.mkdir();out.mkdir()
env=os.environ.copy();env['PATH']=str(a.lean.parent)+os.pathsep+env.get('PATH','');env['LEAN_PATH']=':'.join([str(out)]+[str(q/'.lake/build/lib/lean') for q in sorted(a.packages.iterdir()) if (q/'.lake/build/lib/lean').is_dir()]+[str(a.lean.parent.parent/'lib/lean')])
version=subprocess.check_output([str(a.lean),'--version'],text=True).strip()
check('official-pinned-Lean4331',version.startswith('Lean (version 4.33.1,') and 'commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version)
records=[]
def run(module,data,expected=0):
 f=source/(module.replace('.','/')+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(data)
 obj=out/(module.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 argv=[str(a.lean),'-R',str(source),'-o',str(obj),str(f)]
 r=subprocess.run(argv,cwd=source,env=env,text=True,capture_output=True,timeout=600)
 log=r.stdout+r.stderr;(a.output/(module+'.log')).write_text(log)
 (a.output/(module+'.lean.txt')).write_bytes(data)
 records.append(dict(module=module,source_sha256=sha(data),argv=argv,exit_code=r.returncode,expected_exit=expected,log_sha256=sha(log.encode())))
 print(module,r.returncode,flush=True);check('fresh-command:'+module,r.returncode==expected,actual=r.returncode,expected=expected)
 if r.returncode!=expected:raise RuntimeError(log)
 return log
done=set();order=[]
def visit(module):
 if module in done:return
 done.add(module)
 for imported in re.findall(r'^import ([A-Za-z0-9_.]+)',inputs[module]['bytes'].decode(),re.M):
  if imported in inputs:visit(imported)
  else:check('external-import-pinned:'+module+':'+imported,imported in {'Mathlib','Lean'} or imported.startswith(('Mathlib.','LeanCert.','Lean.')))
 order.append(module)
for module in inputs:visit(module)
for module in order:run(module,inputs[module]['bytes'])
kind='''open Lean Elab Command in
elab "#assert_proof_constant " n:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  match (← getEnv).find? decl with
  | some (.thmInfo _) => pure ()
  | _ => throwErrorAt n "expected a proved theorem constant"
'''
imports='\n'.join('import '+m for m in inputs)+'\n'
header=imports+'set_option autoImplicit false\nset_option leancert.trust "kernel"\n'+kind
names=[]
for m,x in inputs.items():
 if not m.startswith('NLA.Proofs.TR26.'):continue
 stack=[]
 # Authored source uses explicit, line-start namespace/end commands. These
 # names are checked by Lean, not trusted merely because the scanner found them.
 for line in x['bytes'].decode().splitlines():
  ns=re.match(r'^namespace ([A-Za-z0-9_.]+)\s*$',line)
  end=re.match(r'^end ([A-Za-z0-9_.]+)\s*$',line)
  thm=re.match(r'^(?:theorem|lemma) ([A-Za-z0-9_\']+)\b',line)
  if ns:stack.append(ns.group(1))
  elif end and stack:
   if stack[-1]==end.group(1):stack.pop()
  elif thm:names.append('.'.join(stack+[thm.group(1)]))
check('all-scanned-public-theorems-qualified-unique',len(set(names))==len(names) and all(n.startswith('NLA.Proofs.TR26.') for n in names))
consumer=read(checkpoint['audit_input']['path']).decode()+'\n'+header+'\n'.join('#assert_proof_constant '+n+'\n#assert_trust kernel '+n+'\n#print axioms '+n for n in names)+'''
example (d : ℕ) (hd : 2 ≤ d) :
    NLA.Statements.TR26.HasReducedDegree d (2*d) (NLA.Statements.TR26.IsotropicImage d) :=
  NLA.Proofs.TR26.isotropic_degree d hd
example : NLA.Statements.TR26.Target = NLA.ReviewedStatements.TR26.Target := rfl
'''
log=run('InventoryFullTargetAudit',consumer.encode())
axioms=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log)
check('all-public-theorem-kinds-and-kernel-axioms-standard',len(axioms)==len(names) and [n for n,_ in axioms]==names and all(set(s.strip() for s in ax.split(',')) <= {'propext','Classical.choice','Quot.sound'} for _,ax in axioms))
reference=read(D+'preproof/Challenge.lean');run('InventoryReferenceHoles',reference)
reject=b'import InventoryReferenceHoles\n#assert_trust kernel NLA.Proofs.TR26.nonisotropic_degree\n#assert_trust kernel NLA.Proofs.TR26.isotropic_degree\n#assert_trust kernel NLA.Proofs.TR26.target\n'
log=run('InventoryPlaceholderRejection',reject,1)
check('all3reference-placeholders-actually-rejected',log.count('depends on sorry or unrecognized axioms')==3 and log.count('sorryAx: sorryAx')==3)
fake=header+'''\naxiom InventoryInjectedAxiom : False
theorem inventoryCounterfeit (d : ℕ) (hd : 2 ≤ d) :
    NLA.Statements.TR26.HasReducedDegree d (2*d) (NLA.Statements.TR26.IsotropicImage d) :=
  False.elim InventoryInjectedAxiom
#assert_trust kernel inventoryCounterfeit
'''
log=run('InventoryCustomAxiomRejection',fake.encode(),1)
check('exact-typed-counterfeit-with-custom-axiom-rejected','depends on sorry or unrecognized axioms' in log and 'InventoryInjectedAxiom' in log)
fake=header+'''\ndef inventoryDefinitionAlias (d : ℕ) (hd : 2 ≤ d) :
    NLA.Statements.TR26.HasReducedDegree d (2*d) (NLA.Statements.TR26.IsotropicImage d) :=
  NLA.Proofs.TR26.isotropic_degree d hd
#assert_proof_constant inventoryDefinitionAlias
'''
log=run('InventoryKindRejection',fake.encode(),1)
check('definition-alias-not-counted-as-theorem','expected a proved theorem constant' in log)
result=dict(scope='Independent fresh pinned macOS source replay of all77 authored TR26 modules, both exact degree endpoints and literal full Target. No canonical full-package, Linux or Comparator pipeline claim.',reviewer='/root/inventory',authored_TR26_proof_sources=[],immutable_commit=C,UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),checkpoint_sha256=sha(checkpoint_data),lean_version=version,lean_executable_sha256=sha(a.lean.read_bytes()),script_sha256=sha(Path(__file__).read_bytes()),pins=pins,inputs={m:dict(path=x['path'],sha256=sha(x['bytes'])) for m,x in inputs.items()},compile_order=order,public_theorems=names,public_theorem_count=len(names),records=records,checks=checks,check_count=len(checks),passed=all(c['passed'] for c in checks))
(a.output/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS',result['check_count'],'checks;',len(inputs),'fresh sources;',len(names),'actual theorem-kind/kernel/axiom checks',flush=True)
