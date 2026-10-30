#!/usr/bin/env python3
"""Fresh author replay of the three exact machine-support modules, not TR04 Target."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,importlib.util
P=argparse.ArgumentParser(description=__doc__);P.add_argument('--tooling',type=Path,required=True);P.add_argument('--output',type=Path,required=True);a=P.parse_args()
repo=Path(__file__).resolve().parents[5];project=repo/'lean-statements';out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
files=['MachineExecution','MachineTotality','MachineTraceBounds'];names=[];sources={}
for f in files:
 p=project/'NLA/Proofs/TR04'/f'{f}.lean';s=p.read_text();sources[str(p.relative_to(repo))]=hashlib.sha256(p.read_bytes()).hexdigest()
 import re
 names += re.findall(r'^theorem ([A-Za-z0-9_]+)',s,re.M)
env=dict(os.environ,NLA_CAMPAIGN_SOURCE_ROOT=str(project),NLA_CAMPAIGN_OBJECT_ROOT=str(out/'objects'))
with (out/'closure.log').open('w') as log:
 result=subprocess.run(['python3',str(a.tooling/'tr06-build-closure.py'),'NLA.Proofs.TR04.MachineTraceBounds'],env=env,stdout=log,stderr=subprocess.STDOUT)
if result.returncode:raise SystemExit(result.returncode)
consumer='import NLA.Proofs.TR04.MachineTraceBounds\nset_option leancert.trust "kernel"\n'
for name in names:consumer+=f'#assert_trust kernel NLA.Proofs.TR04.{name}\n#print axioms NLA.Proofs.TR04.{name}\n'
consumer+='''example (P : NLA.Computation.SVDMachine.Program) (s : NLA.Computation.SVDMachine.State P) :
    ∃ tr : NLA.Computation.SVDMachine.Trace P, NLA.Computation.SVDMachine.LegalTrace P s tr :=
  NLA.Proofs.TR04.exists_legalTrace P s
'''
p=out/'MachineSupportConsumer.lean.txt';p.write_text(consumer)
spec=importlib.util.spec_from_file_location('pinned_lean',a.tooling/'tr06-lean.py');m=importlib.util.module_from_spec(spec)
os.environ.update(NLA_CAMPAIGN_SOURCE_ROOT=str(project),NLA_CAMPAIGN_OBJECT_ROOT=str(out/'objects'));spec.loader.exec_module(m)
with (out/'consumer.log').open('w') as log:
 r=subprocess.run([str(m.BIN/'lean'),str(p)],cwd=project,env=m.ENV,stdout=log,stderr=subprocess.STDOUT)
if r.returncode:raise SystemExit(r.returncode)
for name,digest in sources.items():assert hashlib.sha256((repo/name).read_bytes()).hexdigest()==digest
commands=sum(line.endswith(' 0') for line in (out/'closure.log').read_text().splitlines())+1
report={'scope':'Fresh private local author replay of exact machine support and unconditional legal-trace totality. Not an approximation, termination, cost bound or complete TR04 proof.', 'passed':True,'author':'/root','owned_modules':3,'owned_theorem_kernel_checks':len(names),'project_objects_reused':False,'pinned_external_dependency_objects_reused':True,'successful_commands':commands,'sources':sources,'consumer_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'logs':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in out.glob('*.log')}}
(out/'result.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
