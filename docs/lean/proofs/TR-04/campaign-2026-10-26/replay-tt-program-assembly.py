#!/usr/bin/env python3
"""Fresh snapshot replay of static finite TT assembly, direct trace interfaces and initial header prefix; not full TR04 Target."""
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess
from pathlib import Path
from datetime import datetime,timezone
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--tooling',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args()
repo=Path(__file__).resolve().parents[5]
project=repo/'lean-statements'
out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
snapshot=out/'sources';snapshot.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
started=datetime.now(timezone.utc).isoformat()
owned=['MachineCodeBanks','MachineInstructionTrace','MachineTTProgram','MachineTTProgramFacts']
targets=['NLA.Proofs.TR04.MachineTTProgramFacts']
closure={}
def visit(mod):
    if mod in closure:return
    path=Path(mod.replace('.','/')+'.lean')
    src=project/path
    closure[mod]={'path':str(Path('lean-statements')/path),'sha256':sha(src),'bytes':src.stat().st_size}
    dest=snapshot/path;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest)
    for imp in re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',src.read_text(),re.M):
        if imp.startswith(('NLA.','Reviewed.')):visit(imp)
for mod in targets:visit(mod)
for file in ['lean-toolchain','lake-manifest.json','lakefile.toml']:
    shutil.copyfile(project/file,snapshot/file)
(snapshot/'.lake').mkdir();(snapshot/'.lake/packages').symlink_to((project/'.lake/packages').resolve(),target_is_directory=True)
originals=json.loads((repo/'docs/lean/proofs/TR-04/campaign-2026-10-23/input-lock.json').read_text())['records']
for record in originals:assert sha(repo/record['path'])==record['sha256'],record['path']
names=[]
for file in owned:
    text=(snapshot/'NLA/Proofs/TR04'/f'{file}.lean').read_text()
    names += ['NLA.Proofs.TR04.'+name for name in re.findall(r'^(?:@\[[^\]]+\]\s*)?(?:noncomputable\s+)?(?:def|theorem|structure)\s+([A-Za-z0-9_.]+)',text,re.M)]
lock={'execution_started_utc':started,'scope':'Four finite TT assembly/direct trace/initial-prefix supporting modules. Full recursive execution, approximation and uniform total cost remain unproved; no full TR04 Target or Linux/Comparator claim','author':'/root','authored_modules':owned,'authored_declarations':names,'targets':targets,'project_closure':list(closure.values()),'reviewed_original_inputs':originals}
support=[Path(__file__).with_name('program-assembly')/f for f in ['generate-controller.py','controller-layout.json','PREFIX_GATHER_REVIEW_FINDING.json']]
lock['support_inputs']=[{'path':str(p.relative_to(repo)),'sha256':sha(p)} for p in support]
with (out/'generator-check.log').open('w') as log:subprocess.run(['python3',str(support[0]),'--check'],stdout=log,stderr=subprocess.STDOUT,check=True)
(out/'source-lock.json').write_text(json.dumps(lock,indent=2)+'\n')
env=dict(os.environ,NLA_CAMPAIGN_SOURCE_ROOT=str(snapshot),NLA_CAMPAIGN_OBJECT_ROOT=str(out/'objects'))
with (out/'closure.log').open('w') as log:
    r=subprocess.run(['python3',str(a.tooling/'tr06-build-closure.py'),*targets],env=env,stdout=log,stderr=subprocess.STDOUT)
assert r.returncode==0,'closure failed'
consumer=Path(__file__).with_name('TTProgramAssemblyConsumer.lean.txt').read_text()
for name in names:consumer+=f'#assert_trust kernel {name}\n#print axioms {name}\n'
cp=out/'TTProgramAssemblyConsumerWithTrust.lean.txt';cp.write_text(consumer)
spec=importlib.util.spec_from_file_location('pinned_lean',a.tooling/'tr06-lean.py');m=importlib.util.module_from_spec(spec)
os.environ.update(NLA_CAMPAIGN_SOURCE_ROOT=str(snapshot),NLA_CAMPAIGN_OBJECT_ROOT=str(out/'objects'));spec.loader.exec_module(m)
with (out/'consumer.log').open('w') as log:
    r=subprocess.run([str(m.BIN/'lean'),str(cp)],cwd=snapshot,env=m.ENV,stdout=log,stderr=subprocess.STDOUT)
assert r.returncode==0,'consumer failed'
for rec in lock['support_inputs']:assert sha(repo/rec['path'])==rec['sha256'],rec['path']
for rec in closure.values():assert sha(repo/rec['path'])==rec['sha256'],rec['path']
for rec in originals:assert sha(repo/rec['path'])==rec['sha256'],rec['path']
manifest=json.loads((project/'lake-manifest.json').read_text())
pins=[]
for pkg in manifest['packages']:
    path=(project/'.lake/packages'/pkg['name']).resolve()
    head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=path,text=True).strip()
    dirty=subprocess.check_output(['git','status','--porcelain','--untracked-files=normal'],cwd=path,text=True)
    assert head==pkg['rev'] and not dirty,pkg['name']
    pins.append({'name':pkg['name'],'revision':head,'clean':True})
axiom_log=(out/'consumer.log').read_text()
axiom_sets={name:set(x.strip() for x in values.split(',') if x.strip()) for name,values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",axiom_log,re.S)}
for name in re.findall(r"'([^']+)' does not depend on any axioms",axiom_log):axiom_sets[name]=set()
assert set(axiom_sets)==set(names),set(axiom_sets)^set(names)
assert all(v<={'propext','Classical.choice','Quot.sound'} for v in axiom_sets.values())
commands=sum(line.endswith(' 0') for line in (out/'closure.log').read_text().splitlines())+1
assert commands==len(closure)+1
report={'execution_started_utc':started,'execution_completed_utc':datetime.now(timezone.utc).isoformat(),'only_standard_three_axioms':True,'axiom_reports_checked':len(axiom_sets),'passed':True,'scope':lock['scope'],'author':'/root','new_modules':4,'project_modules_rebuilt':len(closure),'successful_commands':commands,'public_declaration_kernel_checks':len(names),'literal_consumer_examples':14,'project_objects_reused':False,'pinned_external_objects_reused':True,'pinned_dependencies':pins,'source_lock_sha256':sha(out/'source-lock.json'),'consumer_sha256':sha(cp),'reviewed_original_inputs_unchanged':len(originals),'logs':{p.name:sha(p) for p in out.glob('*.log')}}
(out/'result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
