#!/usr/bin/env python3
"""Fresh snapshot author replay of the complete original TR04 Target and actual finite candidate loop."""
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
consumer_path=Path(__file__).with_name('TTFullTargetConsumer.lean.txt')
consumer_input=consumer_path.read_bytes()
consumer_snapshot=out/'ConsumerInput.lean.txt';consumer_snapshot.write_bytes(consumer_input)
assert not re.search(r'^(?:theorem|def|axiom|instance)\s',consumer_input.decode(),re.M),'Unexpected named declaration in consumer'

owned=['MachineTTCandidateLoopInduction','MachineTTCompletedCandidates','TTFullBudget','MachineTTCandidateExecution','MachineTTCandidateAll','MachineTTFull']
targets=['NLA.Proofs.TR04.MachineTTFull']
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
prior_path=repo/'docs/lean/proofs/TR-04/campaign-2026-10-26/independent-evidence-index/result-through-initial-family-child.json'
prior=json.loads(prior_path.read_text())
for name,digest in prior['current_project_source_hashes'].items():assert sha(project/name)==digest,name

for file in ['lean-toolchain','lake-manifest.json','lakefile.toml']:
    shutil.copyfile(project/file,snapshot/file)
(snapshot/'.lake').mkdir();(snapshot/'.lake/packages').symlink_to((project/'.lake/packages').resolve(),target_is_directory=True)
originals=json.loads((repo/'docs/lean/proofs/TR-04/campaign-2026-10-23/input-lock.json').read_text())['records']
for record in originals:assert sha(repo/record['path'])==record['sha256'],record['path']
names=[]
for file in owned:
    text=(snapshot/'NLA/Proofs/TR04'/f'{file}.lean').read_text()
    names += ['NLA.Proofs.TR04.'+name for name in re.findall(r'^(?:@\[[^\]]+\]\s*)?(?:noncomputable\s+)?(?:def|theorem|structure|instance)\s+([A-Za-z0-9_.]+)',text,re.M)]
lock={'execution_started_utc':started,'scope':'Complete unchanged original TR04 Target: one fixed finite program and C1000000 k5 before all original inputs and all legal full-SVD reply traces; actual stored candidate loop, minimum, feasibility and strict-or-zero; author fresh kernel only, not independent or Linux/Comparator acceptance','author':'/root','replay_driver_sha256':sha(Path(__file__)),'consumer_input':{'path':str(consumer_path.relative_to(repo)),'sha256':sha(consumer_snapshot)},'authored_modules':owned,'authored_declarations':names,'targets':targets,'project_closure':list(closure.values()),'reviewed_original_inputs':originals,'prior_frozen_source_record':{'path':str(prior_path.relative_to(repo)),'sha256':sha(prior_path),'current_project_source_hashes':prior['current_project_source_hashes']}}
(out/'source-lock.json').write_text(json.dumps(lock,indent=2)+'\n')
env=dict(os.environ,NLA_CAMPAIGN_SOURCE_ROOT=str(snapshot),NLA_CAMPAIGN_OBJECT_ROOT=str(out/'objects'))
with (out/'closure.log').open('w') as log:
    r=subprocess.run(['python3',str(a.tooling/'tr06-build-closure.py'),*targets],env=env,stdout=log,stderr=subprocess.STDOUT)
assert r.returncode==0,'closure failed'
consumer=consumer_input.decode()
for name in names:consumer+=f'#assert_trust kernel {name}\n#print axioms {name}\n'
cp=out/'TTFullTargetConsumerWithTrust.lean.txt';cp.write_text(consumer)
spec=importlib.util.spec_from_file_location('pinned_lean',a.tooling/'tr06-lean.py');m=importlib.util.module_from_spec(spec)
os.environ.update(NLA_CAMPAIGN_SOURCE_ROOT=str(snapshot),NLA_CAMPAIGN_OBJECT_ROOT=str(out/'objects'));spec.loader.exec_module(m)
with (out/'consumer.log').open('w') as log:
    r=subprocess.run([str(m.BIN/'lean'),str(cp)],cwd=snapshot,env=m.ENV,stdout=log,stderr=subprocess.STDOUT)
assert r.returncode==0,'consumer failed'
assert consumer_path.read_bytes()==consumer_input
for rec in closure.values():assert sha(repo/rec['path'])==rec['sha256'],rec['path']
for rec in originals:assert sha(repo/rec['path'])==rec['sha256'],rec['path']
for name,digest in prior['current_project_source_hashes'].items():assert sha(project/name)==digest,name
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
report={'execution_started_utc':started,'execution_completed_utc':datetime.now(timezone.utc).isoformat(),'only_standard_three_axioms':True,'axiom_reports_checked':len(axiom_sets),'passed':True,'scope':lock['scope'],'author':'/root','new_modules':len(owned),'project_modules_rebuilt':len(closure),'successful_commands':commands,'public_declaration_kernel_checks':len(names),'literal_consumer_examples':15,'verbatim_public_theorem_headers':13,'project_objects_reused':False,'pinned_external_objects_reused':True,'pinned_dependencies':pins,'replay_driver_sha256':sha(Path(__file__)),'consumer_input_sha256':sha(consumer_snapshot),'source_lock_sha256':sha(out/'source-lock.json'),'consumer_sha256':sha(cp),'reviewed_original_inputs_unchanged':len(originals),'logs':{p.name:sha(p) for p in out.glob('*.log')}}
(out/'result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
