#!/usr/bin/env python3
"""Fresh author kernel replay of literal recursive TT controller execution."""
import argparse,datetime,hashlib,json,os,pathlib,re,subprocess,sys
HERE=pathlib.Path(__file__).resolve().parent;REPO=HERE.parents[5];LIVE=REPO/'lean-statements'
TOOLING=pathlib.Path(os.environ.get('NLA_CAMPAIGN_TOOLING',REPO.parent/'tooling'))
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=pathlib.Path,default=HERE/'final')
OUT=p.parse_args().output.resolve();SNAP=OUT/'sources';OBJECTS=OUT/'objects'
assert not OBJECTS.exists(),'Use a new output: acceptance cannot reuse project objects.'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
LOCK=HERE/'source-lock.json';lock_sha=h(LOCK);lock=json.loads(LOCK.read_text())
def path_for(record):
 p=REPO/record['path']
 if not p.exists():p=LIVE/record['path']
 return p

def check_record(record):
 p=path_for(record);assert h(p)==record['sha256'],str(p)
 return p

def check_inputs():
 assert h(LOCK)==lock_sha
 for group in ['project_closure','authored_sources','unchanged_boundary_and_pins','reviewed_original_inputs']:
  for record in lock[group]:check_record(record)
 assert len(lock['reviewed_original_inputs'])==25
 for record in lock['prior_frozen_evidence']:
  prior=check_record(record);data=json.loads(prior.read_text())
  for group in ['project_closure','authored_sources','sources','frozen_sources','runtime_pins','unchanged_boundary_and_pins','reviewed_original_inputs']:
   for item in data.get(group,[]):
    if isinstance(item,dict)and 'path'in item and 'sha256'in item:check_record(item)
 check_record(lock['literal_consumer'])
check_inputs()
for record in lock['project_closure']:
 rel=pathlib.Path(record['path']).relative_to('lean-statements');dst=SNAP/rel
 dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes((LIVE/rel).read_bytes())
for record in lock['unchanged_boundary_and_pins']:
 rel=pathlib.Path(record['path'])
 if str(rel).startswith('lean-statements/'):
  dst=SNAP/rel.relative_to('lean-statements');dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes((REPO/rel).read_bytes())
(SNAP/'.lake').mkdir(exist_ok=True);(SNAP/'.lake/packages').symlink_to((LIVE/'.lake/packages').resolve(),target_is_directory=True)
env=dict(os.environ,NLA_CAMPAIGN_SOURCE_ROOT=str(SNAP),NLA_CAMPAIGN_OBJECT_ROOT=str(OBJECTS))
command=[sys.executable,str(TOOLING/'tr06-build-closure.py')]+lock['targets']
with (OUT/'source-build.log').open('w')as log:proc=subprocess.run(command,cwd=REPO,env=env,stdout=log,stderr=subprocess.STDOUT)
assert proc.returncode==0,OUT/'source-build.log'
consumer=SNAP/'ExactConsumer.lean';consumer.write_bytes((HERE/'ExactConsumer.lean').read_bytes())
binary=TOOLING/'lean-4.33.1-darwin_aarch64/bin/lean'
paths=[OBJECTS]+[p/'.lake/build/lib/lean'for p in sorted((SNAP/'.lake/packages').iterdir())if(p/'.lake/build/lib/lean').is_dir()]
cenv=dict(env,LEAN_PATH=os.pathsep.join(map(str,paths)),PATH=str(binary.parent)+os.pathsep+os.environ['PATH'])
cc=[str(binary),'-o',str(OBJECTS/'ExactConsumer.olean'),str(consumer)]
with (OUT/'consumer-build.log').open('w')as log:cp=subprocess.run(cc,cwd=SNAP,env=cenv,stdout=log,stderr=subprocess.STDOUT)
assert cp.returncode==0,OUT/'consumer-build.log'
check_inputs()
for record in lock['project_closure']:assert h(SNAP/pathlib.Path(record['path']).relative_to('lean-statements'))==record['sha256']
logs=(OUT/'source-build.log').read_text()+(OUT/'consumer-build.log').read_text()
assert 'sorryAx'not in logs
axioms=re.findall(r'depends on axioms: \[([^]]*)\]',logs)
assert all(set(x.strip()for x in a.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for a in axioms)
metas=list(OBJECTS.rglob('*.source-sha256.json'));assert len(metas)==len(lock['project_closure'])
consumer_log=(OUT/'consumer-build.log').read_text()
for name in lock['authored_declarations']+lock['literal_consumer']['literal_endpoints']:assert "'"+name+"' depends on axioms:"in consumer_log,name
result=dict(author='/root/recover_geometry',executed_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),passed=True,scope=lock['scope'],source_lock_sha256=lock_sha,driver_sha256=h(pathlib.Path(__file__)),authored_source_count=len(lock['authored_sources']),fresh_project_closure_source_count=len(metas),fresh_kernel_command_count=len(metas)+1,authored_explicit_declarations_asserted=len(lock['authored_declarations']),literal_consumer_kernel_assertions=lock['literal_consumer']['declared_kernel_assertions'],project_objects_reused=False,pinned_external_package_cache_reused=True,source_build_exit_code=proc.returncode,consumer_build_exit_code=cp.returncode,all_frozen_live_and_snapshot_sources_unchanged=True,reviewed_original25_and_literal_model_Target_IDs_pins_unchanged=True,printed_axiom_lists=axioms,compiler=subprocess.check_output([str(binary),'--version'],text=True).strip(),compiler_binary_sha256=h(binary),source_command=command,consumer_command=cc,evidence=[dict(path=str(p.relative_to(OUT)),sha256=h(p))for p in [consumer,OUT/'source-build.log',OUT/'consumer-build.log']])
(OUT/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
