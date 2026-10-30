#!/usr/bin/env python3
"""Fresh author kernel replay of actual saved-metadata decoding, strided lift and reverse return."""
import argparse,datetime,hashlib,json,os,pathlib,re,subprocess,sys
HERE=pathlib.Path(__file__).resolve().parent
REPO=HERE.parents[5]
LIVE=REPO/'lean-statements'
TOOLING=pathlib.Path(os.environ.get('NLA_CAMPAIGN_TOOLING',REPO.parent/'tooling'))
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=pathlib.Path,default=HERE/'run')
OUT=parser.parse_args().output.resolve();SNAP,OBJECTS=OUT/'sources',OUT/'objects'
assert not OBJECTS.exists(),'Use new output: no project objects may be reused.'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lock=json.loads((HERE/'source-lock.json').read_text())
consumer_sha=h(HERE/'ExactConsumer.lean')
def check_lock(rec):
    path=REPO/rec['path'];assert h(path)==rec['sha256'],path
    data=json.loads(path.read_text())
    for group in ['project_closure','unchanged_boundary_and_pins','reviewed_original_inputs','support_inputs']:
        for item in data.get(group,[]):
            assert h(REPO/item['path'])==item['sha256'],item['path']
    return data

def check_inputs():
    for rec in lock['project_closure']+lock['unchanged_boundary_and_pins']:
        assert h(REPO/rec['path'])==rec['sha256'],rec['path']
    check_lock(lock['prior_forward_source_lock'])
    check_lock(lock['root_initialization_source_lock'])
    header=check_lock(lock['prior_header_metadata_source_lock'])
    check_lock(lock['prior_tensor_multiply_source_lock'])
    dim=check_lock(lock['prior_dimension_source_lock'])
    layout=check_lock(dim['prior_layout_source_lock'])
    check_lock(layout['prior_selector_source_lock'])
    check_lock(lock['root_assembly_source_lock'])
    campaign23=HERE.parent.parent/'campaign-2026-10-23'
    radix=campaign23/'radix-interface-author-2026-10-25/source-lock.json'
    assert h(radix)==dim['prior_radix_source_lock_sha256']
    for rec in json.loads(radix.read_text())['project_closure']:
        assert h(REPO/rec['path'])==rec['sha256'],rec['path']
    original=json.loads((campaign23/'input-lock.json').read_text())['records']
    assert len(original)==25
    for rec in original:assert h(REPO/rec['path'])==rec['sha256'],rec['path']
    assert h(HERE/'ExactConsumer.lean')==consumer_sha
check_inputs()
for rec in lock['project_closure']:
    rel=pathlib.Path(rec['path']).relative_to('lean-statements');dst=SNAP/rel
    dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes((LIVE/rel).read_bytes())
(SNAP/'.lake').mkdir(exist_ok=True)
(SNAP/'.lake/packages').symlink_to((LIVE/'.lake/packages').resolve(),target_is_directory=True)
env=dict(os.environ,NLA_CAMPAIGN_SOURCE_ROOT=str(SNAP),NLA_CAMPAIGN_OBJECT_ROOT=str(OBJECTS))
command=[sys.executable,str(TOOLING/'tr06-build-closure.py')]+lock['targets']
with (OUT/'source-build.log').open('w') as log:
    proc=subprocess.run(command,cwd=REPO,env=env,stdout=log,stderr=subprocess.STDOUT)
assert proc.returncode==0,OUT/'source-build.log'
consumer=SNAP/'ExactConsumer.lean';consumer.write_bytes((HERE/'ExactConsumer.lean').read_bytes())
binary=TOOLING/'lean-4.33.1-darwin_aarch64/bin/lean'
paths=[OBJECTS]+[p/'.lake/build/lib/lean'for p in sorted((SNAP/'.lake/packages').iterdir())if(p/'.lake/build/lib/lean').is_dir()]
cenv=dict(env,LEAN_PATH=os.pathsep.join(map(str,paths)),PATH=str(binary.parent)+os.pathsep+os.environ['PATH'])
cc=[str(binary),'-o',str(OBJECTS/'ExactConsumer.olean'),str(consumer)]
with (OUT/'consumer-build.log').open('w') as log:
    cp=subprocess.run(cc,cwd=SNAP,env=cenv,stdout=log,stderr=subprocess.STDOUT)
assert cp.returncode==0,OUT/'consumer-build.log'
check_inputs()
for rec in lock['project_closure']:
    assert h(SNAP/pathlib.Path(rec['path']).relative_to('lean-statements'))==rec['sha256']
logs=(OUT/'source-build.log').read_text()+(OUT/'consumer-build.log').read_text();assert 'sorryAx'not in logs
axioms=re.findall(r'depends on axioms: \[([^]]*)\]',logs)
assert all(set(x.strip()for x in a.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for a in axioms)
metas=list(OBJECTS.rglob('*.source-sha256.json'));assert len(metas)==len(lock['project_closure'])
result={'author':'/root/recover_geometry','executed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'passed':True,'scope':'Author kernel replay of actual reverse metadata read/shared decoding, strided matrix lift, buffer swap/level return and physical child unmerge; no independent review, complete TT program/Target, Linux CI or Comparator acceptance claim','source_lock_sha256':h(HERE/'source-lock.json'),'driver_sha256':h(pathlib.Path(__file__)),'authored_source_count':len(lock['authored_sources']),'fresh_project_closure_source_count':len(metas),'fresh_kernel_command_count':len(metas)+1,'authored_explicit_definitions_theorems_asserted':len(lock['authored_declarations']),'literal_reverse_arithmetic_time_parent_or_candidate_pointer_tensor_unmerge_protected_registers_cost_and_prefix_stepOutput_consumer':True,'project_objects_reused':False,'pinned_external_package_cache_reused':True,'source_build_exit_code':proc.returncode,'consumer_build_exit_code':cp.returncode,'all_frozen_live_and_snapshot_sources_unchanged':True,'prior_dimension_layout_selector_radix_assembly_sources_and_original25_preserved':True,'printed_axiom_lists':axioms,'compiler':subprocess.check_output([str(binary),'--version'],text=True).strip(),'source_command':command,'consumer_command':cc,'evidence':[{'path':str(p.relative_to(OUT)),'sha256':h(p)}for p in[consumer,OUT/'source-build.log',OUT/'consumer-build.log']]}
(OUT/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
