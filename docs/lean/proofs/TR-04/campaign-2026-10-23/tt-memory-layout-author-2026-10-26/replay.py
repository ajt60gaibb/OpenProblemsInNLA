#!/usr/bin/env python3
"""Fresh author replay of the concrete TT memory allocation and safety contracts."""
import argparse, datetime, hashlib, json, os, pathlib, re, subprocess, sys
HERE=pathlib.Path(__file__).resolve().parent
REPO=HERE.parents[5]
LIVE=REPO/'lean-statements'
TOOLING=pathlib.Path(os.environ.get('NLA_CAMPAIGN_TOOLING',REPO.parent/'tooling'))
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--output',type=pathlib.Path,default=HERE/'run')
OUT=p.parse_args().output.resolve()
SNAP,OBJECTS=OUT/'sources',OUT/'objects'
assert not OBJECTS.exists(), 'Choose new output; no project objects may be reused.'
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lock=json.loads((HERE/'source-lock.json').read_text())
def check_inputs():
    for rec in lock['project_closure']+lock['unchanged_boundary_and_pins']:
        assert h(REPO/rec['path'])==rec['sha256'],rec['path']
    prior=lock['prior_selector_source_lock']
    assert h(REPO/prior['path'])==prior['sha256']
    for rec in json.loads((REPO/prior['path']).read_text())['project_closure']:
        assert h(REPO/rec['path'])==rec['sha256'],rec['path']
    radix=HERE.parent/'radix-interface-author-2026-10-25/source-lock.json'
    assert h(radix)==lock['prior_radix_source_lock_sha256']
    for rec in json.loads(radix.read_text())['project_closure']:
        assert h(REPO/rec['path'])==rec['sha256'],rec['path']
    original=json.loads((HERE.parent/'input-lock.json').read_text())['records']
    assert len(original)==25
    for rec in original:
        assert h(REPO/rec['path'])==rec['sha256'],rec['path']
check_inputs()
for rec in lock['project_closure']:
    rel=pathlib.Path(rec['path']).relative_to('lean-statements')
    dst=SNAP/rel;dst.parent.mkdir(parents=True,exist_ok=True)
    dst.write_bytes((LIVE/rel).read_bytes())
(SNAP/'.lake').mkdir(exist_ok=True)
(SNAP/'.lake/packages').symlink_to((LIVE/'.lake/packages').resolve(),target_is_directory=True)
env=dict(os.environ,NLA_CAMPAIGN_SOURCE_ROOT=str(SNAP),NLA_CAMPAIGN_OBJECT_ROOT=str(OBJECTS))
command=[sys.executable,str(TOOLING/'tr06-build-closure.py')]+lock['targets']
with (OUT/'source-build.log').open('w') as log:
    proc=subprocess.run(command,cwd=REPO,env=env,stdout=log,stderr=subprocess.STDOUT)
assert proc.returncode==0,OUT/'source-build.log'
consumer=SNAP/'TTMemoryLayoutAuthorConsumer.lean'
text='''import NLA.Proofs.TR04.TTMemoryLayoutMatrix
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace TTMemoryLayoutAuthorConsumer
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
open NLA.Proofs.TR04.TTMemoryLayout
 theorem literal_first_output_blocks (d N m l : ℕ) (hm : m ≤ N) (hl : l ≤ N) :
    OutputBlocksDisjoint m l (2*d-1+N) (2*d-1+N+N^2) (2*d-1+N+N^2+N) :=
  Layout.first_outputs_disjoint ⟨d,N⟩ m l hm hl
 theorem literal_child_output_blocks (d N level m l : ℕ) (hm : m ≤ N) (hl : l ≤ N) :
    OutputBlocksDisjoint m l
      (2*d-1+N+N^2+N+N^2+N+N^2+level*N^2)
      (2*d-1+N+N^2+N+N^2) (2*d-1+N+N^2+N+N^2+N) :=
  Layout.child_outputs_disjoint ⟨d,N⟩ level m l hm hl
 theorem literal_original_heap_bound (S : Shape) (r : Ranks S) (K : ℕ)
    (hK : K ≤ DenseSize S + 1) :
    2*S.order-1+DenseSize S+(DenseSize S)^2+DenseSize S+(DenseSize S)^2+
      DenseSize S+(DenseSize S)^2+S.order*(DenseSize S)^2+4*S.order+
      DenseSize S+DenseSize S+K*DenseSize S ≤20*(Size S r+1)^3 :=
  ofShape_endAddress_le_size S r K hK
 theorem literal_work_buffers (L : Layout) (m l a b : ℕ)
    (hml : m*l ≤ L.entries) (hab : a*b ≤ L.entries) :
    DisjointBlocks L.workA (m*l) L.workB (a*b) :=
  L.work_rectangle_disjoint m l a b hml hab
 theorem literal_transpose_contract_safety (L : Layout) (level m q cols : ℕ)
    (memory : ℕ → ℝ) (hlevel : level < L.order)
    (hm : m ≤ L.entries) (hq : q ≤ L.entries)
    (hmcols : m*cols ≤ L.entries) (hqcols : q*cols ≤ L.entries) :
    (L.contraction level m q cols memory).InputsOutsideOutput :=
  L.contraction_inputsOutsideOutput level m q cols memory hlevel hm hq hmcols hqcols
 theorem literal_empty_svd_outputs (L : Layout) :
    OutputBlocksDisjoint 0 0 L.firstU L.firstSigma L.firstV :=
  L.first_outputs_disjoint 0 0 (Nat.zero_le _) (Nat.zero_le _)
#assert_trust kernel literal_first_output_blocks
#assert_trust kernel literal_child_output_blocks
#assert_trust kernel literal_original_heap_bound
#assert_trust kernel literal_work_buffers
#assert_trust kernel literal_transpose_contract_safety
#assert_trust kernel literal_empty_svd_outputs
#print axioms literal_first_output_blocks
#print axioms literal_child_output_blocks
#print axioms literal_original_heap_bound
#print axioms literal_work_buffers
#print axioms literal_transpose_contract_safety
#print axioms literal_empty_svd_outputs
end TTMemoryLayoutAuthorConsumer
'''
for name in lock['authored_declarations']:
    text+='#assert_trust kernel '+name+'\n#print axioms '+name+'\n'
consumer.write_text(text)
binary=TOOLING/'lean-4.33.1-darwin_aarch64/bin/lean'
paths=[OBJECTS]+[p/'.lake/build/lib/lean' for p in sorted((SNAP/'.lake/packages').iterdir()) if (p/'.lake/build/lib/lean').is_dir()]
cenv=dict(env,LEAN_PATH=os.pathsep.join(map(str,paths)),PATH=str(binary.parent)+os.pathsep+os.environ['PATH'])
cc=[str(binary),'-o',str(OBJECTS/'TTMemoryLayoutAuthorConsumer.olean'),str(consumer)]
with (OUT/'consumer-build.log').open('w') as log:
    cp=subprocess.run(cc,cwd=SNAP,env=cenv,stdout=log,stderr=subprocess.STDOUT)
assert cp.returncode==0,OUT/'consumer-build.log'
check_inputs()
for rec in lock['project_closure']:
    assert h(SNAP/pathlib.Path(rec['path']).relative_to('lean-statements'))==rec['sha256']
logs=(OUT/'source-build.log').read_text()+(OUT/'consumer-build.log').read_text()
assert 'sorryAx' not in logs
axioms=re.findall(r'depends on axioms: \[([^]]*)\]',logs)
assert all(set(x.strip() for x in a.split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'} for a in axioms)
metas=list(OBJECTS.rglob('*.source-sha256.json'))
assert len(metas)==len(lock['project_closure'])
result={'author':'/root/recover_geometry','date':'2026-10-26','executed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'passed':True,'scope':'Fresh author kernel replay of concrete TT memory layout/safety/address bounds only; no independent review, complete TT Target/program, Linux CI or Comparator claim','source_lock_sha256':h(HERE/'source-lock.json'),'driver_sha256':h(pathlib.Path(__file__)),'authored_source_count':len(lock['authored_sources']),'fresh_project_closure_source_count':len(metas),'fresh_kernel_command_count':len(metas)+1,'authored_declarations_asserted':len(lock['authored_declarations']),'literal_first_child_SVD_outputs_original_heap_bound_zero_dimensions_and_explicit_work_capacity_consumer':True,'project_objects_reused':False,'pinned_external_package_cache_reused':True,'source_build_exit_code':proc.returncode,'consumer_build_exit_code':cp.returncode,'all_frozen_live_and_snapshot_sources_unchanged':True,'prior_selector_radix_recursive_sources_and_all_25_original_review_inputs_preserved':True,'printed_axiom_lists':axioms,'compiler':subprocess.check_output([str(binary),'--version'],text=True).strip(),'source_command':command,'consumer_command':cc,'evidence':[{'path':str(p.relative_to(OUT)),'sha256':h(p)} for p in [consumer,OUT/'source-build.log',OUT/'consumer-build.log']]}
(OUT/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
