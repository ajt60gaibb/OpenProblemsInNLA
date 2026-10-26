#!/usr/bin/env python3
"""Fresh author replay of genuine recursive TT dimension and positivity bounds."""
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
    prior=lock['prior_layout_source_lock']
    assert h(REPO/prior['path'])==prior['sha256']
    for rec in json.loads((REPO/prior['path']).read_text())['project_closure']:
        assert h(REPO/rec['path'])==rec['sha256'],rec['path']
    selector=json.loads((REPO/prior['path']).read_text())['prior_selector_source_lock']
    assert h(REPO/selector['path'])==selector['sha256']
    for rec in json.loads((REPO/selector['path']).read_text())['project_closure']:
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
consumer=SNAP/'TTDimensionAuthorConsumer.lean'
text='import NLA.Proofs.TR04.TTDimensionBoundsReachable\nset_option autoImplicit false\nset_option leancert.trust "kernel"\nnamespace TTDimensionAuthorConsumer\nopen NLA.Computation.TensorTrainApproximation\nopen NLA.Proofs.TR04.TensorFormat NLA.Proofs.TR04.TensorFormat.Dimensions\n theorem literal_all_natural_product_reduction (m n : ℕ) (ns : List ℕ) (r : ℕ → ℕ) :\n    (min (r 0) (min m (Fintype.card (Index (n::ns)))) * n) * ns.prod ≤\n      m * (n * ns.prod) := step_prod_le m n ns r\n theorem literal_reachable_work_and_squares (S : Shape) (r : Ranks S)\n    (hr : ∀ j, 1 ≤ r j) (level m n : ℕ) (ns : List ℕ)\n    (h : Reachable (modeList S.mode) (originalRanks S r) level (m::n::ns)) :\n    let q := stepRank m (n::ns) (fun j => originalRanks S r (level+j))\n    let cols := Fintype.card (Index (n::ns))\n    0<m ∧ 0<q ∧ 0<cols ∧ 0<q*n ∧\n      m≤DenseSize S ∧ q≤DenseSize S ∧ cols≤DenseSize S ∧\n      m*cols≤DenseSize S ∧ q*cols≤DenseSize S ∧\n      (q*n)*ns.prod≤DenseSize S ∧\n      m*m≤(DenseSize S)^2 ∧ m*q≤(DenseSize S)^2 ∧ cols*cols≤(DenseSize S)^2 := by\n  have hb := h.original_step_bounds S r hr\n  exact ⟨hb.rows_pos,hb.rank_pos,hb.cols_pos,hb.child_mode_pos,hb.rows_le,hb.rank_le,\n    hb.cols_le,hb.input_dense_le,hb.contracted_dense_le,hb.child_prod_le,\n    hb.frame_square_le,hb.frame_rectangle_le,hb.right_square_le⟩\n theorem literal_suffix_layout (S : Shape) (r : Ranks S) (level m n : ℕ) (ns : List ℕ)\n    (h : Reachable (modeList S.mode) (originalRanks S r) level (m::n::ns)) :\n    Fintype.card (Index (n::ns)) = ((modeList S.mode).drop (level+1)).prod :=\n  h.original_suffix S r\n theorem literal_two_modes_terminate (m n : ℕ) (r : ℕ → ℕ) :\n    ((stepRank m [n] r * n)::([]:List ℕ)).length = 1 := rfl\n theorem literal_zero_request (m : ℕ) (ns : List ℕ) :\n    stepRank m ns (fun _ => 0) = 0 := by simp [stepRank,cappedRank]\n#assert_trust kernel literal_all_natural_product_reduction\n#assert_trust kernel literal_reachable_work_and_squares\n#assert_trust kernel literal_suffix_layout\n#assert_trust kernel literal_two_modes_terminate\n#assert_trust kernel literal_zero_request\n#print axioms literal_all_natural_product_reduction\n#print axioms literal_reachable_work_and_squares\n#print axioms literal_suffix_layout\n#print axioms literal_two_modes_terminate\n#print axioms literal_zero_request\nend TTDimensionAuthorConsumer\n'
for name in lock['authored_declarations']:
    text+='#assert_trust kernel '+name+'\n#print axioms '+name+'\n'
consumer.write_text(text)
binary=TOOLING/'lean-4.33.1-darwin_aarch64/bin/lean'
paths=[OBJECTS]+[p/'.lake/build/lib/lean' for p in sorted((SNAP/'.lake/packages').iterdir()) if (p/'.lake/build/lib/lean').is_dir()]
cenv=dict(env,LEAN_PATH=os.pathsep.join(map(str,paths)),PATH=str(binary.parent)+os.pathsep+os.environ['PATH'])
cc=[str(binary),'-o',str(OBJECTS/'TTDimensionAuthorConsumer.olean'),str(consumer)]
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
result={'author':'/root/recover_geometry','date':'2026-10-26','executed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'passed':True,'scope':'Fresh author kernel replay of genuine recursive TT dimension/positivity/capacity invariants only; no independent review, complete TT Target/program, Linux CI or Comparator claim','source_lock_sha256':h(HERE/'source-lock.json'),'driver_sha256':h(pathlib.Path(__file__)),'authored_source_count':len(lock['authored_sources']),'fresh_project_closure_source_count':len(metas),'fresh_kernel_command_count':len(metas)+1,'authored_declarations_asserted':len(lock['authored_declarations']),'literal_unconditional_product_reduction_original_reachable_work_sizes_squares_suffix_two_modes_zero_rank_consumer':True,'project_objects_reused':False,'pinned_external_package_cache_reused':True,'source_build_exit_code':proc.returncode,'consumer_build_exit_code':cp.returncode,'all_frozen_live_and_snapshot_sources_unchanged':True,'prior_layout_selector_radix_recursive_sources_and_all_25_original_review_inputs_preserved':True,'printed_axiom_lists':axioms,'compiler':subprocess.check_output([str(binary),'--version'],text=True).strip(),'source_command':command,'consumer_command':cc,'evidence':[{'path':str(p.relative_to(OUT)),'sha256':h(p)} for p in [consumer,OUT/'source-build.log',OUT/'consumer-build.log']]}
(OUT/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
