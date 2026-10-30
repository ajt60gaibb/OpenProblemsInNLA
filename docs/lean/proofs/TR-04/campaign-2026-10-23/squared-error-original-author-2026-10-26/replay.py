#!/usr/bin/env python3
"""Fresh author replay of original tensor Frobenius memory interface."""
import argparse, datetime, hashlib, json, os, pathlib, re, subprocess, sys

HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parents[5]
LIVE = REPO / 'lean-statements'
TOOLING = pathlib.Path(os.environ.get('NLA_CAMPAIGN_TOOLING', REPO.parent / 'tooling'))
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=pathlib.Path, default=HERE / 'run')
OUT = parser.parse_args().output.resolve()
SNAP, OBJECTS = OUT / 'sources', OUT / 'objects'
assert not OBJECTS.exists(), 'Choose a new output directory; no project objects may be reused.'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
lock = json.loads((HERE / 'source-lock.json').read_text())

def check_inputs():
    for rec in lock['project_closure'] + lock['unchanged_boundary_and_pins']:
        assert digest(REPO / rec['path']) == rec['sha256'], rec['path']
    prior = HERE.parent / 'radix-interface-author-2026-10-25/source-lock.json'
    assert digest(prior) == lock['prior_radix_source_lock_sha256']
    for rec in json.loads(prior.read_text())['project_closure']:
        assert digest(REPO / rec['path']) == rec['sha256'], rec['path']
    rec = lock['squared_error_source_lock']
    assert digest(REPO / rec['path']) == rec['sha256']
    for src in json.loads((REPO / rec['path']).read_text())['sources']:
        assert digest(LIVE / src['path']) == src['sha256']
    rec = lock['shape_header_source_lock']
    assert digest(REPO / rec['path']) == rec['sha256']
    for src in json.loads((REPO / rec['path']).read_text())['authored_sources']:
        assert digest(REPO / src['path']) == src['sha256']
    original = json.loads((HERE.parent / 'input-lock.json').read_text())['records']
    assert len(original) == 25
    for rec in original:
        assert digest(REPO / rec['path']) == rec['sha256'], rec['path']

check_inputs()
for rec in lock['project_closure']:
    rel = pathlib.Path(rec['path']).relative_to('lean-statements')
    dst = SNAP / rel
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_bytes((LIVE / rel).read_bytes())
(SNAP / '.lake').mkdir(exist_ok=True)
(SNAP / '.lake/packages').symlink_to((LIVE / '.lake/packages').resolve(), target_is_directory=True)
env = dict(os.environ, NLA_CAMPAIGN_SOURCE_ROOT=str(SNAP), NLA_CAMPAIGN_OBJECT_ROOT=str(OBJECTS))
command = [sys.executable, str(TOOLING / 'tr06-build-closure.py')] + lock['targets']
with (OUT / 'source-build.log').open('w') as log:
    proc = subprocess.run(command, cwd=REPO, env=env, stdout=log, stderr=subprocess.STDOUT)
assert proc.returncode == 0, OUT / 'source-build.log'

consumer = SNAP / 'SquaredErrorOriginalConsumer.lean'
consumer_text = 'import NLA.Proofs.TR04.MachineSquaredErrorOriginal\nset_option autoImplicit false\nset_option leancert.trust "kernel"\nopen scoped BigOperators\nnamespace SquaredErrorOriginalConsumer\nopen NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation NLA.Proofs.TR04\n theorem literal_squared_error (S : Shape) (memory : ℕ → ℝ) (baseA baseB : ℕ)\n    (A B : Tensor S) (hA : ∀ x, memory (baseA + Offset S x) = A x)\n    (hB : ∀ x, memory (baseB + Offset S x) = B x) :\n    (∑ i ∈ Finset.range (∏ j, S.mode j),\n      (memory (baseA + i) - memory (baseB + i))^2) = ∑ x : Index S, (A x - B x)^2 :=\n  squaredErrorSum_eq_frobeniusSq S memory baseA baseB A B hA hB\n theorem literal_caller_error {Q : Program} (E : RoutineEmbedding squaredErrorProgram Q)\n    (S : Shape) (r : Ranks S) (memory : ℕ → ℝ) (baseA baseB : ℕ) (A B : Tensor S)\n    (hA : ∀ x, memory (baseA + Offset S x) = A x)\n    (hB : ∀ x, memory (baseB + Offset S x) = B x)\n    (accumulator scratchA scratchB : ℝ) {start : State Q} {trace : Trace Q} (offset : ℕ)\n    (hs : E.Relates (squaredErrorStart memory baseA baseB (DenseSize S)\n      accumulator scratchA scratchB) (trace.state offset)) (ht : LegalTrace Q start trace) :\n    (trace.state (offset + (9 * DenseSize S + 2))).label = E.labels 10 ∧\n    (trace.state (offset + (9 * DenseSize S + 2))).real (E.reals 0) = ∑ x : Index S, (A x - B x)^2 ∧\n    (trace.state (offset + (9 * DenseSize S + 2))).memory = memory ∧\n    (trace.state (offset + (9 * DenseSize S + 2))).status = .running ∧\n    CostThrough Q trace (offset + (9 * DenseSize S + 2)) ≤\n      CostThrough Q trace offset + (9 * DenseSize S + 2) ∧\n    CostThrough Q trace (offset + (9 * DenseSize S + 2)) ≤\n      CostThrough Q trace offset + 11 * Size S r ∧\n    (∀ j : Fin Q.realRegisters, (∀ i, j ≠ E.reals i) →\n      (trace.state (offset + (9 * DenseSize S + 2))).real j = (trace.state offset).real j) ∧\n    (∀ j : Fin (Q.extraNatRegisters + 1), (∀ i, j ≠ E.naturals i) →\n      (trace.state (offset + (9 * DenseSize S + 2))).natural j = (trace.state offset).natural j) :=\n  E.squaredError_run_frobenius S r memory baseA baseB A B hA hB accumulator scratchA scratchB\n    offset hs ht\n#assert_trust kernel literal_squared_error\n#assert_trust kernel literal_caller_error\n#print axioms literal_squared_error\n#print axioms literal_caller_error\nend SquaredErrorOriginalConsumer\n'
for name in lock['authored_declarations']:
    consumer_text += '#assert_trust kernel ' + name + '\n#print axioms ' + name + '\n'
consumer.write_text(consumer_text)
binary = TOOLING / 'lean-4.33.1-darwin_aarch64/bin/lean'
paths = [OBJECTS] + [p / '.lake/build/lib/lean' for p in sorted((SNAP / '.lake/packages').iterdir())
                     if (p / '.lake/build/lib/lean').is_dir()]
cenv = dict(env, LEAN_PATH=os.pathsep.join(map(str, paths)),
            PATH=str(binary.parent) + os.pathsep + os.environ['PATH'])
consumer_cmd = [str(binary), '-o', str(OBJECTS / 'SquaredErrorOriginalConsumer.olean'), str(consumer)]
with (OUT / 'consumer-build.log').open('w') as log:
    cp = subprocess.run(consumer_cmd, cwd=SNAP, env=cenv, stdout=log, stderr=subprocess.STDOUT)
assert cp.returncode == 0, OUT / 'consumer-build.log'
check_inputs()
for rec in lock['project_closure']:
    assert digest(SNAP / pathlib.Path(rec['path']).relative_to('lean-statements')) == rec['sha256']
logs = (OUT / 'source-build.log').read_text() + (OUT / 'consumer-build.log').read_text()
assert 'sorryAx' not in logs
axioms = re.findall(r'depends on axioms: \[([^]]*)\]', logs)
assert all(set(x.strip() for x in a.split(',') if x.strip()) <=
           {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms)
metas = sorted(OBJECTS.rglob('*.source-sha256.json'))
assert len(metas) == len(lock['project_closure'])
result = {
    'author': '/root/recover_geometry', 'date': '2026-10-26', 'executed_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'passed': True,
    'scope': 'Fresh author kernel replay of literal original Frobenius memory interface and actual squared-error caller charges; no independent review, complete TT Target/program, Linux CI or Comparator claim',
    'source_lock_sha256': digest(HERE / 'source-lock.json'),
    'driver_sha256': digest(pathlib.Path(__file__)),
    'authored_source_count': len(lock['authored_sources']), 'fresh_project_closure_source_count': len(metas),
    'fresh_kernel_command_count': len(metas) + 1, 'authored_declarations_asserted': len(lock['authored_declarations']),
    'literal_dense_sum_original_FrobeniusSq_CostThrough_consumer': True,
    'project_objects_reused': False, 'pinned_external_package_cache_reused': True,
    'source_build_exit_code': proc.returncode, 'consumer_build_exit_code': cp.returncode,
    'all_frozen_live_and_snapshot_sources_unchanged': True,
    'prior_radix_recursive_sources_and_all_25_original_review_inputs_preserved': True,
    'printed_axiom_lists': axioms,
    'compiler': subprocess.check_output([str(binary), '--version'], text=True).strip(),
    'source_command': command, 'consumer_command': consumer_cmd,
    'evidence': [{'path': str(p.relative_to(OUT)), 'sha256': digest(p)} for p in
                 [consumer, OUT / 'source-build.log', OUT / 'consumer-build.log']]}
(OUT / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
