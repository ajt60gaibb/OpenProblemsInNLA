#!/usr/bin/env python3
"""Fresh author replay of callable strided RAM matrix multiplication."""
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
    matrix_lock = HERE.parent / 'matrix-multiply-author-2026-10-25/source-lock.json'
    assert digest(matrix_lock) == lock['frozen_matrix_three_source_lock_sha256']
    for rec in json.loads(matrix_lock.read_text())['project_closure']:
        assert digest(REPO / rec['path']) == rec['sha256']
    for key in ['root_relocation_lock', 'root_no_early_halt']:
        rec = lock[key]
        assert digest(REPO / rec['path']) == rec['sha256']
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

consumer = SNAP / 'MatrixMultiplyCallableConsumer.lean'
consumer_text = 'import NLA.Proofs.TR04.MachineMatrixMultiplyCallable\nset_option autoImplicit false\nset_option leancert.trust "kernel"\nnamespace MatrixMultiplyCallableConsumer\nopen NLA.Computation.SVDMachine NLA.Proofs.TR04\n theorem arbitrary_caller_actual_fields {Q : Program}\n    (E : RoutineEmbedding matrixMultiplyProgram Q) (p : MatrixMultiplyData)\n    (h : p.InputsOutsideOutput) (scratch : MatrixMultiplyScratch)\n    {start : State Q} {trace : Trace Q} (ht : LegalTrace Q start trace) (offset : ℕ)\n    (hs : E.Relates (matrixMultiplyRowState p 0 scratch) (trace.state offset)) :\n    (trace.state (offset + (matrixMultiplyRowTime p * p.rows + 1))).label = E.labels 21 ∧\n    (trace.state (offset + (matrixMultiplyRowTime p * p.rows + 1))).status = .running ∧\n    readMatrix (trace.state (offset + (matrixMultiplyRowTime p * p.rows + 1))).memory\n      p.rows p.cols p.dBase = p.leftMatrix * p.rightMatrix ∧\n    (∀ address, ¬ (p.dBase ≤ address ∧ address < p.dBase + p.rows * p.cols) →\n      (trace.state (offset + (matrixMultiplyRowTime p * p.rows + 1))).memory address = p.memory address) ∧\n    CostThrough Q trace (offset + (matrixMultiplyRowTime p * p.rows + 1)) ≤\n      CostThrough Q trace offset + 17 * (p.rows + p.inner + p.cols + 1) ^ 3 ∧\n    (∀ j : Fin Q.realRegisters, (∀ i, j ≠ E.reals i) →\n      (trace.state (offset + (matrixMultiplyRowTime p * p.rows + 1))).real j =\n        (trace.state offset).real j) ∧\n    (∀ j : Fin (Q.extraNatRegisters + 1), (∀ i, j ≠ E.naturals i) →\n      (trace.state (offset + (matrixMultiplyRowTime p * p.rows + 1))).natural j =\n        (trace.state offset).natural j) :=\n  E.matrixMultiply_product_at p h scratch ht offset hs\n#assert_trust kernel arbitrary_caller_actual_fields\n#print axioms arbitrary_caller_actual_fields\nend MatrixMultiplyCallableConsumer\n'
for name in lock['authored_declarations']:
    consumer_text += '#assert_trust kernel ' + name + '\n#print axioms ' + name + '\n'
consumer.write_text(consumer_text)
binary = TOOLING / 'lean-4.33.1-darwin_aarch64/bin/lean'
paths = [OBJECTS] + [p / '.lake/build/lib/lean' for p in sorted((SNAP / '.lake/packages').iterdir())
                     if (p / '.lake/build/lib/lean').is_dir()]
cenv = dict(env, LEAN_PATH=os.pathsep.join(map(str, paths)),
            PATH=str(binary.parent) + os.pathsep + os.environ['PATH'])
consumer_cmd = [str(binary), '-o', str(OBJECTS / 'MatrixMultiplyCallableConsumer.olean'), str(consumer)]
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
    'author': '/root/recover_geometry', 'campaign_date': '2026-10-25', 'executed_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'passed': True,
    'scope': 'Fresh author kernel replay of callable finite strided matrix multiplication at arbitrary caller time, actual prefix costs and outside-frame registers; no independent review, full TT Target, Linux CI or Comparator claim',
    'source_lock_sha256': digest(HERE / 'source-lock.json'),
    'driver_sha256': digest(pathlib.Path(__file__)),
    'authored_source_count': len(lock['authored_sources']), 'fresh_project_closure_source_count': len(metas),
    'fresh_kernel_command_count': len(metas) + 1, 'authored_declarations_asserted': len(lock['authored_declarations']),
    'literal_arbitrary_caller_continuation_product_CostThrough_register_consumer': True,
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
