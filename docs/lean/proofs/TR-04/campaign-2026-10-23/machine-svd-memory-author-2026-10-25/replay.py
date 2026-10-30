#!/usr/bin/env python3
"""Fresh author replay of the exact SVD output memory interface."""
import argparse, hashlib, json, os, pathlib, re, subprocess, sys

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

consumer = SNAP / 'SVDMemoryAuthorConsumer.lean'
consumer_text = '''import NLA.Proofs.TR04.MachineSVDMemory
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace SVDMemoryAuthorConsumer
open NLA.Computation.SVDMachine NLA.Proofs.TR04
theorem literal_output_readback {m l : ℕ} (old : ℕ → ℝ) (ub sb vb : ℕ)
    (U : Matrix (Fin m) (Fin m) ℝ) (sigma : Fin (min m l) → ℝ)
    (V : Matrix (Fin l) (Fin l) ℝ) (h : OutputBlocksDisjoint m l ub sb vb) :
    readMatrix (writeSVD old ub sb vb U sigma V) m m ub = U ∧
    (∀ k : Fin (min m l), writeSVD old ub sb vb U sigma V (sb + k.val) = sigma k) ∧
    readMatrix (writeSVD old ub sb vb U sigma V) l l vb = V ∧
    (∀ address : ℕ,
      ¬ (ub ≤ address ∧ address < ub + m * m) →
      ¬ (sb ≤ address ∧ address < sb + min m l) →
      ¬ (vb ≤ address ∧ address < vb + l * l) →
      writeSVD old ub sb vb U sigma V address = old address) := by
  exact ⟨readMatrix_writeSVD_u old ub sb vb U sigma V,
    writeSVD_sigma_entry old ub sb vb U sigma V h,
    readMatrix_writeSVD_v old ub sb vb U sigma V h,
    writeSVD_outside old ub sb vb U sigma V⟩
theorem literal_row_major {m l : ℕ} (A : Matrix (Fin m) (Fin l) ℝ)
    (i : Fin m) (j : Fin l) : matrixCell A (i.val * l + j.val) = A i j :=
  matrixCell_entry A i j
#assert_trust kernel literal_output_readback
#assert_trust kernel literal_row_major
#print axioms literal_output_readback
#print axioms literal_row_major
end SVDMemoryAuthorConsumer
'''
for name in lock['authored_declarations']:
    consumer_text += '#assert_trust kernel ' + name + '\n#print axioms ' + name + '\n'
consumer.write_text(consumer_text)
binary = TOOLING / 'lean-4.33.1-darwin_aarch64/bin/lean'
paths = [OBJECTS] + [p / '.lake/build/lib/lean' for p in sorted((SNAP / '.lake/packages').iterdir())
                     if (p / '.lake/build/lib/lean').is_dir()]
cenv = dict(env, LEAN_PATH=os.pathsep.join(map(str, paths)),
            PATH=str(binary.parent) + os.pathsep + os.environ['PATH'])
consumer_cmd = [str(binary), '-o', str(OBJECTS / 'SVDMemoryAuthorConsumer.olean'), str(consumer)]
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
assert len(metas) == len(lock['project_closure']) == 2
result = {
    'author': '/root/recover_geometry', 'date': '2026-10-25', 'passed': True,
    'scope': 'Fresh author kernel replay of exact output memory equations; no independent review, Target, actual full algorithm/runtime, Linux CI or Comparator claim',
    'source_lock_sha256': digest(HERE / 'source-lock.json'),
    'driver_sha256': digest(pathlib.Path(__file__)),
    'authored_source_count': 1, 'fresh_project_closure_source_count': 2,
    'fresh_kernel_command_count': 3, 'authored_declarations_asserted': len(lock['authored_declarations']),
    'literal_model_matrixCell_readMatrix_writeSVD_consumer': True,
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
