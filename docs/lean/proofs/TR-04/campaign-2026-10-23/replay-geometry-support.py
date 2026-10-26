#!/usr/bin/env python3
"""Fresh author replay of frozen TR-04 geometry supports, not independent review."""
import argparse, hashlib, json, os, pathlib, re, subprocess, sys

HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parents[4]
SOURCE = REPO / 'lean-statements'
TOOLING = pathlib.Path(os.environ.get('NLA_CAMPAIGN_TOOLING', REPO.parent / 'tooling'))
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=pathlib.Path, default=HERE / 'author-fresh-geometry')
args = parser.parse_args()
OUT = args.output.resolve()
OBJECTS = OUT / 'objects'
if OBJECTS.exists():
    raise SystemExit('Refusing to reuse project objects; pass a new --output directory.')
OUT.mkdir(parents=True, exist_ok=True)
lock = json.loads((HERE / 'geometry-support-source-lock.json').read_text())
def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
for record in lock['records']:
    assert digest(REPO / record['path']) == record['sha256'], record['path']
env = dict(os.environ, NLA_CAMPAIGN_SOURCE_ROOT=str(SOURCE),
           NLA_CAMPAIGN_OBJECT_ROOT=str(OBJECTS))
command = [sys.executable, str(TOOLING / 'tr06-build-closure.py'),
           'NLA.Proofs.TR04.Optimum', 'NLA.Proofs.TR04.ReshapeFrobenius']
with (OUT / 'source-build.log').open('w') as log:
    result = subprocess.run(command, env=env, cwd=REPO, stdout=log, stderr=subprocess.STDOUT)
assert result.returncode == 0, (OUT / 'source-build.log')
consumer = OUT / 'Consumer.lean'
consumer.write_text('''import NLA.Proofs.TR04.Optimum
import NLA.Proofs.TR04.ReshapeFrobenius
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace TR04GeometryAuthorConsumer
open NLA.Computation.TensorTrainApproximation NLA.Proofs.TR04
example (S : Shape) (j : Cut S) :
    RowIndex S j × ColIndex S j ≃ Index S := joinEquiv S j
example (S : Shape) (j : Cut S) :
    Tensor S ≃L[ℝ] Matrix (RowIndex S j) (ColIndex S j) ℝ :=
  unfoldContinuousLinearEquiv S j
example (S : Shape) (r : Ranks S) : Feasible S r 0 := feasible_zero S r
example (S : Shape) (r : Ranks S) : IsClosed {Y : Tensor S | Feasible S r Y} :=
  isClosed_feasible S r
 theorem actual_optimum_attained (S : Shape) (r : Ranks S) (A : Tensor S) :
    ∃ X : Tensor S, Feasible S r X ∧ Optimum S r A = FrobeniusSq S A X :=
  exists_optimum S r A
 theorem actual_optimum_zero (S : Shape) (r : Ranks S) (A : Tensor S) :
    Optimum S r A = 0 ↔ Feasible S r A := optimum_eq_zero_iff_feasible S r A
#assert_trust kernel actual_optimum_attained
#assert_trust kernel actual_optimum_zero
#print axioms actual_optimum_attained
#print axioms actual_optimum_zero
end TR04GeometryAuthorConsumer
''')
binary = TOOLING / 'lean-4.33.1-darwin_aarch64' / 'bin' / 'lean'
packages = SOURCE / '.lake/packages'
paths = [OBJECTS] + [p / '.lake/build/lib/lean' for p in sorted(packages.iterdir())
                     if (p / '.lake/build/lib/lean').is_dir()]
consumer_env = dict(env, LEAN_PATH=os.pathsep.join(map(str, paths)))
consumer_command = [str(binary), '--root=' + str(REPO), '-o',
                    str(OBJECTS / 'AuthorConsumer.olean'), str(consumer)]
with (OUT / 'consumer-build.log').open('w') as log:
    consumer_result = subprocess.run(consumer_command, env=consumer_env, cwd=REPO,
                                     stdout=log, stderr=subprocess.STDOUT)
assert consumer_result.returncode == 0, (OUT / 'consumer-build.log')
for record in lock['records']:
    assert digest(REPO / record['path']) == record['sha256'], record['path']
build_text = (OUT / 'source-build.log').read_text()
consumer_text = (OUT / 'consumer-build.log').read_text()
assert 'sorryAx' not in build_text + consumer_text
axiom_lists = re.findall(r'depends on axioms: \[([^]]*)\]', build_text + consumer_text)
for axioms in axiom_lists:
    assert set(x.strip() for x in axioms.split(',') if x.strip()) <= {
        'propext', 'Classical.choice', 'Quot.sound'}, axioms
receipt = {
    'author': '/root/recover_geometry', 'date': '2026-10-23',
    'scope': 'Fresh author replay; no independent reviewer, final Target, CI or Comparator claim',
    'status': 'PASS', 'source_command': command, 'consumer_command': consumer_command,
    'source_root': str(SOURCE), 'object_root': str(OBJECTS),
    'project_objects_reused': False, 'read_only_pinned_external_package_objects_reused': True,
    'source_build_exit_code': result.returncode,
    'consumer_build_exit_code': consumer_result.returncode,
    'fresh_project_modules': [p.relative_to(OBJECTS).as_posix() for p in sorted(OBJECTS.rglob('*.source-sha256.json'))],
    'kernel_mode': True, 'printed_axiom_lists': axiom_lists,
    'frozen_sources_unchanged': True,
    'compiler': subprocess.run([str(binary), '--version'], text=True, capture_output=True, check=True).stdout.strip(),
    'files': [{'path': str(p.relative_to(OUT)), 'sha256': digest(p)} for p in
              [consumer, OUT / 'source-build.log', OUT / 'consumer-build.log']]
}
(OUT / 'result.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
