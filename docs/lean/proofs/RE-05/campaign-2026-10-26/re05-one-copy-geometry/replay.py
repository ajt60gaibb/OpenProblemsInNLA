#!/usr/bin/env python3
"""Fresh author replay of deterministic RE05 same-plan residual, coefficient, optimum and one-copy error bounds."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[5]
LIVE = REPO / 'lean-statements'
TOOL = REPO.parent / 'tooling'
args = argparse.ArgumentParser(description=__doc__)
args.add_argument('--output', type=Path, default=HERE / 'final')
OUT = args.parse_args().output.resolve()
SNAP, OBJECTS = OUT / 'sources', OUT / 'objects'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
freeze_path = HERE / 'SOURCE_FREEZE.json'
freeze_sha = sha(freeze_path)
freeze = json.loads(freeze_path.read_text())
input_path = HERE.parent / 'attained-input-lock.json'
input_sha = '05d6b0bc8a3fd4dc65facb3144a50d9dc51bf0a1dd57e04d0c522213415e597d'
assert sha(input_path) == input_sha
inputs = json.loads(input_path.read_text())['source_inputs']
assert sha(HERE / 'Consumer.lean') == freeze['consumer_sha256']
assert sha(HERE / 'NegativeControl.lean') == freeze['negative_control_sha256']
assert sha(Path(__file__)) == freeze['driver_sha256']

seen, records = set(), []
def visit(module):
    if module in seen:
        return
    seen.add(module)
    p = LIVE / (module.replace('.', '/') + '.lean')
    for dep in re.findall(r'^import\s+(\S+)\s*$', p.read_text(), re.M):
        if dep.startswith(('NLA.', 'Reviewed.')):
            visit(dep)
    records.append(dict(module=module, path=str(p.relative_to(REPO)), sha256=sha(p)))
for module in ['NLA.Proofs.RE05.OneCopyError', 'Reviewed.RE05']:
    visit(module)

def check():
    assert sha(freeze_path) == freeze_sha and sha(input_path) == input_sha
    for rec in inputs + freeze['new_sources'] + records + freeze['frozen_prerequisites'] + freeze['frozen_anchors']:
        assert sha(REPO / rec['path']) == rec['sha256'], rec['path']
    assert sha(HERE / 'Consumer.lean') == freeze['consumer_sha256']
    assert sha(HERE / 'NegativeControl.lean') == freeze['negative_control_sha256']
    assert sha(Path(__file__)) == freeze['driver_sha256']

check()
assert not OBJECTS.exists(), 'Empty private project output is required.'
for rec in records:
    p = SNAP / Path(rec['path']).relative_to('lean-statements')
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes((REPO / rec['path']).read_bytes())
(SNAP / '.lake').mkdir(exist_ok=True)
CACHE = (LIVE / '.lake/packages').resolve()
(SNAP / '.lake/packages').symlink_to(CACHE, target_is_directory=True)
binary = TOOL / 'lean-4.33.1-darwin_aarch64/bin/lean'
assert sha(binary) == '1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554'
package_heads = {p.name: subprocess.check_output(['git', '-C', str(p), 'rev-parse', 'HEAD'], text=True).strip() for p in sorted(CACHE.iterdir()) if (p / '.git').exists()}
assert package_heads['mathlib'] == '0df444a360eaa60ab8c11dca51a86af692955474'
assert package_heads['leancert'] == '621a43d7cf21f87872392a01e874f2f1dbddc926'
paths = [OBJECTS] + [p / '.lake/build/lib/lean' for p in sorted(CACHE.iterdir())
                     if (p / '.lake/build/lib/lean').is_dir()]
env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, paths)),
           PATH=str(binary.parent) + os.pathsep + os.environ['PATH'])
lock = dict(author='/root/recover_geometry', scope=freeze['scope'],
            freeze_sha256=freeze_sha, source_inputs=inputs,
            frozen_prerequisites=freeze['frozen_prerequisites'],
            frozen_anchors=freeze['frozen_anchors'],
            new_sources=freeze['new_sources'], fresh_project_closure=records,
            consumer_sha256=freeze['consumer_sha256'],
            negative_control_sha256=freeze['negative_control_sha256'],
            driver_sha256=freeze['driver_sha256'])
(OUT / 'source-lock.json').write_text(json.dumps(lock, indent=2) + '\n')
commands = []
with (OUT / 'source-build.log').open('w') as log:
    for rec in records:
        rel = Path(rec['path']).relative_to('lean-statements')
        dest = OBJECTS / rel.with_suffix('.olean')
        dest.parent.mkdir(parents=True, exist_ok=True)
        cmd = [str(binary), '-o', str(dest), str(SNAP / rel)]
        commands.append(cmd)
        result = subprocess.run(cmd, cwd=SNAP, env=env, stdout=log, stderr=subprocess.STDOUT)
        log.write(rec['module'] + ' EXIT ' + str(result.returncode) + '\n')
        log.flush()
        assert result.returncode == 0, rec['module']
positive = SNAP / 'Consumer.lean'
positive.write_bytes((HERE / 'Consumer.lean').read_bytes())
cmd = [str(binary), '-o', str(OBJECTS / 'Consumer.olean'), str(positive)]
commands.append(cmd)
with (OUT / 'consumer-build.log').open('w') as log:
    result = subprocess.run(cmd, cwd=SNAP, env=env, stdout=log, stderr=subprocess.STDOUT)
assert result.returncode == 0, OUT / 'consumer-build.log'
logs = (OUT / 'source-build.log').read_text() + (OUT / 'consumer-build.log').read_text()
assert 'sorryAx' not in logs
axioms = re.findall(r'depends on axioms: \[([^]]*)\]', logs)
assert all(set(x.strip() for x in a.split(',') if x.strip()) <=
           {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms)
negative = SNAP / 'NegativeControl.lean'
negative.write_bytes((HERE / 'NegativeControl.lean').read_bytes())
cmd = [str(binary), '-o', str(OBJECTS / 'NegativeControl.olean'), str(negative)]
commands.append(cmd)
with (OUT / 'negative-control.log').open('w') as log:
    neg = subprocess.run(cmd, cwd=SNAP, env=env, stdout=log, stderr=subprocess.STDOUT)
assert neg.returncode != 0 and 'sorryAx' in (OUT / 'negative-control.log').read_text()
check()
for rec in records:
    assert sha(SNAP / Path(rec['path']).relative_to('lean-statements')) == rec['sha256']
result = dict(author='/root/recover_geometry', executed_at_utc=datetime.datetime.now(
                  datetime.timezone.utc).isoformat(), passed=True, scope=freeze['scope'],
              source_lock_sha256=sha(OUT / 'source-lock.json'), freeze_sha256=freeze_sha,
              new_sources=len(freeze['new_sources']), fresh_project_sources=len(records),
              kernel_commands=len(commands),
              explicit_positive_assertions=(HERE / 'Consumer.lean').read_text().count('#assert_trust kernel'),
              project_objects_reused=False, pinned_external_package_objects_reused=True,
              original_model_review_registry_pins_and_frozen_prerequisites_exact=True,
              standard_axioms_only=True, negative_control_rejected=True,
              actual_same_plan_residual_normal_equation=True,
              cauchy_coefficient_error_bound=True, analysis_optimum_chosen_before_all_plans=True,
              conditional_original_output_squared_error_bound=True,
              half_Gram_and_offset_imply_relative_squared_error=True, zero_optimum_exact=True,
              original_plan_never_regenerated_on_fold_basis=True, division_by_optimum=False,
              full_RE05_Target_proved=False, probability_success_proved=False,
              compiler=subprocess.check_output([str(binary), '--version'], text=True).strip(),
              compiler_binary_sha256=sha(binary), external_package_heads=package_heads, commands=commands,
              evidence=[dict(path=str(p.relative_to(OUT)), sha256=sha(p)) for p in
                        [OUT / 'source-build.log', OUT / 'consumer-build.log',
                         OUT / 'negative-control.log', positive, negative]])
(OUT / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2), flush=True)
