#!/usr/bin/env python3
"""Independent statement-only inspection; never imports the author's checker."""
from pathlib import Path
import datetime, hashlib, json, os, re, subprocess, tempfile, time

project = Path(__file__).resolve().parents[2]
repo = project.parents[2]
evidence = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
freeze_path = project / 'reviews/statement-freeze.json'
freeze_sha = '0243fca8b3e04b5dd3ee9d79f3fa9e25a4c706519089fbece2984178d11f7804'
assert sha(freeze_path) == freeze_sha
freeze = json.loads(freeze_path.read_text())

def check_inputs():
    assert not (project / 'Solution.lean').exists()
    assert sorted(str(p.relative_to(project)) for p in (project / 'NLA').rglob('*.lean')) == ['NLA/MI03/Definitions.lean']
    for rel, expected in freeze['files'].items():
        assert sha(project / rel) == expected, rel
    for rel, expected in freeze['source_files'].items():
        assert sha(repo / rel) == expected, rel
        original = subprocess.check_output(['git', 'show', freeze['base_commit'] + ':' + rel], cwd=repo)
        assert hashlib.sha256(original).hexdigest() == expected, rel

check_inputs()
defs = (project / 'NLA/MI03/Definitions.lean').read_text()
challenge = (project / 'Challenge.lean').read_text()
definitions = re.findall(r'^(?:def|abbrev) (\w+)', defs, re.M)
exports = re.findall(r'^theorem (\w+)', challenge, re.M)
assert len(definitions) == 20 and len(exports) == 8
assert len(re.findall(r'^\s+sorry\s*$', challenge, re.M)) == 8
assert not re.search(r'\b(?:axiom|sorry|admit|native_decide|implemented_by)\b', defs)
config = json.loads((project / 'comparator.json').read_text())
assert config['theorem_names'] == ['NLA.MI03.' + s for s in exports]
assert config['definition_names'] == []
assert set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
pins = []
for p in json.loads((project / 'lake-manifest.json').read_text())['packages']:
    local = project / '.lake/packages' / p['name']
    rev = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=local, text=True).strip()
    dirty = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=local, text=True)
    assert rev == p['rev'] and not dirty, p['name']
    pins.append({'name': p['name'], 'revision': rev, 'tracked_sources_clean': True})
(evidence / 'dependency-pins.json').write_text(json.dumps(pins, indent=2) + '\n')

intro = '''/- Independent semantic inspection, not a proof implementation. -/
import Challenge
import LeanCert.Tactic.Verification
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option leancert.trust "kernel"
set_option pp.explicit true
set_option pp.universes true
open scoped BigOperators Classical ComplexOrder MatrixOrder

'''
inspection = intro
for name in definitions:
    inspection += f'#print NLA.MI03.{name}\n#assert_trust kernel NLA.MI03.{name}\n#print axioms NLA.MI03.{name}\n\n'
for name in exports:
    inspection += f'#check NLA.MI03.{name}\n#print axioms NLA.MI03.{name}\n\n'
inspection += '''
#print Matrix.PosSemidef
#print Matrix.instPartialOrder
#print Matrix.le_iff
#print Complex.le_def
#print Matrix.toEuclideanCLM
#print CFC.sqrt
#print CFC.abs
#print IsLeast
#check IsLeast.csInf_eq
#check Matrix.posSemidef_conjTranspose_mul_self
#check CFC.sqrt_mul_sqrt_self
#check CFC.sqrt_unique
#check CFC.abs_mul_abs
#check CFC.norm_abs
#check CStarAlgebra.norm_le_one_iff_of_nonneg
#check Matrix.l2_opNorm_toEuclideanCLM
#check Matrix.toEuclideanCLM_toLp
#check EuclideanSpace.norm_sq_eq
#check InnerProductSpace.norm_rankOne
#check InnerProductSpace.symm_toEuclideanLin_rankOne
#check Complex.isPrimitiveRoot_exp
#check IsPrimitiveRoot.norm'_eq_one
#check IsPrimitiveRoot.geom_sum_eq_zero
#synth PartialOrder (NLA.MI03.Mat 2)
#synth Norm (EuclideanSpace ℂ (Fin 2))
set_option pp.all true in
#print NLA.MI03.operatorNorm
set_option pp.all true in
#print NLA.MI03.matrixModulus
set_option pp.all true in
#print NLA.MI03.OddContractionConjecture
set_option pp.all true in
#check NLA.MI03.sharpness_witness
set_option pp.all true in
#check NLA.MI03.sharp_constant
'''
(evidence / 'Inspect.lean').write_text(inspection)

lake = '/Users/georgestepaniants/.elan/bin/lake'
lean = '/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean'
raw = subprocess.check_output([lake, 'env', 'printenv', 'LEAN_PATH'], cwd=project, text=True).strip()
prefix = Path(tempfile.mkdtemp(prefix='mi03-statement-referee1-', dir='/tmp/nla-lean-formalization/independent-prefixes'))
old = (project / '.lake/build/lib/lean').resolve()
deps = [p for p in raw.split(os.pathsep) if p and (project / p).resolve() != old]
assert all((project / p).resolve() != old for p in deps)
env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(prefix), *deps]))
records = []
for module, source in [('NLA/MI03/Definitions', project / 'NLA/MI03/Definitions.lean'), ('Challenge', project / 'Challenge.lean'), ('Inspect', evidence / 'Inspect.lean')]:
    out = prefix / (module + '.olean')
    out.parent.mkdir(parents=True, exist_ok=True)
    log = evidence / (module.rsplit('/', 1)[-1] + '.log')
    cmd = [lean, '-o', str(out), '-i', str(out.with_suffix('.ilean')), str(source)]
    t = time.monotonic()
    with log.open('w') as stream:
        stream.write('COMMAND ' + json.dumps(cmd) + '\n')
        stream.flush()
        run = subprocess.run(cmd, cwd=project, env=env, stdout=stream, stderr=subprocess.STDOUT)
    rec = {'module': module, 'source_sha256': sha(source), 'command': cmd, 'exit_code': run.returncode, 'seconds': round(time.monotonic() - t, 3), 'log_sha256': sha(log)}
    records.append(rec)
    print(json.dumps(rec), flush=True)
    if run.returncode:
        break
(evidence / 'fresh-checks.json').write_text(json.dumps({'prefix': str(prefix), 'excluded_old_project_output': str(old), 'lean_path': env['LEAN_PATH'], 'commands': records}, indent=2) + '\n')
assert len(records) == 3 and all(r['exit_code'] == 0 for r in records)
assert (evidence / 'Challenge.log').read_text().count('declaration uses `sorry`') == 8
assert 'warning:' not in (evidence / 'Definitions.log').read_text()
assert 'warning:' not in (evidence / 'Inspect.log').read_text()
reports = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", (evidence / 'Inspect.log').read_text())
assert len(reports) == 28, len(reports)
whitelist = {'propext', 'Classical.choice', 'Quot.sound'}
parsed = []
for i, (name, text) in enumerate(reports):
    axioms = [re.sub(r'\.\{[^}]*\}', '', a.strip()) for a in text.split(',') if a.strip()]
    assert set(axioms) <= whitelist | ({'sorryAx'} if i >= 20 else set()), name
    assert (i < 20) == ('sorryAx' not in axioms), name
    parsed.append({'name': name, 'axioms': axioms, 'intentional_placeholder': i >= 20})
(evidence / 'axiom-report.json').write_text(json.dumps(parsed, indent=2) + '\n')
check_inputs()
result = {'status': 'PASS: statement-only source and semantic checks; no proof checked or claimed', 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'freeze_sha256': freeze_sha, 'frozen_project_files_unchanged': len(freeze['files']), 'original_sources_match_base': len(freeze['source_files']), 'base_commit': freeze['base_commit'], 'fresh_sources_passed': len(records), 'definition_kernel_assertions': 20, 'definition_axioms_within_standard_three': True, 'all_eight_placeholders_expose_sorryAx': True, 'clean_dependency_pins': len(pins), 'scope': 'macOS fresh project elaboration with pinned cached dependencies; no Linux Comparator or complete Mathlib rebuild', 'proof_implementation_absent': True}
(evidence / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
print('PASS ' + sha(evidence / 'result.json'), flush=True)
