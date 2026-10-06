#!/usr/bin/env python3
"""Read-only audit of the completed IE-06 local validation evidence.
No Lean build is launched and no frozen input is modified.
"""
from pathlib import Path
import hashlib, json, re, subprocess, os

project = Path(__file__).resolve().parents[1]
repo = project.parents[2]
attempt = project / 'verification/local/attempt-0i_0ibma'
snapshot = attempt / 'source'
receipt_path = attempt / 'result.json'
if not receipt_path.exists():
    raise SystemExit('Final receipt is not present; no execution review written.')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
r = json.loads(receipt_path.read_text())
receipt_hash = sha(receipt_path)
assert r['pass'] and r['source_unchanged']
for key in ['compare_solution_requested', 'comparator_executed', 'comparator_core_executed',
            'actual_targets_kernel_proof_checked', 'ie06_targets_proved',
            'challenge_holes_are_reference_signatures_only', 'own_output_directory_removed']:
    assert r[key] is True, key
for key in ['authoritative_linux_comparator', 'full_comparator_executed',
            'authoritative_linux_sandbox', 'exporter_executed', 'raw_kernel_replay_executed']:
    assert r[key] is False, key
assert r['phase'] == 'local actual Solution proof comparison'
assert '--compare-solution' in r['argv'] and '--infrastructure-only' not in r['argv']
assert 'version 4.33.1,' in r['lean_version']
assert len(r['commands']) > 0
lean = Path(r['commands'][0]['argv'][0])
assert sha(lean) == r['lean_executable_sha256']

for rel, info in r['inputs'].items():
    src, saved = project / rel, snapshot / rel
    assert not src.is_symlink() and not saved.is_symlink(), rel
    assert sha(src) == sha(saved) == info['sha256'], rel
    assert src.stat().st_size == saved.stat().st_size == info['bytes'], rel
assert r['inputs']['verification/check_local.py']['sha256'] == 'b0fd644cd88d1e6dce576e435a48ed53ce7878147255ed6c95e07ea7002426ce'

lean_inputs = {rel for rel in r['inputs'] if rel.endswith('.lean')}
expected_inputs = {str(p.relative_to(project)) for p in (project / 'NLA').rglob('*.lean')}
expected_inputs |= {str(p.relative_to(project)) for p in project.glob('*.lean')}
if (project / 'verification/Inspect.lean').is_file():
    expected_inputs.add('verification/Inspect.lean')
assert lean_inputs == expected_inputs
concrete = sorted(p for p in lean_inputs if Path(p).name != 'Challenge.lean' and Path(p).parts[0] != 'verification')
module_names = sorted(str(Path(p).with_suffix('')).replace(os.sep, '.') for p in concrete)
assert sorted(r['generated_audit']['modules']) == module_names
assert sha(snapshot / 'AuditConcrete.lean') == r['generated_audit']['sha256']
audit_source = (snapshot / 'AuditConcrete.lean').read_text()
assert 'collectAxioms name' in audit_source and 'localModules.contains moduleName' in audit_source
assert 'unless allowed.contains axiomName' in audit_source
assert 'let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]' in audit_source
for rel in concrete:
    assert not re.search(r'^\s*(?:public\s+)?import\s+Challenge\b', (snapshot / rel).read_text(), re.M), rel

assert r['dependencies_before'] == r['dependencies_after']
manifest = json.loads((snapshot / 'lake-manifest.json').read_text())
pins = {p['name']: p['rev'] for p in manifest['packages']}
assert {d['name']: d['revision'] for d in r['dependencies_before']} == pins
for dep in r['dependencies_before']:
    assert dep['tracked_sources_clean']
    directory = Path(dep['directory'])
    head = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
    dirty = subprocess.check_output(['git', '-C', str(directory), 'status', '--porcelain', '--untracked-files=no'], text=True).strip()
    assert head == dep['revision'] and not dirty, dep['name']

commands = {c['source']: c for c in r['commands']}
assert len(commands) == len(r['commands'])
expected_generated = {'AuditConcrete.lean', 'RejectSorry.lean', 'RejectNative.lean',
                      'Export/Parse.lean', 'Comparator/Util.lean', 'Comparator/Axioms.lean',
                      'Comparator/Compare.lean', 'CompareSolution.lean'}
assert set(commands) == lean_inputs | expected_generated
warnings = {}
for rel, c in commands.items():
    assert c['expectation_met'], rel
    log = attempt / c['log']
    assert sha(log) == c['log_sha256'], rel
    assert c['argv'][0] == str(lean) and c['argv'][-1] == rel, rel
    body = log.read_text()
    wc = body.count('warning:')
    if wc:
        warnings[rel] = wc
    if rel in {'RejectSorry.lean', 'RejectNative.lean'}:
        assert not c['expected_success'] and c['exit_code'] != 0, rel
    else:
        assert c['expected_success'] and c['exit_code'] == 0, rel
        assert 'error:' not in body, rel
    if rel == 'CompareSolution.lean':
        assert c['argv'] == [str(lean), '--run', rel]
    else:
        assert '-o' in c['argv'] and '-i' in c['argv'], rel
assert '#assert_trust: \'rejectSorry\' depends on sorry or unrecognized axioms' in (attempt / commands['RejectSorry.lean']['log']).read_text()
assert '#assert_trust kernel: \'rejectNative\' is not kernel-clean' in (attempt / commands['RejectNative.lean']['log']).read_text()
for rel, info in r['generated_controls'].items():
    assert sha(snapshot / rel) == info['sha256'], rel

names = [
 'NLA.IE06.squareRootUpperBound', 'NLA.IE06.schurSubpolynomialTail',
 'NLA.IE06.gaussianMatrix_probability', 'NLA.IE06.exceedanceEvent_measurable',
 'NLA.IE06.admissiblePath_exists', 'NLA.IE06.gaussianMatrix_singular_null']
expected_config = {'challenge_module':'Challenge','solution_module':'Solution',
 'theorem_names':names,'definition_names':[],
 'permitted_axioms':['propext','Classical.choice','Quot.sound']}
assert r['comparator_targets'] == json.loads((snapshot/'comparator.json').read_text()) == expected_config
# Evaluating only the already-reviewed checker definitions creates no files: its
# __main__ entry point is disabled, and comparator_runner is a pure generator.
ns = {'__name__':'independent_checker_read', '__file__':str(snapshot/'verification/check_local.py')}
exec(compile((snapshot/'verification/check_local.py').read_text(), str(snapshot/'verification/check_local.py'), 'exec'), ns)
runner = snapshot/'CompareSolution.lean'
assert runner.read_text() == ns['comparator_runner'](expected_config)
assert sha(runner) == r['generated_solution_comparator']['sha256']
assert r['generated_solution_comparator']['module_environments'] == 'separate importModules calls'
comparison = (attempt / commands['CompareSolution.lean']['log']).read_text()
for name in names:
    assert comparison.count('PASS actual theorem statement and referenced definitions: '+name+'\n') == 1
    assert comparison.count('PASS actual theorem transitive proof axioms: '+name+'\n') == 1
assert comparison.count('PASS ') == 12
assert comparison.count('All six actual IE-06 Challenge/Solution theorem comparisons and axiom checks passed.') == 1

lock_file = snapshot/'verification/comparator-source-lock.json'
assert sha(lock_file) == r['comparator_source_lock']['sha256']
assert lock_file.stat().st_size == r['comparator_source_lock']['bytes']
assert sha(repo/'tools/lean/source-lock.json') == sha(lock_file)
lock = {e['destination']:e for e in json.loads(lock_file.read_text())['files']}
assert len(r['comparator_pinned_sources']) == 5
pinned_pairs = ns['COMPARATOR_PINNED'] + [('.tools/comparator/LICENSE','LICENSE-COMPARATOR')]
assert set(r['comparator_pinned_sources']) == {new for old,new in pinned_pairs}
for old,new in pinned_pairs:
    info = r['comparator_pinned_sources'][new]
    assert info['source'] == 'eigenvalues-and-inverse-problems/IS-03/lean/verification/linux-2026-09-12/source/forsythe/'+old
    assert info['sha256'] == lock[old]['sha256'] and info['bytes'] == lock[old]['bytes']
for rel, info in r['comparator_pinned_sources'].items():
    src, saved = repo/info['source'], snapshot/rel
    assert sha(src) == sha(saved) == info['sha256'], rel
    assert src.stat().st_size == saved.stat().st_size == info['bytes'], rel
    assert any(e['sha256']==info['sha256'] and e['bytes']==info['bytes'] for e in lock.values()), rel
shared = json.loads((snapshot/'verification/tooling-lock.json').read_text())['shared_tools']
for rel, info in shared.items():
    assert sha(repo/rel)==info['sha256'], rel

concrete_log = (attempt / commands['AuditConcrete.lean']['log']).read_text()
matches = re.findall(r'All (\d+) concrete local declarations have permitted transitive axioms\.', concrete_log)
assert len(matches) == 1
build_dir = Path(r['lean_path'].split(os.pathsep)[0])
assert not build_dir.exists()
assert r['removed_own_objects']
assert sha(receipt_path)==receipt_hash
latest = json.loads((attempt.parent/'latest.json').read_text())
assert latest == {'attempt':attempt.name, 'result_sha256':receipt_hash}
result = {
 'attempt': str(attempt.relative_to(project)), 'receipt_sha256': receipt_hash,
 'auditor_sha256': sha(Path(__file__)), 'pass': True,
 'input_files':len(r['inputs']), 'lean_source_modules':len(lean_inputs),
 'concrete_modules':len(concrete), 'concrete_declarations_audited':int(matches[0]),
 'recorded_commands':len(commands), 'successful_commands':sum(c['exit_code']==0 for c in commands.values()),
 'expected_rejection_commands':2, 'actual_comparator_checks':12, 'actual_targets':6,
 'pinned_dependency_packages':len(pins), 'copied_locked_comparator_files':5,
 'recorded_removed_output_files':len(r['removed_own_objects']),
 'latest_pointer_matches':True, 'total_warnings':sum(warnings.values()),
 'existing_vendor_warnings':sum(v for k,v in warnings.items() if '/Vendor/' in k),
 'challenge_reference_warnings':warnings.get('Challenge.lean',0),
 'deliberate_sorry_control_warnings':warnings.get('RejectSorry.lean',0),
 'warnings_by_module':warnings,
 'limitations':'Local macOS kernel compilation and locked Comparator core with trusted pinned compiled external dependency caches; no Linux sandbox, complete exporter Comparator, exporter execution, or raw kernel replay. Removed temporary object digests are receipt records, not independently recomputable after deletion.'
}
(project/'reviews/final-validation-independent-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
