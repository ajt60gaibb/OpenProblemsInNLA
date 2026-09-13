"""Independent TR-15 final referee 1: immutable inputs and fresh local Lean checks.
Uses the campaign's pinned local dependency artifacts; not Linux Comparator.
Candidate statements and proofs are never edited by this driver.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import platform
import re
import subprocess
import tempfile
import time

OUT = Path(__file__).resolve().parent
PROJECT = OUT.parents[1]
REPO = PROJECT.parents[2]
BIN = Path('/Users/georgestepaniants/.elan/toolchains/leanprover--lean4---v4.33.1/bin')

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def save(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2) + '\n')

def capture(argv, cwd=PROJECT):
    return subprocess.check_output(argv, cwd=cwd, text=True).strip()

freeze_path = PROJECT / 'reviews/proof-freeze.json'
assert digest(freeze_path) == '1263937a8aeef77192d2eaf434457c36abefc77a7aefbd25fdf0dbd854ed7f6c'
freeze = json.loads(freeze_path.read_text())
inputs = {}
for field, base in [('files', PROJECT), ('source_files', REPO)]:
    for rel, expected in freeze[field].items():
        path = base / rel
        assert digest(path) == expected, rel
        inputs[str(path.relative_to(REPO))] = expected
        if field == 'source_files':
            blob = subprocess.check_output(['git', 'show', freeze['base_commit'] + ':' + rel], cwd=REPO)
            assert hashlib.sha256(blob).hexdigest() == expected
assert len(freeze['files']) == 75 and len(freeze['source_files']) == 6
save('inputs-before.json', {'proof_freeze_sha256': digest(freeze_path), 'inputs': inputs})

pins = []
for package in json.loads((PROJECT / 'lake-manifest.json').read_text())['packages']:
    folder = PROJECT / '.lake/packages' / package['name']
    rev = capture(['git', 'rev-parse', 'HEAD'], folder)
    dirty = capture(['git', 'status', '--porcelain'], folder)
    assert rev == package['rev'] and dirty == '', package['name']
    pins.append({'name': package['name'], 'expected': package['rev'], 'actual': rev, 'status': dirty})
assert len(pins) == 10
save('dependency-pins.json', pins)

def signatures(text):
    return {name: ' '.join(body.split()) for name, body in
            re.findall(r'theorem\s+(\w+)\s+(.*?)\s*:=\s*by', text, re.S)}

challenge = signatures((PROJECT / 'Challenge.lean').read_text())
solution = signatures((PROJECT / 'Solution.lean').read_text())
config = json.loads((PROJECT / 'comparator.json').read_text())
assert challenge == solution
assert set(solution) == {name.removeprefix('NLA.TR15.') for name in config['theorem_names']}
assert len(solution) == 7 and config['definition_names'] == []
assert set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
save('signatures.json', {'scope': 'Normalized source identity plus separate actual-environment inspection; Linux Comparator pending', 'signatures': solution})
for rel in ['NLA/TR15/Definitions.lean', 'NLA/TR15/Proof.lean', 'Solution.lean']:
    source = (PROJECT / rel).read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', source), rel
    assert not re.search(r'^import\s+Challenge\b', source, re.M), rel

parent = Path('/tmp/nla-lean-formalization/independent-prefixes')
parent.mkdir(parents=True, exist_ok=True)
prefix = Path(tempfile.mkdtemp(prefix='tr15-proof-referee1-', dir=parent))
original = capture([str(BIN / 'lake'), 'env', 'printenv', 'LEAN_PATH'])
old_build = (PROJECT / '.lake/build/lib/lean').resolve()
parts = original.split(os.pathsep)
filtered = [str(Path(item).resolve()) for item in parts if Path(item).resolve() != old_build]
assert len(filtered) + 1 == len(parts)
env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(prefix), *filtered]))
result = {'reviewer': '/root/formal_review_standards', 'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'platform': platform.platform(), 'lean_version': capture([str(BIN / 'lean'), '--version']),
          'fresh_prefix': str(prefix), 'LEAN_PATH': env['LEAN_PATH'],
          'excluded_project_artifacts': str(old_build), 'dependency_artifacts_reused': True,
          'linux_comparator': 'pending', 'commands': []}
jobs = [('NLA/TR15/Definitions.lean', 'definitions', 0),
        ('NLA/TR15/Proof.lean', 'proof', 0), ('Solution.lean', 'solution', 0),
        ('Challenge.lean', 'challenge', 7),
        ('reviews/proof-referee-1-evidence/Inspect.lean', 'inspection', 0)]
for rel, label, warning_count in jobs:
    output = prefix / Path(rel).with_suffix('.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    argv = [str(BIN / 'lean'), '-o', str(output), '-i', str(output.with_suffix('.ilean')), rel]
    print('START', label, flush=True)
    start = time.monotonic()
    proc = subprocess.run(argv, cwd=PROJECT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = OUT / (label + '.log')
    log.write_bytes(proc.stdout)
    result['commands'].append({'argv': argv, 'source_sha256': digest(PROJECT / rel),
        'exit_code': proc.returncode, 'elapsed_seconds': time.monotonic() - start,
        'log': log.name, 'log_sha256': digest(log),
        'olean_sha256': digest(output) if output.exists() else None})
    save('checks.json', result)
    print('END', label, proc.returncode, flush=True)
    assert proc.returncode == 0, proc.stdout.decode()
    assert proc.stdout.count(b'warning:') == warning_count, proc.stdout.decode()
    assert proc.stdout.count(b'declaration uses `sorry`') == warning_count

axiom_reports = []
for label in ['proof', 'solution']:
    for name, body in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", (OUT / (label + '.log')).read_text()):
        items = [item.strip() for item in body.split(',')]
        assert set(items) == {'propext', 'Classical.choice', 'Quot.sound'}
        axiom_reports.append({'declaration': name, 'axioms': items})
assert len(axiom_reports) == 15
inspection = (OUT / 'inspection.log').read_text()
assert inspection.count('REFEREE_REQUIRED ') == 14
assert 'of_decide_eq_true (id (Eq.refl true))' in inspection
assert 'LeanCert.Validity.verify_strict_upper_bound_dyadic_checked' in inspection
assert not any(name in inspection for name in ['sorryAx', 'Lean.ofReduceBool', 'Lean.trustCompiler'])
reached = int(re.search(r'REFEREE_VISITED (\d+)', inspection).group(1))
save('axiom-audit.json', {'fifteen_original_kernel_commands_passed': True, 'reports': axiom_reports,
    'reached_project_definitions_and_theorems_audited': reached,
    'all_reached_transitive_axioms_are_standard_only': True,
    'fourteen_material_dependencies_retained': True,
    'checked_LeanCert_term_retained_and_consumed': True})
for rel, expected in inputs.items():
    assert digest(REPO / rel) == expected, rel
assert digest(freeze_path) == '1263937a8aeef77192d2eaf434457c36abefc77a7aefbd25fdf0dbd854ed7f6c'
save('inputs-after.json', {'unchanged': True, 'inputs': inputs})
result['result'] = 'PASS: five fresh local source modules; fifteen standard-three kernel checks; complete dependency audit; all frozen inputs unchanged'
save('checks.json', result)
print(result['result'], flush=True)
