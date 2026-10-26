#!/usr/bin/env python3
"""Immutable source/input preflight only; no Lean, CI or review acceptance."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo', type=Path, required=True)
p.add_argument('--head', required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
PROJECT = 'tensor-computations/TR-26/lean/'
DOC = 'docs/lean/proofs/TR-26/campaign-2026-10-26/'
SOURCE = 'ecc597cb68b65b473aecce9ac635e27d35c09694'
SUPERSEDED = 'f0fc0691c3496822e330894de60a9d6e94b7890a'
NAMES = ['NLA.Proofs.TR26.nonisotropic_degree', 'NLA.Proofs.TR26.isotropic_degree', 'NLA.Proofs.TR26.target']
git = lambda *v: subprocess.check_output(['git', *v], cwd=a.repo)
read = lambda c, q: git('show', c + ':' + q)
sha = lambda b: hashlib.sha256(b).hexdigest()
checks = []

def check(name, passed):
    checks.append(dict(name=name, passed=bool(passed)))
    if not passed:
        raise AssertionError(name)

error = None
try:
    paths = git('ls-tree', '-r', '--name-only', a.head, PROJECT).decode().splitlines()
    bodies = {q.removeprefix(PROJECT): read(a.head, q) for q in paths}
    hashes = {q: sha(b) for q, b in bodies.items()}
    lock = json.loads(bodies['PACKAGE_LOCK.json'])
    check('exact857-Git-inputs-856-complete-lock', len(bodies) == 857 and len(lock['files']) == 856 and
          set(lock['files']) == set(bodies) - {'PACKAGE_LOCK.json'})
    for q, e in lock['files'].items():
        check('locked-input:' + q, hashes[q] == e['sha256'] and len(bodies[q]) == e['bytes'])
    binding = json.loads(bodies['reviews/FULL_SOURCE_REVIEW_BINDINGS.json'])
    check('exact332-existing-review-bindings', len(binding['files']) == 332)
    for e in binding['files']:
        check('existing-review-binding:' + e['path'], hashes[e['path']] == e['sha256'] and
              len(bodies[e['path']]) == e['bytes'])
    omitted = 'reviews/full-target-review/verification/__pycache__/reproduce.cpython-313.pyc'
    check('explicit-omission-absent-from-Git-and-lock',
          [e['path'] for e in binding['omitted_regenerable_artifacts']] == [omitted] and
          omitted not in bodies and omitted not in lock['files'])
    freeze = json.loads(read(SOURCE, DOC + 'FULL_TARGET_SOURCE_FREEZE.json'))
    shared = freeze['proof_inputs'] + freeze['shared_inputs']
    check('exact77-proofs-plus3-shared-sources', len(freeze['proof_inputs']) == 77 and len(shared) == 80)
    for e in shared:
        q = e['path'].removeprefix('lean-statements/')
        b = read(SOURCE, e['path'])
        check('exact-ECC-source-copy:' + q, b == bodies[q] and hashes[q] == e['sha256'] and len(b) == e['bytes'])
    runtime = [q for q in bodies if q.endswith('.lean') and not q.startswith('reviews/')]
    check('exact84-runtime-Lean-inputs', len(runtime) == 84)
    executable = runtime + ['controls/ChallengeTrustRejection.lean.txt',
        'controls/CustomAxiomRejection.lean.txt', 'controls/DefinitionKindRejection.lean.txt',
        'comparator.json', 'lake-manifest.json', 'lakefile.toml', 'lean-toolchain', 'reproduce.py']
    check('exact92-executable-pin-inputs', len(executable) == 92)
    for q in executable:
        check('unchanged-executable-pin-input:' + q, bodies[q] == read(SUPERSEDED, PROJECT + q))
    cfg = json.loads(bodies['comparator.json'])
    check('exact-three-exports-no-replaceable-definitions', cfg == dict(challenge_module='Challenge',
          solution_module='Solution', theorem_names=NAMES, definition_names=[],
          permitted_axioms=['propext', 'Classical.choice', 'Quot.sound']))
    original = json.loads(read(a.head, DOC + 'preproof/INPUT_LOCK.json'))
    check('exact24-original-inputs', len(original['reviewed_inputs']) == 24)
    for e in original['reviewed_inputs']:
        b = read(a.head, e['path'])
        check('preserved-original:' + e['path'], sha(b) == e['sha256'] and len(b) == e['bytes'])
except Exception as exc:
    error = str(exc)
report = dict(scope='Author immutable input preflight only; no Lean/Linux/Comparator execution or independent review claim',
              head=a.head, source=SOURCE, passed=error is None and all(c['passed'] for c in checks),
              error=error, checks=checks, check_count=len(checks), driver_sha256=sha(Path(__file__).read_bytes()))
a.output.parent.mkdir(parents=True, exist_ok=True)
a.output.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: report[k] for k in ['head', 'passed', 'error', 'check_count']}, indent=2))
raise SystemExit(0 if report['passed'] else 1)
