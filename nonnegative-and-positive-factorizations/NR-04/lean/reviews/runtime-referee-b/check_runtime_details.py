"""Additional independent runtime evidence checks; no compiler execution."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

D = Path(__file__).resolve().parents[2]
E = D / 'verification/NR04-linux-20260919'
spec = json.loads((E / 'SPEC.json').read_text())
W = Path(spec['worktree'])
P = spec['project']
proof = spec['proof']
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def blob(path):
    return subprocess.check_output(['git', 'show', f'{proof}:{path}'], cwd=W)


snapshot = json.loads((D / 'final-review-packets/NR04-v1/REVIEW-SNAPSHOT.json').read_text())
for path, digest in snapshot['Lean_sources'].items():
    assert hashlib.sha256(blob(f'{P}/{path}')).hexdigest() == digest
config = json.loads(blob(f'{P}/comparator.json'))
manifest = json.loads(blob(f'{P}/lake-manifest.json'))
lock = json.loads(blob('tools/lean/source-lock.json'))
assert len(lock['files']) == 58
archive = D / 'publication/PF03/docs/lean/verification/2026-09-12/source/forsythe'
locked_sources = {}
for path in ['scripts/strict_landrun.py', 'reproduction/checks/PinnedReplayProbe.lean',
             'reproduction/checks/run_replay.sh', 'reproduction/checks/sandbox_probe.py',
             'reproduction/checks/comparator_regressions.py']:
    entry = next(e for e in lock['files'] if e['destination'] == path)
    p = archive / path
    assert p.stat().st_size == entry['bytes'] and sha(p) == entry['sha256']
    locked_sources[str(p)] = sha(p)

# Reproduce the harness's exact, checked text-only noninteractive adaptation.
probe = (archive / 'reproduction/checks/sandbox_probe.py').read_text()
replacements = [
    ('"--pty"', '"--pipe"', 2),
    ('"--property=RestrictAddressFamilies=~AF_UNIX"',
     '"--property=RestrictAddressFamilies=~AF_UNIX", "--property=RuntimeMaxSec=40"', 2),
    ('subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)',
     'subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=45)', 2),
    ('\n                result = subprocess.run(command',
     '\n                print(f"START sandbox mode: {mode}", flush=True)\n                result = subprocess.run(command', 1),
    ('\n            result = subprocess.run(command',
     '\n            print(f"START sandbox negative case: {label}", flush=True)\n            result = subprocess.run(command', 1),
    ('landrun_args = ["--best-effort", "--ro", "/",',
     'landrun_args = ["--best-effort", "--rox", "/usr/bin/bwrap", "--ro", "/",', 1),
]
for old, new, count in replacements:
    assert probe.count(old) == count
    probe = probe.replace(old, new)
adapted_sha = hashlib.sha256(probe.encode()).hexdigest()

checks = []
for entry in spec['runs']:
    root = E / entry['kind']
    provenance = json.loads((root / 'GITHUB-PROVENANCE.json').read_text())
    receipt_file = next((root / 'artifact').rglob('result.json'))
    receipt = json.loads(receipt_file.read_text())
    logs = receipt_file.parent
    assert receipt['tool_receipt']['ci_sandbox_probe_sha256'] == adapted_sha
    assert receipt['tool_receipt']['platform'].startswith('Linux-')
    assert receipt['tool_receipt']['go_version'] == 'go version go1.27.1 linux/amd64'
    dependency_log = (logs / 'dependencies.log').read_text()
    for package in manifest['packages']:
        assert f"info: {package['name']}: checking out revision '{package['rev']}'" in dependency_log
    assert dependency_log.rstrip().endswith('EXIT_STATUS=0')
    assert (logs / 'mathlib-cache.log').read_text().rstrip().endswith('EXIT_STATUS=0')
    sandbox = (logs / 'sandbox.log').read_text()
    assert sandbox.count('Sandbox UID: 1001') == 2
    for marker in [
        'PASS outside .lake write-open: denied', 'PASS outside .lake truncate: denied',
        'PASS outside .lake read-only truncate-open: denied', 'PASS symlink from .lake to outside write: denied',
        'PASS outside .lake creation: denied', 'PASS user namespace: private', 'PASS pid namespace: private',
        'PASS mnt namespace: private', 'PASS net namespace: private', 'PASS ipc namespace: private',
        'PASS uts namespace: private', 'PASS host parent: absent from private /proc',
        'PASS host parent signal lookup: denied', 'PASS host loopback listener: unreachable',
        'PASS AF_UNIX socket creation: denied', 'PASS effective capabilities: none',
        'PASS no_new_privs: set', 'PASS nested namespace write attempt: rejected exit=1']:
        assert sandbox.count(marker) == 2, marker
    for marker in ['PASS build .lake write: allowed', 'PASS export .lake write-open: denied',
                   'PASS export .lake truncate: denied', 'NEGATIVE unknown option: exit=2',
                   'NEGATIVE unexpected --rw: exit=2', 'NEGATIVE unexpected --rwx: exit=2',
                   'NEGATIVE relative --rwx: exit=2']:
        assert sandbox.count(marker) == 1
    kernel = (logs / 'kernel-controls.log').read_text()
    for marker in ['RETURN honest_with_inductives_and_quotients: accepted',
                   "RETURN invalid_raw_proof: rejected: while replaying declaration 'PinnedReplayProbe.invalid'",
                   "(kernel) declaration type mismatch, 'PinnedReplayProbe.invalid' has type",
                   'RETURN quotient_postcheck_mismatch: rejected: Quotient constant mismatch on: Quot.lift']:
        assert marker in kernel
    regression = (logs / 'comparator-controls.log').read_text()
    for case, status in [('simple_match', 0), ('simple_mismatch', 1), ('simple_axiom_issue', 1),
                         ('simple_kind_mismatch', 1), ('type_mismatch', 1)]:
        assert f'PASS {case}: exit {status}, expected {status}; required phase:' in regression
    comparator = (logs / 'comparator.log').read_text()
    exports = re.findall(r'Exporting #\[(.*?)\] from (Challenge|Solution)', comparator)
    assert {module for _, module in exports} == {'Challenge', 'Solution'} and len(exports) == 2
    for listed, module in exports:
        assert all(name in {n.strip() for n in listed.split(',')} for name in config['theorem_names'])
    solution_axioms = dict(re.findall(r"info: Solution\.lean:\d+:\d+: '([^']+)' depends on axioms: \[([^\]]*)\]", comparator))
    assert set(solution_axioms) == set(config['theorem_names'])
    assert all(set(a.strip() for a in values.split(',')) == set(config['permitted_axioms']) for values in solution_axioms.values())
    select = next(j for j in provenance['jobs']['jobs'] if j['name'] == 'select')
    verify = next(j for j in provenance['jobs']['jobs'] if j['name'].startswith('verify ('))
    for job in [select, verify]:
        text = (root / f"official-job-{job['id']}.raw.log").read_text()
        assert receipt['repository_commit'] in text
    selected = (root / f"official-job-{select['id']}.raw.log").read_text()
    assert '{"include":[{"id":"NR-04","project":"nonnegative-and-positive-factorizations/NR-04/lean"}]}' in selected
    joblog = (root / f"official-job-{verify['id']}.raw.log").read_text()
    assert 'PASS: fresh Comparator run and all controls.' in joblog
    assert 'lean-NR-04.zip successfully finalized.' in joblog
    checks.append({'kind': entry['kind'], 'run_id': entry['run_id'],
                   'sandbox_uids': [1001, 1001], 'all_sandbox_cases_checked': True,
                   'all_kernel_and_comparator_controls_checked': True,
                   'all_pinned_dependency_checkout_logs_matched': len(manifest['packages']),
                   'actual_solution_axiom_reports': len(solution_axioms),
                   'official_selected_projects': ['NR-04'],
                   'official_job_log_checkout_and_finalization_matched': True})

output = {'reviewer': spec['reviewer'], 'scope': 'Independent read-only source/log/hash audit; no compiler',
          'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'verdict': 'PASS', 'reviewed_frozen_Lean_sources_match_proof_commit': len(snapshot['Lean_sources']),
          'locked_verifier_source_files': locked_sources, 'adapted_sandbox_probe_sha256': adapted_sha,
          'source_lock_entries_enforced_by_unchanged_harness': len(lock['files']),
          'runs': checks, 'script_sha256': sha(Path(__file__))}
(E / 'INDEPENDENT-DETAILS.json').write_text(json.dumps(output, indent=2) + '\n')
print(json.dumps(output, indent=2))
