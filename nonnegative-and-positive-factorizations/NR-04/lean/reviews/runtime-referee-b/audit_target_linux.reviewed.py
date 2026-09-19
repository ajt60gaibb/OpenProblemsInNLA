"""Audit downloaded per-target GitHub artifacts; no Lean/Comparator execution.
Arguments: SPEC_JSON (problem, worktree, evidence, proof, project, runs).
"""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess
import sys

D = Path(__file__).resolve().parents[1]
spec = json.loads(Path(sys.argv[1]).read_text())
W = Path(spec['worktree']).resolve()
E = Path(spec['evidence']).resolve()
PROOF = spec['proof']
PROJECT = spec['project']
ID = spec['problem']
assert W.is_relative_to(D) and E.is_relative_to(D)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def blob(path):
    return subprocess.check_output(['git', 'show', f'{PROOF}:{path}'], cwd=W)

config = json.loads(blob(f'{PROJECT}/comparator.json'))
names = config['theorem_names']
assert names and len(names) == len(set(names)) and not config['definition_names']
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert set(config['permitted_axioms']) == allowed
paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', PROOF, '--', PROJECT], cwd=W, text=True).splitlines()
expected_inputs = {str(Path(p).relative_to(PROJECT)): hashlib.sha256(blob(p)).hexdigest() for p in paths}
assert expected_inputs and 'Solution.lean' in expected_inputs and 'Challenge.lean' in expected_inputs
shared = subprocess.check_output(['git', 'diff', '--name-only', spec['base'], PROOF, '--', 'tools/lean', 'docs/lean', '.github/workflows/lean-verification.yml'], cwd=W, text=True).strip()
assert not shared, ('shared verifier unexpectedly changed', shared)
lock = hashlib.sha256(blob('tools/lean/source-lock.json')).hexdigest()
results = []
for entry in spec['runs']:
    kind, run_id, repository = entry['kind'], entry['run_id'], entry['repository']
    root = E / kind
    api = json.loads((root / 'GITHUB-PROVENANCE.json').read_text())
    assert api['repository'] == repository
    run = api['run']
    assert run['id'] == run_id and run['head_sha'] == PROOF
    assert run['repository']['full_name'] == repository
    assert run['path'] == '.github/workflows/lean-verification.yml'
    assert run['status'] == 'completed' and run['conclusion'] == 'success'
    selected = [x for x in api['jobs']['jobs'] if x['name'].startswith('verify (')]
    assert len(selected) == 1
    job = selected[0]
    job_id = job['id']
    assert job['name'] == f'verify ({ID}, {PROJECT})'
    assert job['status'] == 'completed' and job['conclusion'] == 'success'
    step = next(x for x in job['steps'] if x['name'] == 'Fresh sandboxed statement, axiom and kernel verification')
    assert step['conclusion'] == 'success'
    artifacts = [a for a in api['artifacts']['artifacts'] if a['name'] == f'lean-{ID}']
    assert len(artifacts) == 1
    artifact = artifacts[0]
    assert not artifact['expired']
    assert artifact['workflow_run']['id'] == run_id
    assert 'sha256:' + sha(root / f'lean-{ID}.zip') == artifact['digest']
    assert (root / f'lean-{ID}.zip').stat().st_size == artifact['size_in_bytes']
    found = list((root / 'artifact').rglob('result.json'))
    assert len(found) == 1
    receipt_path = found[0]
    receipt = json.loads(receipt_path.read_text())
    assert receipt['result'] == 'comparator-accepted'
    assert receipt['project'] == PROJECT and receipt['config'] == config
    assert receipt['input_sha256'] == expected_inputs
    assert receipt['source_lock_sha256'] == lock
    tool = receipt['tool_receipt']
    assert tool['source_lock_sha256'] == lock
    assert tool['lean_toolchain'] == 'leanprover/lean4:v4.33.1'
    assert 'linux' in tool['lean_version'].lower()
    assert tool['forsythe_commit'] == '8d1b0c0545a77b40245e84705aa7d273e6c81e62'
    assert set(tool['executables']) == {'.tools/comparator/.lake/build/bin/comparator', '.tools/lean4export/.lake/build/bin/lean4export', '.tools/bin/landrun'}
    assert all(re.fullmatch('[0-9a-f]{64}', v) for v in tool['executables'].values())
    assert api['checked_commit']['sha'] == receipt['repository_commit']
    if kind == 'fork':
        assert receipt['repository_commit'] == PROOF
    else:
        checked = api['checked_commit']
        assert checked['sha'] == receipt['repository_commit']
        assert [p['sha'] for p in checked['parents']] == [spec['base'], PROOF], 'unexpected merge parents'
    assert run['head_repository']['full_name'] == 'sgstepaniants/OpenProblemsInNLA'
    assert run['event'] == ('push' if kind == 'fork' else 'pull_request')
    logs = receipt_path.parent
    checks = {
        'user-service.log': (0, ['systemd-run', '--user']),
        'sandbox.log': (0, ['Outer and export fixture contents unchanged; only designated build fixture written.']),
        'kernel-controls.log': (0, ['PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']),
        'comparator-controls.log': (0, ['PASS: all five Comparator regressions']),
        'negative-sorry.log': (1, ["Illegal axiom detected: 'sorryAx'"]),
        'negative-native.log': (1, ["Illegal axiom detected: 'checked._native.native_decide.ax_1_1'"]),
        'comparator.log': (0, ['Building Challenge', 'Building Solution', 'Running Lean default kernel on solution.', 'Lean default kernel accepts the solution', 'Your solution is okay!']),
    }
    log_records = {}
    for name, (code, markers) in checks.items():
        path = logs / name
        text = path.read_text()
        assert text.rstrip().endswith(f'EXIT_STATUS={code}'), name
        assert all(marker in text for marker in markers), name
        log_records[name] = {'sha256': sha(path), 'exit_code': code, 'required_markers': markers}
    text = (logs / 'comparator.log').read_text()
    assert 'XDG_RUNTIME_DIR=/run/user/1001' in text and 'systemd-run --user' in text
    reports = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        observed = {a.strip() for a in axioms.split(',') if a.strip()}
        reports.setdefault(name, []).append(sorted(observed))
    actual = {}
    for name in names:
        assert name in reports, name
        assert all(set(v) <= allowed for v in reports[name]), name
        actual[name] = reports[name]
    results.append({'repository': repository, 'run_id': run_id, 'job_id': job_id,
                    'artifact_id': artifact['id'], 'artifact_digest': artifact['digest'],
                    'proof_commit': PROOF, 'checked_repository_commit': receipt['repository_commit'],
                    'all_project_inputs_match': len(expected_inputs), 'contracts': len(names),
                    'source_lock_sha256': lock, 'actual_axiom_reports': actual,
                    'logs': log_records, 'result_receipt_sha256': sha(receipt_path),
                    'provenance_sha256': sha(root / 'GITHUB-PROVENANCE.json')})

report = {'scope': spec.get('audit_scope', 'Root read-only audit of real downloaded GitHub evidence; no additional Lean or Comparator run.'),
          'reviewer': spec.get('reviewer', '/root'),
          'time': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'verdict': 'PASS',
          'script_sha256': sha(Path(__file__)), 'spec_sha256': sha(Path(sys.argv[1])), 'problem': ID, 'runs': results,
          'limits': 'Machine logs and source matching do not establish informal statement fidelity; the two separate nonauthor mathematical reviews cover that scope.',
          'canonical_promotion': 'PENDING metadata, documentation, independent runtime review and repository publication'}
output_name = spec.get('audit_output', 'ROOT-AUDIT.json')
assert Path(output_name).name == output_name and output_name.endswith('.json')
output_path = E / output_name
output_path.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'verdict': 'PASS', 'actual_GitHub_runs': len(results), 'inputs_per_run': len(expected_inputs), 'contracts_per_run': len(names), 'audit_output': output_name, 'audit_sha256': sha(output_path)}))
