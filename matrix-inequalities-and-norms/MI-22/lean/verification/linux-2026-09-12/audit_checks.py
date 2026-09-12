"""Independent MI-22 operational audit by /root/formal_review_standards.
Adapts the MI-26 audit by /root/solved_statement_inventory, itself based on
the campaign's MI-06 and MI-29 audits. Supplements actual raw-log inspection.
Reads immutable Git blobs and retained original artifacts; writes evidence only.
"""
from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import zipfile

OUT = Path(__file__).resolve().parent
WT = Path('/tmp/nla-lean-mi22-worktree')
COMMIT = '26f526cf8b6232af9528b30616076dc7a2c66ac6'
BASE = '8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc'
PROJECT = 'matrix-inequalities-and-norms/MI-22/lean'
RUN = 34720684925
V = next((OUT / 'artifacts/lean-MI-22').glob('verify-*'))
S = next((OUT / 'artifacts/lean-checker-controls').glob('selftest-*'))

def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(*args):
    return subprocess.check_output(['git', '-C', str(WT), *args])

def save(name, data):
    (OUT / name).write_text(json.dumps(data, indent=2) + '\n')

def retain_source(path):
    data = git('show', COMMIT + ':' + path)
    target = OUT / 'source' / path
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        assert target.read_bytes() == data
    else:
        target.write_bytes(data)
    return data

receipt = json.loads((V / 'result.json').read_text())
assert receipt['repository_commit'] == COMMIT
assert receipt['project'] == PROJECT and receipt['result'] == 'comparator-accepted'
assert receipt['semantic_review'] == 'not-performed-by-this-command'
assert git('rev-parse', 'HEAD').decode().strip() == COMMIT
tracked = {path[len(PROJECT) + 1:] for path in
           git('ls-tree', '-r', '--name-only', COMMIT, '--', PROJECT).decode().splitlines()}
assert tracked == set(receipt['input_sha256'])
input_count = len(tracked)
for rel, digest in receipt['input_sha256'].items():
    data = retain_source(PROJECT + '/' + rel)
    assert sha(data) == digest and (WT / PROJECT / rel).read_bytes() == data, rel
(OUT / 'source/git-project-tree.txt').write_bytes(git('ls-tree', '-r', COMMIT, '--', PROJECT))
(OUT / 'source/git-commit.txt').write_bytes(git('cat-file', 'commit', COMMIT))

pack = json.loads((WT / PROJECT / 'verification/root-linux-packaging.json').read_text())
proof_freeze_bytes = (WT / PROJECT / 'verification/proof-freeze.json').read_bytes()
assert sha(proof_freeze_bytes) == 'f1c267a6aa600074d3b054863926d5f9cdbf6b0eadb83912a912277ac54018a0'
proof_freeze = json.loads(proof_freeze_bytes)
for rel, record in proof_freeze['files'].items():
    digest = record['sha256']
    if rel == 'README.md':
        assert receipt['input_sha256'][pack['historical_README_archive']] == digest
    else:
        assert receipt['input_sha256'][rel] == digest, rel
for name, digest in pack['independent_review_hashes'].items():
    assert receipt['input_sha256']['reviews/' + name] == digest, name
assert pack['independent_review_hashes']['proof-referee-1.md'] == '250b98be84248ba8dcb1c9be0a1d60743b88d0aadf5919ac6baf601a6f9597c3'
assert pack['independent_review_hashes']['proof-referee-2.md'] == 'b97c55e0d2667efa9b297039db26801f66af3a9cd80a8a2de39d45c1ce6a6e77'
core = ['NLA/MI22/Definitions.lean', 'Challenge.lean', 'NUMERICAL_TARGETS.md',
        'SOURCE_CORRESPONDENCE.md', 'NLA/MI22/FunctionalCalculus.lean',
        'NLA/MI22/Norms.lean', 'NLA/MI22/SingularValues.lean', 'NLA/MI22/Witness.lean',
        'NLA/MI22/ExactData.lean', 'NLA/MI22/Proof.lean', 'Solution.lean']
ref1 = json.loads((WT / PROJECT / 'reviews/proof-referee-1-evidence/inputs-before.json').read_text())
ref2 = json.loads((WT / PROJECT / 'reviews/proof-referee-2-root-evidence/source-identity.json').read_text())
assert ref2['before_equals_after']
for rel in core:
    assert ref1[rel]['sha256'] == ref2['files'][rel]['sha256'] == receipt['input_sha256'][rel], rel
    assert ref1[rel]['bytes'] == ref2['files'][rel]['bytes'] == (WT / PROJECT / rel).stat().st_size
for ref in ['reviews/proof-referee-1.md', 'reviews/proof-referee-2.md']:
    report = (WT / PROJECT / ref).read_text()
    for rel in ['NLA/MI22/Proof.lean', 'Solution.lean']:
        assert receipt['input_sha256'][rel] in report
    assert sha(proof_freeze_bytes) in report
assert len(proof_freeze['files']) == 104 and len(proof_freeze['source_files']) == 8
assert pack['frozen_project_files'] == 104 and pack['unchanged_nonREADME_files'] == 103
config = json.loads((WT / PROJECT / 'comparator.json').read_text())
names = ['singular_values_semantics', 'spectral_power_semantics', 'euclidean_norm_bounds',
         'witness_rational_data', 'witness_principal_powers', 'witness_operator_gap',
         'counterexample', 'not_weightedLogMajorizationConjecture']
assert config == receipt['config']
assert config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
assert config['definition_names'] == []
assert config['theorem_names'] == ['NLA.MI22.' + name for name in names] == pack['exports']
assert receipt['input_sha256']['README.md'] == pack['current_README_sha256']
assert receipt['input_sha256']['formalization.yaml'] == pack['formalization_yaml_sha256']

lock_bytes = retain_source('tools/lean/source-lock.json')
lock = json.loads(lock_bytes)
assert sha(lock_bytes) == receipt['source_lock_sha256'] == receipt['tool_receipt']['source_lock_sha256']
assert lock['commit'] == '8d1b0c0545a77b40245e84705aa7d273e6c81e62'
locked_source_count = len(lock['files'])
sources = Path('/tmp/nla-lean-formalization/fetched-tool-source-check')
for item in lock['files']:
    data = (sources / item['destination']).read_bytes()
    assert len(data) == item['bytes'] and sha(data) == item['sha256'], item['destination']
    target = OUT / 'source/forsythe' / item['destination']
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
harness = retain_source('tools/lean/harness.py')
node = next(node for node in ast.parse(harness).body
            if isinstance(node, ast.FunctionDef) and node.name == 'ci_probe_source')
namespace = {'Path': Path, 'HarnessError': RuntimeError}
exec(compile(ast.Module(body=[node], type_ignores=[]), 'reviewed_ci_probe_source', 'exec'), namespace)
probe = namespace['ci_probe_source'](sources).encode()
assert sha(probe) == receipt['tool_receipt']['ci_sandbox_probe_sha256']
(OUT / 'source/sandbox_probe_ci.py').write_bytes(probe)
assert not git('diff', '--name-only', BASE, COMMIT, '--', 'tools/lean',
               '.github/workflows/lean-verification.yml', 'docs/lean/ci-toolchain')
for rel in ['tools/lean/harness.py', 'tools/lean/source-lock.json', 'tools/lean/bootstrap.sh',
            'tools/lean/selftest.sh', 'tools/lean/verify.sh']:
    assert git('show', '214c142d6bfe0f0c338808f188062acbbad0fb19:' + rel) == retain_source(rel)
retain_source('.github/workflows/lean-verification.yml')
save('tool-source-verification.json', {'result': 'PASS', 'source_lock_sha256': sha(lock_bytes),
    'locked_source_count': locked_source_count, 'files': lock['files'], 'ci_sandbox_probe_sha256': sha(probe),
    'harness_sha256': sha(harness), 'linux_tool_receipt': receipt['tool_receipt'],
    'scope': 'All pinned source bytes and the exact reviewed probe adaptation match. Original remote logs and receipts evidence Linux binary execution; no new local Linux execution is claimed.'})

run = json.loads((OUT / 'run-metadata.json').read_text())
assert run['id'] == RUN and run['head_sha'] == COMMIT
jobs = json.loads((OUT / 'jobs.json').read_text())['jobs']
assert jobs
assert run['status'] == 'completed' and run['conclusion'] == 'success'
selected = [job for job in jobs if job['name'] in ['select', 'checker-controls']
            or job['name'].startswith('verify (MI-22,')]
assert len(selected) == 3
for job in selected:
    assert job['status'] == 'completed' and job['conclusion'] == 'success'
    assert all(step['status'] == 'completed' and step['conclusion'] == 'success' for step in job['steps'])
    raw = (OUT / f"job-{job['id']}.log").read_text()
    assert COMMIT in raw and '##[error]' not in raw
project_job = next(job for job in selected if job['name'].startswith('verify (MI-22,'))
project_job_log = (OUT / f"job-{project_job['id']}.log").read_text()
assert 'Manifest schema and comparator coverage: PASS (8 declarations)' in project_job_log
archives = []
for item in json.loads((OUT / 'artifact-metadata.json').read_text())['artifacts']:
    if item['name'] not in {'lean-MI-22', 'lean-checker-controls'}:
        continue
    data = (OUT / (item['name'] + '.zip')).read_bytes()
    assert sha(data) == item['digest'].removeprefix('sha256:')
    assert item['workflow_run']['head_sha'] == COMMIT and not item['expired']
    extracted = OUT / 'artifacts' / item['name']
    with zipfile.ZipFile(OUT / (item['name'] + '.zip')) as archive:
        files = {file.filename for file in archive.infolist() if not file.is_dir()}
        assert files == {str(path.relative_to(extracted)) for path in extracted.rglob('*') if path.is_file()}
        for rel in files:
            assert archive.read(rel) == (extracted / rel).read_bytes()
    job = project_job if item['name'] == 'lean-MI-22' else next(job for job in selected if job['name'] == 'checker-controls')
    raw = (OUT / f"job-{job['id']}.log").read_text()
    assert f"SHA256 digest of uploaded artifact zip is {sha(data)}" in raw
    assert f"Artifact ID {item['id']}" in raw
    archives.append({'name': item['name'], 'id': item['id'], 'sha256': sha(data), 'file_count': len(files)})
assert len(archives) == 2

controls = {}
for label, directory in [('checker-controls', S), ('MI-22 controls', V)]:
    sandbox = (directory / 'sandbox.log').read_text()
    for mode in ['build', 'export']:
        assert f'MODE {mode}: exit=0' in sandbox
    for kind in ['user', 'pid', 'mnt', 'net', 'ipc', 'uts']:
        assert sandbox.count(f'PASS {kind} namespace: private') == 2
    for marker in ['PASS outside .lake write-open: denied errno=30',
                   'PASS outside .lake truncate: denied errno=30',
                   'PASS outside .lake read-only truncate-open: denied errno=30',
                   'PASS symlink from .lake to outside write: denied errno=30',
                   'PASS outside .lake creation: denied errno=30',
                   'PASS host parent: absent from private /proc',
                   'PASS host parent signal lookup: denied errno=3',
                   'PASS host loopback listener: unreachable errno=13',
                   'PASS AF_UNIX socket creation: denied errno=97',
                   'PASS effective capabilities: none', 'PASS no_new_privs: set', 'bwrap: setting up uid map: Permission denied']:
        assert sandbox.count(marker) == 2, (label, marker)
    uids = [int(x) for x in re.findall(r'Sandbox UID: (\d+)', sandbox)]
    assert len(uids) == 2 and all(x > 0 for x in uids)
    for marker in ['PASS build .lake write: allowed', 'PASS export .lake write-open: denied errno=30',
                   'PASS export .lake truncate: denied errno=30',
                   'Outer and export fixture contents unchanged; only designated build fixture written.']:
        assert marker in sandbox
    for case in ['unknown option', 'unexpected --rw', 'unexpected --rwx', 'relative --rwx']:
        assert f'NEGATIVE {case}: exit=2' in sandbox
    kernel = (directory / 'kernel-controls.log').read_text()
    for marker in ['RETURN honest_with_inductives_and_quotients: accepted',
                   'RETURN invalid_raw_proof: rejected:', 'Quotient post-check rejects the solution',
                   'RETURN quotient_postcheck_mismatch: rejected: Quotient constant mismatch on: Quot.lift',
                   'PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']:
        assert marker in kernel
    comparator = (directory / 'comparator-controls.log').read_text()
    for case, code in [('simple_match', 0), ('simple_mismatch', 1), ('simple_axiom_issue', 1),
                       ('simple_kind_mismatch', 1), ('type_mismatch', 1)]:
        assert f'PASS {case}: exit {code}, expected {code}' in comparator
    assert comparator.count('Building Challenge') == comparator.count('Building Solution') == 5
    assert comparator.count('Exporting #[') == 10
    for log, axiom in [('negative-sorry.log', 'sorryAx'),
                       ('negative-native.log', 'checked._native.native_decide.ax_1_1')]:
        text = (directory / log).read_text()
        assert 'Building Challenge' in text and 'Building Solution' in text
        assert text.count('Exporting #[') == 2
        assert f"Illegal axiom detected: '{axiom}'" in text
        assert text.rstrip().endswith('EXIT_STATUS=1')
    for log in ['sandbox.log', 'kernel-controls.log', 'comparator-controls.log', 'user-service.log']:
        assert (directory / log).read_text().rstrip().endswith('EXIT_STATUS=0')
    controls[label] = {'actual_sandbox_modes': 2, 'sandbox_option_rejections': 4,
        'actual_raw_kernel_cases': 3, 'actual_comparator_fixtures': 5, 'actual_axiom_rejections': 2,
        'nested_bwrap_scope': 'Executable ran; UID-map creation was denied before the inner write.'}

main = (V / 'comparator.log').read_text()
assert main.count('Exporting #[') == 2
assert main.count('Building Challenge') == main.count('Building Solution') == 1
for module in ['Definitions', 'FunctionalCalculus', 'Norms', 'SingularValues', 'Witness', 'ExactData', 'Proof']:
    assert 'Built NLA.MI22.' + module in main
build_jobs = [int(value) for value in re.findall(r'Build completed successfully \((\d+) jobs\)\.', main)]
assert len(build_jobs) == 2 and all(n > 0 for n in build_jobs)
assert main.split('Building Solution', 1)[0].count('declaration uses `sorry`') == len(names)
assert 'warning:' not in main.split('Building Solution', 1)[1]
for name in config['theorem_names']:
    assert main.count(name) >= 3
axiom_records = re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]", main)
assert len(axiom_records) == main.count('depends on axioms:') == proof_freeze['kernel_assertion_count'] == 17
assert len({name for name, _ in axiom_records}) == len(axiom_records)
assert all([value.strip() for value in axioms.split(',')] == config['permitted_axioms']
           for _, axioms in axiom_records)
for marker in ['Running Lean default kernel on solution.', 'Lean default kernel accepts the solution',
               'Your solution is okay!']:
    assert marker in main
assert main.rstrip().endswith('EXIT_STATUS=0')
save('axiom-verification.json', {'result': 'PASS', 'count': len(axiom_records),
    'declarations': {name: [value.strip() for value in axioms.split(',')] for name, axioms in axiom_records}})
assertion_counts = {rel: (WT / PROJECT / rel).read_text().count('#assert_trust kernel ')
                    for rel in ['NLA/MI22/Proof.lean', 'Solution.lean']}
assert assertion_counts == {'NLA/MI22/Proof.lean': 9, 'Solution.lean': 8}
assert sum(assertion_counts.values()) == len(axiom_records)
proof_source = (WT / PROJECT / 'NLA/MI22/Proof.lean').read_text()
assert 'set_option leancert.trust "kernel"' in proof_source
assert 'theorem numerical_separation : (10500 : ℝ) < 11000' in proof_source
assert 'interval_decide (trust := kernel)' in proof_source
assert '(numerical_separation.trans witness_operator_gap_proved.2)' in proof_source
assert 'exact counterexample_proved.2.2.2.2.2' in proof_source

manifest = json.loads((WT / PROJECT / 'lake-manifest.json').read_text())
deps = (V / 'dependencies.log').read_text()
assert {p['name'] for p in manifest['packages']} >= {'leancert', 'mathlib'}
for package in manifest['packages']:
    assert f"{package['name']}: cloning " in deps
    assert f"{package['name']}: checking out revision '{package['rev']}'" in deps
assert deps.rstrip().endswith('EXIT_STATUS=0')
cache = (V / 'mathlib-cache.log').read_text()
cache_counts = re.findall(r'^Decompressed (\d+) file\(s\)', cache, re.M)
assert len(cache_counts) == 1 and int(cache_counts[0]) > 0 and cache.rstrip().endswith('EXIT_STATUS=0')
cache_count = int(cache_counts[0])
standalone = json.loads((S / 'result.json').read_text())
assert standalone['result'] == 'checker-selftest-passed'
assert standalone['mathematical_verification'] == 'none; checker fixtures only'
assert standalone['tool_receipt'] == receipt['tool_receipt']
for label in ['lean-MI-22', 'lean-checker-controls']:
    bootstrap = OUT / 'artifacts' / label / 'bootstrap'
    for log in ['comparator-build.log', 'elan.log', 'landrun-build.log']:
        assert (bootstrap / log).read_text().rstrip().endswith('EXIT_STATUS=0')
    for marker in ['Built comparator:exe', 'Built lean4export:exe']:
        assert marker in (bootstrap / 'comparator-build.log').read_text()

for rel, expected in proof_freeze['source_files'].items():
    data = retain_source(rel)
    assert data == git('show', BASE + ':' + rel)
    assert sha(data) == expected
with zipfile.ZipFile(OUT / 'run-logs.zip') as archive:
    assert archive.testzip() is None
    logs = []
    for item in archive.infolist():
        if item.is_dir(): continue
        logs.append({'name': item.filename, 'bytes': item.file_size, 'sha256': sha(archive.read(item))})
    assert logs
save('run-log-archive.json', {'archive_sha256': sha((OUT / 'run-logs.zip').read_bytes()),
    'source': f'https://api.github.com/repos/sgstepaniants/OpenProblemsInNLA/actions/runs/{RUN}/logs',
    'scope': 'Original complete run-log ZIP, fetched from the authenticated GitHub endpoint. No GitHub-published digest is claimed for this log archive.',
    'file_count': len(logs), 'entries': logs})

overall_success = run['status'] == 'completed' and run['conclusion'] == 'success'
if overall_success:
    assert all(job['status'] == 'completed' and job['conclusion'] == 'success' for job in jobs)
    assert all(step['conclusion'] == 'success' for job in jobs for step in job['steps'])
save('identity-verification.json', {'result': 'PASS for actual MI-22 and control jobs',
    'commit': COMMIT, 'run': RUN, 'project': PROJECT, 'input_files': receipt['input_sha256'],
    'complete_tracked_source_set_count': input_count, 'all_input_bytes_match_worktree_and_commit': True,
    'all_eleven_core_hashes_match_both_final_referee_evidence_sets': True,
    'original_proof_freeze_sources_matched_and_retained': proof_freeze['source_files'],
    'independent_review_hashes': pack['independent_review_hashes'], 'archives': archives,
    'audited_tool_bytes_unchanged_since': '214c142d6bfe0f0c338808f188062acbbad0fb19',
    'tools_workflow_and_original_sources_equal_upstream_base': BASE,
    'selected_jobs_and_steps_all_successful': True, 'overall_run_success_observed': overall_success,
    'unrelated_project_artifacts_not_independently_audited_in_this_report': True})
save('control-verification.json', {'result': 'PASS', 'control_runs': controls,
    'theorem_names': config['theorem_names'], 'permitted_axioms': config['permitted_axioms'],
    'axiom_print_count': len(axiom_records), 'fresh_challenge_graph_jobs': build_jobs[0], 'fresh_solution_graph_jobs': build_jobs[1],
    'fresh_dependency_clones': len(manifest['packages']), 'official_mathlib_cache_files': cache_count,
    'default_kernel_replay': 'accepted', 'statement_comparator': 'accepted',
    'LeanCert_role': 'Actual kernel-certified scalar 10500<11000 on [0,0], consumed in the first-singular-value reversal; exact matrix, CFC and norm proofs remain separate. The source and prior independent term inspections are bound by the actual verified input set.'})
print(json.dumps({'selected_job_checks': 'PASS', 'complete_inputs': input_count, 'exports': len(names),
                  'original_archives': archives, 'overall_run_success_observed': overall_success}, indent=2))
