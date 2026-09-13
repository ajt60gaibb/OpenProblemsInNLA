"""Independent TR-15 operational audit by /root/solved_statement_inventory.
Adapts the TR-15 and MI-26 audit scripts, themselves based on
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
WT = Path('/tmp/nla-lean-tr15-worktree')
COMMIT = '6a2d0868e8b7905dbd5c04d4beaae8cf43288e1f'
BASE = '8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc'
PROJECT = 'tensor-computations/TR-15/lean'
RUN = 34716902324
V = next((OUT / 'artifacts/lean-TR-15').glob('verify-*'))
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
assert len(tracked) == 135 and tracked == set(receipt['input_sha256'])
for rel, digest in receipt['input_sha256'].items():
    data = retain_source(PROJECT + '/' + rel)
    assert sha(data) == digest and (WT / PROJECT / rel).read_bytes() == data, rel
(OUT / 'source/git-project-tree.txt').write_bytes(git('ls-tree', '-r', COMMIT, '--', PROJECT))
(OUT / 'source/git-commit.txt').write_bytes(git('cat-file', 'commit', COMMIT))

pack = json.loads((WT / PROJECT / 'verification/root-linux-packaging.json').read_text())
for rel, digest in pack['protected_files'].items():
    assert receipt['input_sha256'][rel] == digest, rel
for name, digest in pack['independent_review_hashes'].items():
    assert receipt['input_sha256']['reviews/' + name] == digest, name
assert pack['independent_review_hashes']['proof-referee-1.md'] == 'b482f8f3a8a5239fafbc975dbbfefef68592e6f0745cbf5f59ddf538e83b2ef7'
assert pack['independent_review_hashes']['proof-referee-2.md'] == 'fee10255f62ca164320349da89c2d839662af1289ee389c11d6d8d52583c370b'
core = ['NLA/TR15/Definitions.lean', 'Challenge.lean', 'NUMERICAL_TARGETS.md',
        'NLA/TR15/Proof.lean', 'Solution.lean']
for ref in ['reviews/proof-referee-1.md', 'reviews/proof-referee-2.md']:
    report = (WT / PROJECT / ref).read_text()
    for rel in core:
        assert receipt['input_sha256'][rel] in report, (ref, rel)
config = json.loads((WT / PROJECT / 'comparator.json').read_text())
names = ['lower_contractions', 'upper_contraction', 'lower_eigenvalues_pos',
         'lower_eigenpair_exists', 'upper_negative_eigenpair', 'counterexample',
         'not_inheritanceConjecture']
assert config == receipt['config']
assert config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
assert config['definition_names'] == []
assert config['theorem_names'] == ['NLA.TR15.' + name for name in names] == pack['exports']

lock_bytes = retain_source('tools/lean/source-lock.json')
lock = json.loads(lock_bytes)
assert sha(lock_bytes) == receipt['source_lock_sha256'] == receipt['tool_receipt']['source_lock_sha256']
assert lock['commit'] == '8d1b0c0545a77b40245e84705aa7d273e6c81e62'
assert len(lock['files']) == 58
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
    'locked_source_count': 58, 'files': lock['files'], 'ci_sandbox_probe_sha256': sha(probe),
    'harness_sha256': sha(harness), 'linux_tool_receipt': receipt['tool_receipt'],
    'scope': 'All pinned source bytes and the exact reviewed probe adaptation match. Original remote logs and receipts evidence Linux binary execution; no new local Linux execution is claimed.'})

run = json.loads((OUT / 'run-metadata.json').read_text())
assert run['id'] == RUN and run['head_sha'] == COMMIT
jobs = json.loads((OUT / 'jobs.json').read_text())['jobs']
assert len(jobs) == 7
selected = [job for job in jobs if job['name'] in ['select', 'checker-controls']
            or job['name'].startswith('verify (TR-15,')]
assert len(selected) == 3
for job in selected:
    assert job['status'] == 'completed' and job['conclusion'] == 'success'
    assert all(step['status'] == 'completed' and step['conclusion'] == 'success' for step in job['steps'])
    raw = (OUT / f"job-{job['id']}.log").read_text()
    assert COMMIT in raw and '##[error]' not in raw
project_job = next(job for job in selected if job['name'].startswith('verify (TR-15,'))
project_job_log = (OUT / f"job-{project_job['id']}.log").read_text()
assert 'Manifest schema and comparator coverage: PASS (7 declarations)' in project_job_log
archives = []
for item in json.loads((OUT / 'artifact-metadata.json').read_text())['artifacts']:
    if item['name'] not in {'lean-TR-15', 'lean-checker-controls'}:
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
    job = project_job if item['name'] == 'lean-TR-15' else next(job for job in selected if job['name'] == 'checker-controls')
    raw = (OUT / f"job-{job['id']}.log").read_text()
    assert f"SHA256 digest of uploaded artifact zip is {sha(data)}" in raw
    assert f"Artifact ID {item['id']}" in raw
    archives.append({'name': item['name'], 'id': item['id'], 'sha256': sha(data), 'file_count': len(files)})
assert len(archives) == 2

controls = {}
for label, directory in [('checker-controls', S), ('TR-15 controls', V)]:
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
                   'PASS effective capabilities: none', 'PASS no_new_privs: set',
                   'Sandbox UID: 1001', 'bwrap: setting up uid map: Permission denied']:
        assert sandbox.count(marker) == 2, (label, marker)
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
for module in ['Definitions', 'Proof']:
    assert 'Built NLA.TR15.' + module in main
build_jobs = [int(value) for value in re.findall(r'Build completed successfully \((\d+) jobs\)\.', main)]
assert build_jobs == [1231, 2918]
assert main.split('Building Solution', 1)[0].count('declaration uses `sorry`') == 7
assert 'warning:' not in main.split('Building Solution', 1)[1]
for name in config['theorem_names']:
    assert main.count(name) >= 3
axiom_records = re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]", main)
assert len(axiom_records) == main.count('depends on axioms:') == 15
assert len({name for name, _ in axiom_records}) == 15
assert all([value.strip() for value in axioms.split(',')] == config['permitted_axioms']
           for _, axioms in axiom_records)
for marker in ['Running Lean default kernel on solution.', 'Lean default kernel accepts the solution',
               'Your solution is okay!']:
    assert marker in main
assert main.rstrip().endswith('EXIT_STATUS=0')
save('axiom-verification.json', {'result': 'PASS', 'count': 15,
    'declarations': {name: [value.strip() for value in axioms.split(',')] for name, axioms in axiom_records}})
for rel, count in [('NLA/TR15/Proof.lean', 8), ('Solution.lean', 7)]:
    assert (WT / PROJECT / rel).read_text().count('#assert_trust kernel ') == count

manifest = json.loads((WT / PROJECT / 'lake-manifest.json').read_text())
deps = (V / 'dependencies.log').read_text()
assert len(manifest['packages']) == 10
for package in manifest['packages']:
    assert f"{package['name']}: cloning " in deps
    assert f"{package['name']}: checking out revision '{package['rev']}'" in deps
assert deps.rstrip().endswith('EXIT_STATUS=0')
cache = (V / 'mathlib-cache.log').read_text()
assert 'Decompressed 8690 file(s)' in cache and cache.rstrip().endswith('EXIT_STATUS=0')
standalone = json.loads((S / 'result.json').read_text())
assert standalone['result'] == 'checker-selftest-passed'
assert standalone['mathematical_verification'] == 'none; checker fixtures only'
assert standalone['tool_receipt'] == receipt['tool_receipt']
for label in ['lean-TR-15', 'lean-checker-controls']:
    bootstrap = OUT / 'artifacts' / label / 'bootstrap'
    for log in ['comparator-build.log', 'elan.log', 'landrun-build.log']:
        assert (bootstrap / log).read_text().rstrip().endswith('EXIT_STATUS=0')
    for marker in ['Built comparator:exe', 'Built lean4export:exe']:
        assert marker in (bootstrap / 'comparator-build.log').read_text()

proof_freeze = json.loads((WT / PROJECT / 'reviews/proof-freeze.json').read_text())
assert sha((WT / PROJECT / 'reviews/proof-freeze.json').read_bytes()) == '1263937a8aeef77192d2eaf434457c36abefc77a7aefbd25fdf0dbd854ed7f6c'
assert len(proof_freeze['files']) == 75
assert len(proof_freeze['source_files']) == 6
history = pack['historical_readme_archive']
for rel, expected in proof_freeze['files'].items():
    actual = history['archive'] if rel == 'README.md' else rel
    assert receipt['input_sha256'][actual] == expected, (rel, actual)
assert receipt['input_sha256']['README.md'] == history['current_sha256']
assert receipt['input_sha256'][history['archive']] == history['old_sha256']
for rel, expected in proof_freeze['source_files'].items():
    data = retain_source(rel)
    assert data == git('show', BASE + ':' + rel)
    assert sha(data) == expected
proof = (WT / PROJECT / 'NLA/TR15/Proof.lean').read_text()
for marker in ['lemma negative_eigenvalue_certificate : (-1 : ℝ) < 0 := by',
               'interval_decide (trust := kernel)',
               'refine ⟨⟨?_, ?_⟩, negative_eigenvalue_certificate⟩',
               '(not_le_of_gt upper_negative_eigenpair_proved.2)',
               'exact counterexample_proved.2.2']:
    assert marker in proof
assert 'LeanCert.Validity.verify_strict_upper_bound_dyadic_checked' in (WT / PROJECT / 'verification/certificate-inspection.log').read_text()

overall_success = run['status'] == 'completed' and run['conclusion'] == 'success'
if overall_success:
    assert all(job['status'] == 'completed' and job['conclusion'] == 'success' for job in jobs)
    assert all(step['conclusion'] == 'success' for job in jobs for step in job['steps'])
save('identity-verification.json', {'result': 'PASS for actual TR-15 and control jobs',
    'commit': COMMIT, 'run': RUN, 'project': PROJECT, 'input_files': receipt['input_sha256'],
    'complete_tracked_source_set_count': 135, 'all_input_bytes_match_worktree_and_commit': True,
    'five_core_hashes_match_both_final_referees': True,
    'original_proof_freeze_sources_matched_and_retained': proof_freeze['source_files'],
    'independent_review_hashes': pack['independent_review_hashes'], 'archives': archives,
    'audited_tool_bytes_unchanged_since': '214c142d6bfe0f0c338808f188062acbbad0fb19',
    'tools_workflow_and_original_sources_equal_upstream_base': BASE,
    'selected_jobs_and_steps_all_successful': True, 'overall_run_success_observed': overall_success,
    'unrelated_project_artifacts_not_independently_audited_in_this_report': True})
save('control-verification.json', {'result': 'PASS', 'control_runs': controls,
    'theorem_names': config['theorem_names'], 'permitted_axioms': config['permitted_axioms'],
    'axiom_print_count': 15, 'fresh_challenge_graph_jobs': 1231, 'fresh_solution_graph_jobs': 2918,
    'fresh_dependency_clones': 10, 'official_mathlib_cache_files': 8690,
    'default_kernel_replay': 'accepted', 'statement_comparator': 'accepted',
    'LeanCert_role': 'Actual retained kernel-mode certificate for minus one less than zero, used in the negative H-eigenpair and full contradiction; no tensor eigenvalue enumeration or numerical root isolation.'})
print(json.dumps({'selected_job_checks': 'PASS', 'complete_inputs': 135, 'exports': 7,
                  'original_archives': archives, 'overall_run_success_observed': overall_success}, indent=2))
