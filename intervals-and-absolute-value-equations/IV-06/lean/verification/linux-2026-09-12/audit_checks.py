"""Independent IV-06 operational audit by /root/formal_review_standards.
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
WT = Path('/tmp/nla-lean-iv06-worktree')
RUN_CONFIG = json.loads((OUT / 'run-config.json').read_text())
COMMIT = RUN_CONFIG['commit']
BASE = 'f41f1f9ffa2171550d4bb795862c6170c4f26070'
PROJECT = 'intervals-and-absolute-value-equations/IV-06/lean'
RUN = RUN_CONFIG['run']
assert RUN_CONFIG['problem'] == 'IV-06'
V = next((OUT / 'artifacts/lean-IV-06').glob('verify-*'))
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
committed = json.loads((OUT / 'committed-candidate.json').read_text())
assert committed['commit'] == COMMIT
assert input_count == committed['complete_tracked_inputs'] == RUN_CONFIG['expected_candidate_inputs']
assert set(committed['files']) == tracked
for rel, record in committed['files'].items():
    assert record['sha256'] == receipt['input_sha256'][rel]
for rel, digest in receipt['input_sha256'].items():
    data = retain_source(PROJECT + '/' + rel)
    assert sha(data) == digest and (WT / PROJECT / rel).read_bytes() == data, rel
(OUT / 'source/git-project-tree.txt').write_bytes(git('ls-tree', '-r', COMMIT, '--', PROJECT))
(OUT / 'source/git-commit.txt').write_bytes(git('cat-file', 'commit', COMMIT))

preflight = json.loads((OUT / 'preflight.json').read_text())
pack = json.loads((WT / PROJECT / 'verification/linux-candidate-2026-09-12/integrity.json').read_text())
assert sha((WT / PROJECT / 'verification/linux-candidate-2026-09-12/integrity.json').read_bytes()) == preflight['packaging_integrity_sha256']
proof_freeze_bytes = (WT / PROJECT / 'verification/proof-freeze.json').read_bytes()
assert sha(proof_freeze_bytes) == preflight['proof_freeze_sha256'] == '5bc8cfd590e82a27807ad5f6832c0cc5d634832979241f80eb30d8d76eaaa673'
proof_freeze = json.loads(proof_freeze_bytes)
for rel, record in proof_freeze['files'].items():
    target = preflight['historical_README_archive'] if rel == 'README.md' else rel
    assert receipt['input_sha256'][target] == record['sha256']
    assert len(retain_source(PROJECT + '/' + target)) == record['bytes']
for rel, digest in pack['review_reports_and_manifests'].items():
    assert receipt['input_sha256'][rel] == digest == preflight['reports_and_manifests'][rel]
assert pack['review_reports_and_manifests']['reviews/proof-referee-1.md'] == 'fa9372a15b89f580959b9febb539d9b5c50e626b4a45672ff8848efce5e9ebc7'
assert pack['review_reports_and_manifests']['reviews/proof-referee-2.md'] == '3d333d14b69424f448e87b5d52984eda37585bf13023eb68890d2964dd534abc'
ref1 = json.loads((WT / PROJECT / 'reviews/proof-referee-1-evidence/integrity-final.json').read_text())
ref2 = json.loads((WT / PROJECT / 'reviews/proof-referee-2-root-evidence/audit.json').read_text())
assert ref1['status'] == 'PASS' and ref1['all_inputs_unchanged']
assert ref2['verdict'].startswith('PASS independent local final proof review')
assert ref1['proof_freeze_sha256'] == ref2['proof_freeze_sha256'] == sha(proof_freeze_bytes)
for rel, record in ref2['source_safety'].items():
    assert record['sha256'] == receipt['input_sha256'][rel] == proof_freeze['files'][rel]['sha256']
for ref in ['reviews/proof-referee-1.md', 'reviews/proof-referee-2.md']:
    assert sha(proof_freeze_bytes) in (WT / PROJECT / ref).read_text()
for manifest_rel, expected_count in pack['verified_review_evidence_counts'].items():
    manifest_path = WT / PROJECT / manifest_rel
    assert sha(manifest_path.read_bytes()) == pack['review_reports_and_manifests'][manifest_rel]
    bound = json.loads(manifest_path.read_text())['files']
    actual = {str(p.relative_to(manifest_path.parent)) for p in manifest_path.parent.rglob('*')
              if p.is_file() and p != manifest_path}
    if manifest_rel == 'reviews/proof-referee-2-root-evidence/EVIDENCE-MANIFEST.json':
        actual.add('../proof-referee-2.md')
    assert actual == set(bound) and len(bound) == expected_count
    for rel, record in bound.items():
        path = manifest_path.parent / rel
        assert path.stat().st_size == record['bytes'] and sha(path.read_bytes()) == record['sha256']
assert len(proof_freeze['files']) == pack['proof_frozen_inputs'] == preflight['proof_freeze_file_count']
assert len(proof_freeze['source_files']) == pack['original_source_git_blobs_unchanged']
assert pack['unchanged_nonwrapper_frozen_inputs'] == len(proof_freeze['files']) - 1
config = json.loads((WT / PROJECT / 'comparator.json').read_text())
names = ['eigenvalue_determinant_semantics', 'family_and_determinant_semantics',
         'witness_eigenpairs', 'witness_separators', 'connected_component_intervals',
         'four_components', 'counterexample', 'not_componentBoundConjecture']
assert config == receipt['config'] == preflight['config']
assert config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
assert config['definition_names'] == []
assert config['theorem_names'] == ['NLA.IV06.' + name for name in names] == proof_freeze['completed_exports']
assert receipt['input_sha256']['README.md'] == pack['current_README_sha256']
assert receipt['input_sha256']['formalization.yaml'] == pack['formalization_yaml_sha256']
candidate_manifest = WT / PROJECT / 'verification/linux-candidate-2026-09-12/EVIDENCE-MANIFEST.json'
assert sha(candidate_manifest.read_bytes()) == preflight['candidate_manifest_sha256']
candidate = json.loads(candidate_manifest.read_text())
for rel, record in candidate['files'].items():
    data = (candidate_manifest.parent / rel).read_bytes()
    assert sha(data) == record['sha256'] and len(data) == record['bytes']
root_manifest_path = candidate_manifest.parent / 'ROOT-EVIDENCE-MANIFEST.json'
assert sha(root_manifest_path.read_bytes()) == RUN_CONFIG['root_candidate_manifest_sha256']
root_manifest = json.loads(root_manifest_path.read_text())
actual_root_files = {str(path.relative_to(root_manifest_path.parent))
                    for path in root_manifest_path.parent.rglob('*')
                    if path.is_file() and path != root_manifest_path}
assert actual_root_files == set(root_manifest['files'])
assert len(actual_root_files) == root_manifest['file_count']
for rel, record in root_manifest['files'].items():
    data = (root_manifest_path.parent / rel).read_bytes()
    assert sha(data) == record['sha256'] and len(data) == record['bytes']
assert sha((candidate_manifest.parent / 'ROOT-CHECKS.json').read_bytes()) == RUN_CONFIG['root_candidate_acceptance_sha256']
for rel, digest in root_manifest['metadata_relative_to_project'].items():
    assert receipt['input_sha256'][rel] == digest

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
assert harness == git('show', '214c142d6bfe0f0c338808f188062acbbad0fb19:tools/lean/harness.py')
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
            or job['name'].startswith('verify (IV-06,')]
assert len(selected) == 3
for job in selected:
    assert job['status'] == 'completed' and job['conclusion'] == 'success'
    assert all(step['status'] == 'completed' and step['conclusion'] == 'success' for step in job['steps'])
    raw = (OUT / f"job-{job['id']}.log").read_text()
    assert COMMIT in raw and '##[error]' not in raw
project_job = next(job for job in selected if job['name'].startswith('verify (IV-06,'))
project_job_log = (OUT / f"job-{project_job['id']}.log").read_text()
assert 'Manifest schema and comparator coverage: PASS (8 declarations)' in project_job_log
archives = []
for item in json.loads((OUT / 'artifact-metadata.json').read_text())['artifacts']:
    if item['name'] not in {'lean-IV-06', 'lean-checker-controls'}:
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
    job = project_job if item['name'] == 'lean-IV-06' else next(job for job in selected if job['name'] == 'checker-controls')
    raw = (OUT / f"job-{job['id']}.log").read_text()
    assert f"SHA256 digest of uploaded artifact zip is {sha(data)}" in raw
    assert f"Artifact ID {item['id']}" in raw
    archives.append({'name': item['name'], 'id': item['id'], 'sha256': sha(data), 'file_count': len(files)})
assert len(archives) == 2

controls = {}
for label, directory in [('checker-controls', S), ('IV-06 controls', V)]:
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
main_command = main.splitlines()[0]
assert main_command.startswith('$ systemd-run --user ')
for marker in ['--wait --pipe --collect', 'RestrictAddressFamilies=~AF_UNIX', '/usr/bin/env -i ',
               'COMPARATOR_LANDRUN=', '/scripts/strict_landrun.py', 'COMPARATOR_LEAN4EXPORT=',
               'GIT_CONFIG_GLOBAL=/dev/null', ' comparator.json']:
    assert marker in main_command, marker
assert '--skip-kernel' not in main_command
fresh_project = re.search(r'--working-directory (\S+)', main_command).group(1)
assert '/.verification-tmp/nla-fresh-proof-' in fresh_project and fresh_project.endswith('/project')
assert main.count('Exporting #[') == 2
assert main.count('Building Challenge') == main.count('Building Solution') == 1
for module in ['Definitions', 'Proof']:
    assert 'Built NLA.IV06.' + module in main
build_jobs = [int(value) for value in re.findall(r'Build completed successfully \((\d+) jobs\)\.', main)]
assert len(build_jobs) == 2 and all(n > 0 for n in build_jobs)
assert main.split('Building Solution', 1)[0].count('declaration uses `sorry`') == len(names)
assert 'warning:' not in main.split('Building Solution', 1)[1]
for name in config['theorem_names']:
    assert main.count(name) >= 3
axiom_records = re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]", main)
assert len(axiom_records) == main.count('depends on axioms:') == proof_freeze['kernel_and_standard_three_checks'] == preflight['expected_kernel_assertions'] == 17
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
                    for rel in ['NLA/IV06/Proof.lean', 'Solution.lean']}
assert assertion_counts == {'NLA/IV06/Proof.lean': 9, 'Solution.lean': 8}
assert sum(assertion_counts.values()) == len(axiom_records)
proof_source = (WT / PROJECT / 'NLA/IV06/Proof.lean').read_text()
assert 'set_option leancert.trust "kernel"' in proof_source
assert proof_source.count('interval_decide (trust := kernel)') == 1
assert re.search(r'theorem numerical_separator_margin\s*:\s*\(-18\s*:\s*ℝ\)\s*<\s*0', proof_source)
implementation_paths = sorted((WT / PROJECT / 'NLA/IV06').glob('*.lean')) + [WT / PROJECT / 'Solution.lean']
for path in implementation_paths:
    code = re.sub(r'/\-.*?\-/', '', path.read_text(), flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', code), str(path)
    assert not re.search(r'^import\s+Challenge\b', code, re.M)
ref1_dependencies = json.loads((WT / PROJECT / 'reviews/proof-referee-1-evidence/actual-dependencies.json').read_text())
ref1_certificate = json.loads((WT / PROJECT / 'reviews/proof-referee-1-evidence/certificate-audit.json').read_text())
assert ref1_certificate['status'] == 'PASS' and ref1_certificate['standard_three_only']
assert not ref1_certificate['native_execution_trust']
for required in ['LeanCert.Validity.verify_strict_upper_bound_dyadic_checked',
                 'NLA.IV06.numerical_separator_margin', 'NLA.IV06.witness_separators_proved',
                 'NLA.IV06.four_components_proved', 'NLA.IV06.counterexample_proved']:
    assert required in ref1_dependencies['actual_consumed'] and required in ref2['actual_required_dependencies']

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
for label in ['lean-IV-06', 'lean-checker-controls']:
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
save('identity-verification.json', {'result': 'PASS for actual IV-06 and control jobs',
    'commit': COMMIT, 'run': RUN, 'project': PROJECT, 'input_files': receipt['input_sha256'],
    'complete_tracked_source_set_count': input_count, 'all_input_bytes_match_worktree_and_commit': True,
    'all_core_hashes_match_both_final_referee_frozen_evidence_sets': True,
    'original_proof_freeze_sources_matched_and_retained': proof_freeze['source_files'],
    'independent_review_hashes': pack['review_reports_and_manifests'], 'archives': archives,
    'audited_tool_bytes_unchanged_since': '214c142d6bfe0f0c338808f188062acbbad0fb19',
    'tools_workflow_and_original_sources_equal_upstream_base': BASE,
    'selected_jobs_and_steps_all_successful': True, 'overall_run_success_observed': overall_success,
    'unrelated_project_artifacts_not_independently_audited_in_this_report': True})
save('control-verification.json', {'result': 'PASS', 'control_runs': controls,
    'theorem_names': config['theorem_names'], 'permitted_axioms': config['permitted_axioms'],
    'axiom_print_count': len(axiom_records), 'fresh_challenge_graph_jobs': build_jobs[0], 'fresh_solution_graph_jobs': build_jobs[1],
    'fresh_dependency_clones': len(manifest['packages']), 'official_mathlib_cache_files': cache_count,
    'default_kernel_replay': 'accepted', 'statement_comparator': 'accepted',
    'fresh_project_directory': fresh_project, 'actual_sandboxed_main_command': main_command,
    'LeanCert_role': 'One materially consumed explicit kernel LeanCert point certificate for -18<0. Exact matrix, full-box affine, real connected-component and Cardinal proofs are bound to both independent final reviews by the actual verified input set. This operational audit did not repeat their mathematical proof reviews.'})
print(json.dumps({'selected_job_checks': 'PASS', 'complete_inputs': input_count, 'exports': len(names),
                  'original_archives': archives, 'overall_run_success_observed': overall_success}, indent=2))
