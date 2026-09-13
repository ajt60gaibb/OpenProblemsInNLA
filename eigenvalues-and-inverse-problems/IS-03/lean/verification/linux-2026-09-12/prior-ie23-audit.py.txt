"""Actual IE-23 Linux operational checks by implementing agent /root/leancert_examples.

Adapts the immutable MI-03 operational audit by /root/formal_review_standards,
which adapts the campaign's MI-26, MI-06 and MI-29 audits. This operational
inspection is NOT a new independent mathematical review; root separately
accepts its evidence and the final mathematical refs are inventory and root.
Actual logs are also read manually. Writes evidence only, never source.
"""
from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import zipfile

OUT = Path(__file__).resolve().parent
CTX = json.loads((OUT / 'context.json').read_text())
WT = Path(CTX['worktree'])
COMMIT, BASE, PROJECT, RUN = CTX['commit'], CTX['source_base'], CTX['project'], CTX['run']
vs = list((OUT / 'artifacts/lean-IE-23').glob('verify-*'))
ss = list((OUT / 'artifacts/lean-checker-controls').glob('selftest-*'))
assert len(vs) == len(ss) == 1
V, S = vs[0], ss[0]

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
assert input_count == CTX['expected_input_count'] == 190
preflight = json.loads((OUT / 'preflight.json').read_text())
assert receipt['input_sha256'] == {r: v['sha256'] for r, v in preflight['input_files'].items()}
for rel, digest in receipt['input_sha256'].items():
    data = retain_source(PROJECT + '/' + rel)
    assert sha(data) == digest and (WT / PROJECT / rel).read_bytes() == data, rel
(OUT / 'source/git-project-tree.txt').write_bytes(git('ls-tree', '-r', COMMIT, '--', PROJECT))
(OUT / 'source/git-commit.txt').write_bytes(git('cat-file', 'commit', COMMIT))
pack = json.loads((WT / PROJECT / 'verification/linux-candidate-2026-09-12/packaging-record.json').read_text())
proof_freeze_bytes = (WT / PROJECT / 'reviews/proof-freeze.json').read_bytes()
assert sha(proof_freeze_bytes) == CTX['proof_freeze_sha256']
proof_freeze = json.loads(proof_freeze_bytes)
archive = 'verification/linux-candidate-2026-09-12/README.statement.md'
for rel, record in proof_freeze['files'].items():
    target = archive if rel == 'README.md' else rel
    assert receipt['input_sha256'][target] == record['sha256'], rel
    assert (WT / PROJECT / target).stat().st_size == record['bytes'], rel
assert len(proof_freeze['files']) == 104 and len(proof_freeze['source_files']) == 8
assert pack['unchanged_nonREADME_proof_inputs'] == 103
reports = pack['review_reports_preserved']
assert reports['reviews/proof-referee-1.md'] == '4aded9a6adfc4723941bae2ac8c4ae0c1ad4bdef7136dd3a285068ae1f68d4d2'
assert reports['reviews/proof-referee-2.md'] == '0b6f2f6ed1aa4505da7ceb63d33470822914820904a4b0fee309f69ba314c008'
for rel, digest in reports.items():
    assert receipt['input_sha256'][rel] == digest
for rel in ['reviews/proof-referee-1.md', 'reviews/proof-referee-2.md']:
    assert CTX['proof_freeze_sha256'] in (WT / PROJECT / rel).read_text()
ref1 = json.loads((WT / PROJECT / 'reviews/proof-referee-1-evidence/final-audit.json').read_text())
ref2 = json.loads((WT / PROJECT / 'reviews/proof-referee-2-root-evidence/audit.json').read_text())
assert ref1['verdict'].startswith('PASS') and ref2['verdict'].startswith('PASS')
assert ref1['proof_freeze_sha256'] == ref2['proof_freeze_sha256'] == CTX['proof_freeze_sha256']
assert len(ref1['source_scan']) == len(ref2['source_safety']) == 8
assert set(ref1['source_scan']) == set(ref2['source_safety'])
for rel, rec in ref1['source_scan'].items():
    assert rec['sha256'] == ref2['source_safety'][rel]['sha256'] == receipt['input_sha256'][rel]
    assert not rec['admissions_or_extra_trust']
    assert ref2['source_safety'][rel]['no_admissions_extra_trust_or_Challenge_import']
for step in ref1['fresh_commands']:
    assert step['exit_code'] == 0
    assert receipt['input_sha256'][step['source']] == step['source_sha256']
assert len(ref1['fresh_commands']) == ref2['fresh_commands'] == 10
assert ref1['frozen_project_inputs_unchanged'] == ref2['frozen_project_inputs'] == 104
assert ref1['original_source_Git_blobs_unchanged'] == ref2['original_source_blobs'] == 8
assert ref1['frozen_original_statement_inputs_unchanged'] == ref2['original_statement_inputs'] == 32
assert ref1['reachable_project_declarations'] == ref2['safe_project_declarations'] == 93

# Every reviewer manifest's parent-relative report remains bound. Include every
# nested manifest. The only exclusions are the exact enclosing manifest paths.
def check_manifest(path, expected, complete=True):
    assert sha(path.read_bytes()) == expected
    bound = json.loads(path.read_text())['files']
    actual = {str(p.relative_to(path.parent)) for p in path.parent.rglob('*')
              if p.is_file() and p != path}
    if complete:
        assert actual == {r for r in bound if not r.startswith('../')}
    for rel, r in bound.items():
        p = path.parent / rel
        assert p.resolve().is_relative_to((WT / PROJECT).resolve())
        assert p.stat().st_size == r['bytes'] and sha(p.read_bytes()) == r['sha256']
    return len(bound)
for rel, r in pack['review_evidence_preserved'].items():
    assert check_manifest(WT / PROJECT / rel, r['sha256']) == r['bound_file_count']
cp = WT / PROJECT / 'verification/linux-candidate-2026-09-12'
assert check_manifest(cp / 'ROOT-EVIDENCE-MANIFEST.json', CTX['root_packaging_manifest_sha256']) == 22
assert check_manifest(cp / 'EVIDENCE-MANIFEST.json', 'e4ea6506d3458e620fb6d3dc27587411c0ee3983b133d78b454fd51495a3deaa', False) == 18
config = json.loads((WT / PROJECT / 'comparator.json').read_text())
names = ['inducedNorm_semantics', 'witness_matrix_identities', 'fourth_power_norm_control',
         'witness_action_identities', 'witness_attainment', 'witness_norms',
         'witness_global_minimizers', 'not_rightInverseUniqueConjecture']
assert config == receipt['config']
assert config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
assert config['definition_names'] == []
assert config['theorem_names'] == ['NLA.IE23.' + name for name in names] == pack['exports'] == proof_freeze['completed_exports']
assert receipt['input_sha256']['comparator.json'] == pack['comparator_sha256']
assert receipt['input_sha256']['reviews/statement-config-supplement.json'] == pack['configuration_supplement_sha256']
for rel, digest in pack['metadata_sha256'].items():
    assert receipt['input_sha256'][rel] == digest
supp = json.loads((WT / PROJECT / 'reviews/statement-config-supplement.json').read_text())
assert len(supp['original_project_inputs_verified_unchanged']) == 32
for rel, digest in supp['original_project_inputs_verified_unchanged'].items():
    assert receipt['input_sha256'][archive if rel == 'README.md' else rel] == digest

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
            or job['name'].startswith('verify (IE-23,')]
assert len(selected) == 3
for job in selected:
    assert job['status'] == 'completed' and job['conclusion'] == 'success'
    assert all(step['status'] == 'completed' and step['conclusion'] == 'success' for step in job['steps'])
    raw = (OUT / f"job-{job['id']}.log").read_text()
    assert COMMIT in raw and '##[error]' not in raw
project_job = next(job for job in selected if job['name'].startswith('verify (IE-23,'))
project_job_log = (OUT / f"job-{project_job['id']}.log").read_text()
assert 'Manifest schema and comparator coverage: PASS (8 declarations)' in project_job_log
archives = []
for item in json.loads((OUT / 'artifact-metadata.json').read_text())['artifacts']:
    if item['name'] not in {'lean-IE-23', 'lean-checker-controls'}:
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
    job = project_job if item['name'] == 'lean-IE-23' else next(job for job in selected if job['name'] == 'checker-controls')
    raw = (OUT / f"job-{job['id']}.log").read_text()
    assert f"SHA256 digest of uploaded artifact zip is {sha(data)}" in raw
    assert f"Artifact ID {item['id']}" in raw
    archives.append({'name': item['name'], 'id': item['id'], 'sha256': sha(data), 'file_count': len(files)})
assert len(archives) == 2

controls = {}
for label, directory in [('checker-controls', S), ('IE-23 controls', V)]:
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
    phases = {
        'simple_match': 'Your solution is okay!',
        'simple_mismatch': "Challenge and solution constant kind don't match: 'comm'",
        'simple_axiom_issue': "Illegal axiom detected: 'helper'",
        'simple_kind_mismatch': "Illegal axiom detected: 'helper'",
        'type_mismatch': "Challenge and solution theorem statement do not match: 'checked'"}
    for case, phase in phases.items():
        block = comparator.split('\nCASE ' + case + '\n', 1)[1].split('\nCASE ', 1)[0]
        assert phase in block and ('required phase: ' + phase) in block
        assert block.count('Building Challenge') == block.count('Building Solution') == 1
        assert block.count('Exporting #[') == 2
    match_block = comparator.split('\nCASE simple_match\n', 1)[1].split('\nCASE ', 1)[0]
    assert 'Running Lean default kernel on solution.' in match_block
    assert 'Lean default kernel accepts the solution' in match_block
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
for module in ['Definitions', 'Norms', 'Matrices', 'FourthPower', 'Actions', 'Minimizers', 'Proof']:
    assert 'Built NLA.IE23.' + module in main
build_jobs = [int(value) for value in re.findall(r'Build completed successfully \((\d+) jobs\)\.', main)]
assert len(build_jobs) == 2 and all(n > 0 for n in build_jobs)
assert main.split('Building Solution', 1)[0].count('declaration uses `sorry`') == len(names)
assert 'warning:' not in main.split('Building Solution', 1)[1]
for name in config['theorem_names']:
    assert main.count(name) >= 3
axiom_records = re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]", main)
assert len(axiom_records) == main.count('depends on axioms:') == 16 == 16
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
                    for rel in ['NLA/IE23/Proof.lean', 'Solution.lean']}
assert assertion_counts == {'NLA/IE23/Proof.lean': 8, 'Solution.lean': 8}
assert sum(assertion_counts.values()) == len(axiom_records)
for rel in ['NLA/IE23/Proof.lean', 'Solution.lean']:
    proof_source = (WT / PROJECT / rel).read_text()
    assert 'set_option leancert.trust "kernel"' in proof_source
implementation_paths = sorted((WT / PROJECT / 'NLA/IE23').glob('*.lean')) + [WT / PROJECT / 'Solution.lean']
for p in implementation_paths:
    code = re.sub(r'/\-.*?\-/', '', p.read_text(), flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|interval_decide)\b', code), str(p)
assert ref1['retained_dependencies'] and ref2['actual_required_dependencies']

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
for label in ['lean-IE-23', 'lean-checker-controls']:
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
    assert len(archive.namelist()) == len(set(archive.namelist()))
    for item in archive.infolist():
        if item.is_dir(): continue
        assert not Path(item.filename).is_absolute() and '..' not in Path(item.filename).parts
        assert (item.external_attr >> 16) & 0o170000 != 0o120000
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
save('identity-verification.json', {'result': 'PASS for actual IE-23 and control jobs',
    'commit': COMMIT, 'run': RUN, 'project': PROJECT, 'input_files': receipt['input_sha256'],
    'complete_tracked_source_set_count': input_count, 'all_input_bytes_match_worktree_and_commit': True,
    'all_eight_implementation_hashes_match_both_final_referee_evidence_sets': True,
    'original_proof_freeze_sources_matched_and_retained': proof_freeze['source_files'],
    'independent_mathematical_review_hashes': pack['review_reports_preserved'], 'operational_reviewer_role': CTX['role'], 'archives': archives,
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
    'LeanCert_role': 'Explicit kernel trust auditing of a pure exact proof; no numerical interval certificate. The exact actual complex p-to-2 induced supremum, Moore-Penrose inverse, two distinct p=4 global minimizers over every complex right inverse and full original universal negation are bound to the two independent final mathematical reviews by the actual verified input set. This operational inspector authored the proof and is not an additional independent mathematical referee.'})
print(json.dumps({'selected_job_checks': 'PASS', 'complete_inputs': input_count, 'exports': len(names),
                  'original_archives': archives, 'overall_run_success_observed': overall_success}, indent=2))
