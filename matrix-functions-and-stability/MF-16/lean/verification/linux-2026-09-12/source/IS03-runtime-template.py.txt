"""Independent IS-03 actual Ubuntu operational audit by /root/leancert_examples.

Adapts this agent's retained IE-23 operational inspector, which reused
/root/formal_review_standards's MI-03 inspector and prior campaign audits.
IS-03 proof coauthors are /root and /root/solved_statement_inventory. This
reviewer authored neither statement nor proof and previously served as
independent final mathematical referee 1. Operational review adds no new
mathematical referee. Root separately accepts this actual evidence.
No new Lean execution, proof/source/config edit, dependency copy or download.
Original raw records are also read manually; all inventories include nested
manifests, excluding only their exact enclosing manifest where appropriate.
"""
from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess
import zipfile

OUT = Path(__file__).resolve().parent
CTX = json.loads((OUT / 'audit-context.json').read_text())
WT = Path(CTX['worktree'])
COMMIT, BASE, PROJECT, RUN = CTX['commit'], CTX['source_base'], CTX['project'], CTX['run']
vs = list((OUT / 'artifacts/lean-IS-03').glob('verify-*'))
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
assert input_count == CTX['expected_input_count'] == 303
for rel, digest in receipt['input_sha256'].items():
    data = retain_source(PROJECT + '/' + rel)
    assert sha(data) == digest and (WT / PROJECT / rel).read_bytes() == data, rel
(OUT / 'source/git-project-tree.txt').write_bytes(git('ls-tree', '-r', COMMIT, '--', PROJECT))
commit_data = git('cat-file', 'commit', COMMIT)
(OUT / 'source/git-commit.txt').write_bytes(commit_data)
assert re.search(rb'^author George Stepaniants <> ', commit_data, re.M)
assert re.search(rb'^committer George Stepaniants <> ', commit_data, re.M)
P = WT / PROJECT
archive = 'verification/linux-candidate-2026-09-12/README.statement.md'
proof_freeze_bytes = (P / 'verification/proof-freeze.json').read_bytes()
assert sha(proof_freeze_bytes) == CTX['proof_freeze_sha256']
proof_freeze = json.loads(proof_freeze_bytes)
statement_freeze = json.loads((P / 'reviews/statement-freeze.json').read_text())
assert sha((P/'reviews/statement-freeze.json').read_bytes()) == '588196a54decb127a814dc4860621505d6874a077295f3e30a782d7f28b8ac6c'
for freeze, count in [(proof_freeze,203),(statement_freeze,34)]:
    assert freeze['base'] == BASE and len(freeze['files']) == count
    assert len(freeze['source_files']) == 10
    for rel,digest in freeze['files'].items():
        assert receipt['input_sha256'][archive if rel == 'README.md' else rel] == digest, rel
assert proof_freeze['source_files'] == statement_freeze['source_files']
pack = json.loads((P/'verification/linux-candidate-2026-09-12/baseline.json').read_text())
assert len(pack['original_project_inputs']) == 288
for rel,rec in pack['original_project_inputs'].items():
    t = archive if rel == 'README.md' else rel
    assert receipt['input_sha256'][t] == rec['sha256']
    assert (P/t).stat().st_size == rec['bytes']
for rel,digest in pack['review_reports_and_manifests'].items():
    assert receipt['input_sha256'][rel] == digest
reports = {r: d for r,d in pack['review_reports_and_manifests'].items() if r.endswith('.md')}
assert reports['reviews/proof-referee-1.md'] == '6f9b0a80286cb200cbd2ea317591a8c1031eb8de7092d25f0a3f09df15c21652'
assert reports['reviews/proof-referee-2.md'] == 'e2d4e754be79026254e5d5cfbaf277d2c23e0d2ef5fff11a8c55b083001a9b01'
for rel in ['reviews/proof-referee-1.md','reviews/proof-referee-2.md']:
    assert CTX['proof_freeze_sha256'] in (P/rel).read_text()
ref1 = json.loads((P/'reviews/proof-referee-1-evidence/final-audit.json').read_text())
ref2 = json.loads((P/'reviews/proof-referee-2-evidence/final-integrity.json').read_text())
assert ref1['verdict'].startswith('APPROVE') and ref2['result'] == 'PASS'
assert ref1['freeze_sha256'] == CTX['proof_freeze_sha256']
assert ref1['frozen_project_inputs_unchanged'] == 203 and ref2['all_203_project_proof_freeze_inputs_preserved']
assert ref1['frozen_statement_inputs_unchanged'] == 34 and ref2['all_34_statement_inputs_preserved']
assert ref1['original_sources_unchanged'] == 10 and ref2['all_ten_original_Git_blobs_preserved']
assert ref1['safe_total_project_declarations'] == ref2['actual_project_declarations_traversed'] == 61
assert ref1['material_dependencies'] == 33 and ref2['required_actual_dependencies'] == 40
assert ref1['fresh_commands'] + ref1['additional_certificate_commands'] == ref2['fresh_source_commands'] == 11
assert ref1['candidate_kernel_axiom_checks'] == ref2['candidate_kernel_axiom_checks'] == 18
assert ref2['actual_retained_LeanCert_boolean_replayed_in_kernel']
assert len(ref1['proof_source_hashes']) == 8
for rel,rec in ref1['proof_source_hashes'].items():
    assert rec['safe_source_scan'] and rec['sha256'] == receipt['input_sha256'][rel]
for r in ['reviews/proof-referee-1-evidence/fresh-checks.json','reviews/proof-referee-2-evidence/fresh-checks.json']:
    record = json.loads((P/r).read_text())
    commands = record['commands'] if isinstance(record,dict) else record
    assert len(commands) == 10
    for step in commands:
        assert step['exit_code'] == 0
        assert receipt['input_sha256'][step['source']] == step['source_sha256']

# Exact scopes matter: reviewer manifests include parent-relative reports; the
# candidate preparer has a historical whole-project inventory, not a folder one.
# Exclude only each exact enclosing manifest, never a matching nested basename.
def check_manifest(path, expected, complete=True):
    assert sha(path.read_bytes()) == expected
    bound = json.loads(path.read_text())['files']
    actual = {str(p.relative_to(path.parent)) for p in path.parent.rglob('*') if p.is_file() and p != path}
    if complete:
        assert actual == {r for r in bound if not r.startswith('../')}, str(path)
    for rel, rec in bound.items():
        p = (path.parent / rel).resolve()
        assert p.is_relative_to(P.resolve())
        assert p.stat().st_size == rec['bytes'] and sha(p.read_bytes()) == rec['sha256'], rel
        assert receipt['input_sha256'][str(p.relative_to(P.resolve()))] == rec['sha256']
    return len(bound)
review_counts = {}
for rel,count in pack['review_evidence_bound_counts'].items():
    review_counts[rel] = check_manifest(P/rel, receipt['input_sha256'][rel])
    assert review_counts[rel] == count
cp = P/'verification/linux-candidate-2026-09-12/EVIDENCE-MANIFEST.json'
assert check_manifest(cp,'2f80b30b36059c084494a125e844bbb2ec5a5d021801b51b8f36960deae5b6d0',False) == 298
cpj = json.loads(cp.read_text())
bound_normalized = {str((cp.parent/r).resolve().relative_to(P.resolve())) for r in cpj['files']}
cp_rel = str(cp.relative_to(P))
root_files = {r for r in tracked if r.startswith('verification/root-candidate-2026-09-12/')}
assert len(root_files) == 4 and len(bound_normalized) == 298
assert bound_normalized | {cp_rel} | root_files == tracked
assert not (bound_normalized & root_files) and cp_rel not in bound_normalized
assert sum(Path(r).name == 'EVIDENCE-MANIFEST.json' for r in bound_normalized) == 4
root_path = P/'verification/root-candidate-2026-09-12/EVIDENCE-MANIFEST.json'
assert check_manifest(root_path, receipt['input_sha256'][str(root_path.relative_to(P))]) == 3
root_check = json.loads((root_path.parent/'ROOT-CHECKS.json').read_text())
assert root_check['preparer_input_count'] == 299
assert set(root_check['preparer_all_input_sha256']) == bound_normalized | {cp_rel}
for rel,digest in root_check['preparer_all_input_sha256'].items():
    assert receipt['input_sha256'][rel] == digest
for rel,digest in root_check['metadata_sha256'].items():
    assert receipt['input_sha256'][rel] == digest
config = json.loads((P/'comparator.json').read_text())
names = ['nonnegative_power_trace','witness_admissible','witness_polynomials',
         'trace_moment_certificate','negative_moment','counterexample','not_derivativeRealizabilityConjecture']
assert config == receipt['config']
assert config['theorem_names'] == ['NLA.IS03.'+n for n in names] == root_check['exact_exports']
assert config['permitted_axioms'] == ['propext','Classical.choice','Quot.sound']
assert config['definition_names'] == []
assert root_check['schema_exit_code'] == 0 and root_check['canonical_status'] == 'Solved'
save('candidate-review-binding.json', {'result':'PASS','candidate_inputs':303,'proof_freeze_inputs':203,
    'statement_freeze_inputs':34,'original_sources':10,'nonREADME_proof_inputs_unchanged':202,
    'historical_README_archive':archive,'historical_README_sha256':receipt['input_sha256'][archive],
    'prepackaging_inputs_preserved':288,'preparer_manifest_inputs':298,'preparer_including_outer':299,
    'preparer_nested_manifests_included':4,'root_acceptance_inputs_including_outer':4,
    'all_candidate_inputs_accounted_once':True,'review_evidence_counts':review_counts,
    'review_reports':reports,'referee1_dependency_count':33,'referee2_dependency_count':40,
    'both_safe_actual_project_declaration_counts':61,'both_fresh_command_counts':11,
    'scope':'Same two independent mathematical reviews; this independent operational role adds no mathematical referee.'})

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
assert len(jobs) == 12 == json.loads((OUT/'jobs.json').read_text())['total_count']
assert run['status'] == 'completed' and run['conclusion'] == 'success'
selected = [job for job in jobs if job['name'] in ['select', 'checker-controls']
            or job['name'].startswith('verify (IS-03,')]
assert len(selected) == 3
for job in selected:
    assert job['status'] == 'completed' and job['conclusion'] == 'success'
    assert all(step['status'] == 'completed' and step['conclusion'] == 'success' for step in job['steps'])
    raw = (OUT / f"job-{job['id']}.log").read_text()
    assert COMMIT in raw and '##[error]' not in raw
project_job = next(job for job in selected if job['name'].startswith('verify (IS-03,'))
project_job_log = (OUT / f"job-{project_job['id']}.log").read_text()
assert 'Manifest schema and comparator coverage: PASS (7 declarations)' in project_job_log
archives = []
for item in json.loads((OUT / 'artifact-metadata.json').read_text())['artifacts']:
    if item['name'] not in {'lean-IS-03', 'lean-checker-controls'}:
        continue
    data = (OUT / (item['name'] + '.zip')).read_bytes()
    assert sha(data) == item['digest'].removeprefix('sha256:')
    assert item['workflow_run']['head_sha'] == COMMIT and not item['expired']
    extracted = OUT / 'artifacts' / item['name']
    with zipfile.ZipFile(OUT / (item['name'] + '.zip')) as archive:
        assert archive.testzip() is None
        assert len(archive.namelist()) == len(set(archive.namelist()))
        for info in archive.infolist():
            assert not Path(info.filename).is_absolute() and '..' not in Path(info.filename).parts
            assert (info.external_attr >> 16) & 0o170000 != 0o120000
        files = {file.filename for file in archive.infolist() if not file.is_dir()}
        assert files == {str(path.relative_to(extracted)) for path in extracted.rglob('*') if path.is_file()}
        for rel in files:
            assert archive.read(rel) == (extracted / rel).read_bytes()
    job = project_job if item['name'] == 'lean-IS-03' else next(job for job in selected if job['name'] == 'checker-controls')
    raw = (OUT / f"job-{job['id']}.log").read_text()
    assert f"SHA256 digest of uploaded artifact zip is {sha(data)}" in raw
    assert f"Artifact ID {item['id']}" in raw
    archives.append({'name': item['name'], 'id': item['id'], 'sha256': sha(data), 'file_count': len(files)})
assert len(archives) == 2
assert receipt['tool_receipt']['lean_toolchain'] == 'leanprover/lean4:v4.33.1'
assert 'x86_64-unknown-linux-gnu' in receipt['tool_receipt']['lean_version']
assert receipt['tool_receipt']['platform'].startswith('Linux-')
assert locked_source_count == 58

controls = {}
for label, directory in [('checker-controls', S), ('IS-03 controls', V)]:
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
for module in ['Definitions', 'Algebra', 'Spectral', 'Witness', 'Newton', 'Numerical', 'Proof']:
    assert 'Built NLA.IS03.' + module in main
build_jobs = [int(value) for value in re.findall(r'Build completed successfully \((\d+) jobs\)\.', main)]
assert len(build_jobs) == 2 and all(n > 0 for n in build_jobs)
assert main.split('Building Solution', 1)[0].count('declaration uses `sorry`') == len(names)
assert 'warning:' not in main.split('Building Solution', 1)[1]
for name in config['theorem_names']:
    assert main.count(name) >= 3
axiom_records = re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]", main)
assert len(axiom_records) == main.count('depends on axioms:') == 18
assert len({name for name, _ in axiom_records}) == len(axiom_records)
assert all([value.strip() for value in axioms.split(',')] == config['permitted_axioms']
           for _, axioms in axiom_records)
for marker in ['Running Lean default kernel on solution.', 'Lean default kernel accepts the solution',
               'Your solution is okay!']:
    assert marker in main
assert main.rstrip().endswith('EXIT_STATUS=0')
save('axiom-verification.json', {'result': 'PASS', 'count': len(axiom_records),
    'declarations': {name: [value.strip() for value in axioms.split(',')] for name, axioms in axiom_records}})
implementation_paths = sorted((P/'NLA/IS03').glob('*.lean')) + [P/'Solution.lean']
assertion_counts = {str(p.relative_to(P)):p.read_text().count('#assert_trust kernel ') for p in implementation_paths}
assert sum(assertion_counts.values()) == 18
for rel in ['NLA/IS03/Numerical.lean','NLA/IS03/Proof.lean','Solution.lean']:
    assert 'set_option leancert.trust "kernel"' in (P/rel).read_text()
for p in implementation_paths:
    code = re.sub(r'/\-.*?\-/', '', p.read_text(), flags=re.S)
    code = re.sub(r'--[^\n]*', '', code)
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', code), str(p)
    assert not re.search(r'^import\s+Challenge\b',code,re.M)
num = (P/'NLA/IS03/Numerical.lean').read_text()
assert 'interval_decide' in num and '(-8593/823543 : ℝ) < 0' in num
save('source-trust-checks.json', {'result':'PASS','explicit_kernel_assertions':assertion_counts,
    'code_scan_inputs':{str(p.relative_to(P)):sha(p.read_bytes()) for p in implementation_paths},
    'material_numerical_consumer_bound_to_both_final_review_inputs':True,
    'scalar_scope':'Explicit kernel LeanCert rational singleton -8593/823543<0; no subdivision or approximate roots.'})

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
for label in ['lean-IS-03', 'lean-checker-controls']:
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

ids = json.loads((OUT/'permanent-id-run.json').read_text())
assert ids['id'] == CTX['permanent_id_run'] and ids['head_sha'] == COMMIT
assert ids['status'] == 'completed' and ids['conclusion'] == 'success'
idjobs = json.loads((OUT/'permanent-id-jobs.json').read_text())['jobs']
assert len(idjobs) == 1
for job in idjobs:
    assert job['conclusion'] == 'success'
    assert all(s['status'] == 'completed' and s['conclusion'] == 'success' for s in job['steps'])
    raw = (OUT/f"permanent-id-job-{job['id']}.log").read_text()
    assert COMMIT in raw and '##[error]' not in raw
    assert 'Ran 17 tests' in raw and 'OK' in raw
save('permanent-id-verification.json', {'result':'PASS','run':ids['id'],'commit':COMMIT,'jobs':[j['id'] for j in idjobs], 'scope':'Actual separate workflow at the same candidate; all steps and seventeen ID tests passed.'})
overall_success = run['status'] == 'completed' and run['conclusion'] == 'success'
if overall_success:
    assert all(job['status'] == 'completed' and job['conclusion'] == 'success' for job in jobs)
    assert all(step['conclusion'] == 'success' for job in jobs for step in job['steps'])
save('identity-verification.json', {'result': 'PASS for actual IS-03 and control jobs',
    'commit': COMMIT, 'run': RUN, 'project': PROJECT, 'input_files': receipt['input_sha256'],
    'complete_tracked_source_set_count': input_count, 'all_input_bytes_match_worktree_and_commit': True,
    'all_eight_implementation_hashes_match_final_referee_evidence_sets': True,
    'original_proof_freeze_sources_matched_and_retained': proof_freeze['source_files'],
    'independent_mathematical_review_hashes': reports, 'operational_reviewer_role': CTX['role'], 'archives': archives,
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
    'LeanCert_role': 'Explicit kernel LeanCert rational singleton -8593/823543<0 materially consumed in the original universal derivative-realizability negation. All actual arbitrary-real-matrix characteristic-polynomial, spectral, Newton and trace bridges are bound to the two independent final mathematical reviews by the verified source set. This operational inspector authored neither proof nor statement; its prior independent final referee 1 role is not an additional mathematical review.'})
print(json.dumps({'selected_job_checks': 'PASS', 'complete_inputs': input_count, 'exports': len(names),
                  'original_archives': archives, 'overall_run_success_observed': overall_success}, indent=2))
