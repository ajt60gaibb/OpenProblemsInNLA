"""Coordinator acceptance of IS-03 independent operational review; no mathematical rerun.
Adapted from the earlier root IE-23/IV-06 acceptance script.
"""
from pathlib import Path, PurePosixPath
from concurrent.futures import ThreadPoolExecutor
import datetime, hashlib, json, re, shutil, stat, subprocess, sys, zipfile

CASES = {
 'IS-03': {'tree': 'is03', 'category': 'eigenvalues-and-inverse-problems',
  'candidate': 'f87375fa5d7926fe0e065199eaab8f15ac5a5e48', 'run': 34728101436,
  'ids_run': 34728101524, 'inputs': 303, 'axioms': 18, 'graphs': [1718, 3101],
  'evidence_count': 444, 'evidence_sha': '66d3eef4f5a6b67f9d9aec94187af141cdda626b8c6d88b9b5c8e8e82c8ccd14',
  'report_sha': '97d43157105cc4abe654c5cd222a2e7928028d2f687f04ee3435ef6c589aff1f',
  'proof_freeze': 'verification/proof-freeze.json', 'freeze_count': 203,
  'role': 'Root is a statement/proof coauthor and independently accepts the separate operational inspection by leancert_examples. This is coordinator acceptance, not a third mathematical review.',
  'LeanCert': 'Material explicit kernel singleton -8593/823543<0 consumed through the seventh trace and full original universal negation'}
}
ID = sys.argv[1]; case = CASES[ID]
R = Path('/tmp/nla-lean-' + case['tree'] + '-worktree')
P = R / case['category'] / ID / 'lean'
E = P / 'verification/linux-2026-09-12'
O = P / 'verification/root-operational-2026-09-12'
O.mkdir(exist_ok=True)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
def git(*args): return subprocess.check_output(['git', *args], cwd=R)
assert git('rev-parse', 'HEAD').decode().strip() == case['candidate']
assert not git('diff', '--name-only').strip()
assert sha(E / 'OPERATIONAL-REVIEW.md') == case['report_sha']
outer = E / 'EVIDENCE-MANIFEST.json'
assert sha(outer) == case['evidence_sha']
em = json.loads(outer.read_text())
actual = {f.relative_to(E).as_posix() for f in E.rglob('*') if f.is_file() and f != outer}
assert actual == set(em['files']) and len(actual) == case['evidence_count']
for rel, rec in em['files'].items():
    f = E / rel
    assert not f.is_symlink() and f.resolve().is_relative_to(E.resolve())
    assert sha(f) == rec['sha256'] and f.stat().st_size == rec['bytes'], rel

gh = '/tmp/nla-submission-tools/gh_2.100.0_macOS_arm64/bin/gh'
prefix = 'repos/sgstepaniants/OpenProblemsInNLA/actions/'
endpoints = {'observed-run.json': prefix + 'runs/' + str(case['run']),
 'observed-jobs.json': prefix + 'runs/' + str(case['run']) + '/jobs?per_page=100',
 'observed-artifacts.json': prefix + 'runs/' + str(case['run']) + '/artifacts?per_page=100',
 'observed-permanent-ids.json': prefix + 'runs/' + str(case['ids_run'])}
def fetch(item):
    fn, endpoint = item
    b = subprocess.check_output([gh, 'api', endpoint], cwd=R)
    (O / fn).write_bytes(b)
    return fn, json.loads(b)
with ThreadPoolExecutor(max_workers=4) as pool: observed = dict(pool.map(fetch, endpoints.items()))
for fn in ['observed-run.json', 'observed-permanent-ids.json']:
    m = observed[fn]
    assert m['status'] == 'completed' and m['conclusion'] == 'success'
    assert m['head_sha'] == case['candidate']
jobs = observed['observed-jobs.json']
assert jobs['total_count'] == len(jobs['jobs']) == 12
for j in jobs['jobs']:
    assert j['head_sha'] == case['candidate'] and j['conclusion'] == 'success'
    assert all(s['status'] == 'completed' and s['conclusion'] == 'success' for s in j['steps'])

receipt_path = next((E / 'artifacts' / ('lean-' + ID)).rglob('result.json'))
receipt = json.loads(receipt_path.read_text()); B = receipt_path.parent
controls_path = next((E / 'artifacts/lean-checker-controls').rglob('result.json'))
control_receipt = json.loads(controls_path.read_text())
assert receipt['repository_commit'] == case['candidate'] and receipt['result'] == 'comparator-accepted'
assert control_receipt['result'] == 'checker-selftest-passed'
assert receipt['tool_receipt'] == control_receipt['tool_receipt']
tr = receipt['tool_receipt']
assert 'x86_64-unknown-linux-gnu' in tr['lean_version'] and tr['platform'].startswith('Linux-')
assert tr['lean_toolchain'] == 'leanprover/lean4:v4.33.1'
assert tr['ci_sandbox_probe_sha256'] == '31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803'
project_rel = P.relative_to(R).as_posix()
tracked = git('ls-tree', '-r', '--name-only', case['candidate'], '--', project_rel).decode().splitlines()
names = {s[len(project_rel)+1:] for s in tracked}
assert names == set(receipt['input_sha256']) and len(names) == case['inputs']
for rel, digest in receipt['input_sha256'].items():
    assert sha(P / rel) == digest
    assert sha(E / 'source' / project_rel / rel) == digest
    assert hashlib.sha256(git('show', case['candidate'] + ':' + project_rel + '/' + rel)).hexdigest() == digest
freeze = json.loads((P / case['proof_freeze']).read_text())
assert len(freeze['files']) == case['freeze_count'] and len(freeze['source_files']) == 10
for rel, rec in freeze['files'].items():
    f = P / ('verification/linux-candidate-2026-09-12/README.statement.md' if rel == 'README.md' else rel)
    assert isinstance(rec, str) and sha(f) == rec
for rel, digest in freeze['source_files'].items():
    assert sha(R / rel) == sha(E / 'source' / rel) == digest
    assert hashlib.sha256(git('show', 'f41f1f9ffa2171550d4bb795862c6170c4f26070:' + rel)).hexdigest() == digest

# Recheck the unusual historical whole-project manifest, including all nested
# manifests, instead of imposing a folder-local scope or basename exclusion.
statement = json.loads((P / 'reviews/statement-freeze.json').read_text())
assert len(statement['files']) == 34 and len(statement['source_files']) == 10
for rel, value in statement['files'].items():
    actual_file = P / ('verification/linux-candidate-2026-09-12/README.statement.md' if rel == 'README.md' else rel)
    digest = value if isinstance(value, str) else value['sha256']
    assert sha(actual_file) == digest, rel
preparer_path = P / 'verification/linux-candidate-2026-09-12/EVIDENCE-MANIFEST.json'
preparer = json.loads(preparer_path.read_text())
assert len(preparer['files']) == 298
prepared = {preparer_path.relative_to(P).as_posix()}
for rel, value in preparer['files'].items():
    actual_file = (preparer_path.parent / rel).resolve()
    assert actual_file.is_relative_to(P.resolve()) and actual_file != preparer_path.resolve()
    assert sha(actual_file) == value['sha256'] and actual_file.stat().st_size == value['bytes'], rel
    prepared.add(actual_file.relative_to(P.resolve()).as_posix())
assert len(prepared) == 299
root_candidate_dir = P / 'verification/root-candidate-2026-09-12'
root_candidate = {f.relative_to(P).as_posix() for f in root_candidate_dir.rglob('*') if f.is_file()}
assert len(root_candidate) == 4 and prepared.isdisjoint(root_candidate)
assert names == prepared | root_candidate
for kind, count in [('statement-referee-1', 23), ('statement-referee-2', 26),
                    ('proof-referee-1', 36), ('proof-referee-2', 45)]:
    directory = P / 'reviews' / (kind + '-evidence')
    bound = json.loads((directory / 'EVIDENCE-MANIFEST.json').read_text())
    assert len(bound['files']) == count
    for rel, value in bound['files'].items():
        f = directory / rel
        assert f.resolve().is_relative_to(P.resolve())
        expected = value if isinstance(value, str) else value['sha256']
        assert sha(f) == expected, (kind, rel)

config = json.loads((P / 'comparator.json').read_text())
assert config == receipt['config'] and len(config['theorem_names']) == 7
assert config['definition_names'] == [] and set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
log = (B / 'comparator.log').read_text()
assert 'Running Lean default kernel on solution.' in log and 'Lean default kernel accepts the solution' in log
assert 'Your solution is okay!' in log and log.rstrip().endswith('EXIT_STATUS=0')
assert 'RestrictAddressFamilies=~AF_UNIX' in log.splitlines()[0] and 'systemd-run --user' in log.splitlines()[0]
assert 'skip-kernel' not in log
for count in case['graphs']: assert f'Build completed successfully ({count} jobs).' in log
assert log.count('warning: Challenge.lean:') == 7
assert 'warning:' not in log.split('Building Solution', 1)[1]
axioms = re.findall(r"'([^']+)' depends on axioms: \[([^]]+)\]", log)
assert len(axioms) == case['axioms']
assert all(set(s.split(', ')) == {'propext', 'Classical.choice', 'Quot.sound'} for _, s in axioms)
exports = [s for s in log.splitlines() if s.startswith('Exporting #[')]
assert len(exports) == 2
for line in exports:
    assert all(n in line for n in config['theorem_names'])

for C in [B, controls_path.parent]:
    kernel = (C / 'kernel-controls.log').read_text()
    for expected in ['RETURN honest_with_inductives_and_quotients: accepted',
                     'RETURN invalid_raw_proof: rejected:', '(kernel) declaration type mismatch',
                     'RETURN quotient_postcheck_mismatch: rejected: Quotient constant mismatch on: Quot.lift',
                     'PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']:
        assert expected in kernel
    regress = (C / 'comparator-controls.log').read_text()
    assert regress.count('CASE ') == 5 and 'PASS: all five Comparator regressions' in regress
    assert regress.count('Building Challenge') == regress.count('Building Solution') == 5
    for text in ["constant kind don't match", "Illegal axiom detected: 'helper'", 'theorem statement do not match']:
        assert text in regress
    for kind, ax in [('sorry', 'sorryAx'), ('native', 'checked._native.native_decide.ax_1_1')]:
        neg = (C / ('negative-' + kind + '.log')).read_text()
        assert 'Building Challenge' in neg and 'Building Solution' in neg
        assert neg.count('Exporting #[') == 2 and "Illegal axiom detected: '" + ax + "'" in neg
        assert neg.rstrip().endswith('EXIT_STATUS=1')
    sandbox = (C / 'sandbox.log').read_text()
    assert sandbox.count('Sandbox UID: 1001') == 2
    for ns in ['user', 'pid', 'mnt', 'net', 'ipc', 'uts']:
        assert sandbox.count('PASS ' + ns + ' namespace: private') == 2
    for text in ['PASS effective capabilities: none', 'PASS no_new_privs: set',
                 'PASS AF_UNIX socket creation: denied', 'PASS host loopback listener: unreachable',
                 'PASS symlink from .lake to outside write: denied',
                 'bwrap: setting up uid map: Permission denied']:
        assert sandbox.count(text) == 2
    assert sandbox.count(': exit=2') == 4
    assert 'PASS build .lake write: allowed' in sandbox and 'PASS export .lake write-open: denied' in sandbox
    assert 'Outer and export fixture contents unchanged; only designated build fixture written.' in sandbox
    assert sandbox.rstrip().endswith('EXIT_STATUS=0')

lock = E / 'source/tools/lean/source-lock.json'
assert sha(lock) == receipt['source_lock_sha256'] == 'b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b'
locked = json.loads(lock.read_text())
assert locked['commit'] == tr['forsythe_commit'] == '8d1b0c0545a77b40245e84705aa7d273e6c81e62'
assert len(locked['files']) == 58
for rec in locked['files']:
    f = E / 'source/forsythe' / rec['destination']
    assert sha(f) == rec['sha256'] and f.stat().st_size == rec['bytes']
deps = (B / 'dependencies.log').read_text()
pins = json.loads((P / 'lake-manifest.json').read_text())['packages']
assert len(pins) == 10
for pin in pins: assert pin['name'] in deps and pin['rev'] in deps
assert '8690' in (B / 'mathlib-cache.log').read_text()

def zip_entries(path):
    with zipfile.ZipFile(path) as z:
        assert z.testzip() is None
        ns = z.namelist(); assert len(ns) == len(set(ns))
        for info in z.infolist():
            p = PurePosixPath(info.filename)
            assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(info.external_attr >> 16)
        return {n: z.read(n) for n in ns if not n.endswith('/')}
runlogs = zip_entries(E / 'run-logs.zip'); assert len(runlogs) == 152
runlog_text = '\n'.join(b.decode() for b in runlogs.values())
archives = []
for name in ['lean-' + ID, 'lean-checker-controls']:
    meta = next(a for a in observed['observed-artifacts.json']['artifacts'] if a['name'] == name)
    z = E / (name + '.zip'); digest = sha(z)
    assert meta['workflow_run']['head_sha'] == case['candidate'] and meta['workflow_run']['id'] == case['run']
    assert meta['digest'] == 'sha256:' + digest
    assert digest in runlog_text and str(meta['id']) in runlog_text
    entries = zip_entries(z)
    assert len(entries) == (13 if name == 'lean-' + ID else 10)
    for rel, data in entries.items(): assert (E / 'artifacts' / name / rel).read_bytes() == data
    archives.append({'name': name, 'id': meta['id'], 'sha256': digest, 'files': len(entries)})
assert git('show', '-s', '--format=%ae%x00%ce', case['candidate']).strip(b'\n') == b'\0'
assert '**Status:** Solved' in (P.parent / 'README.md').read_text()
record = {'status': 'APPROVE actual Ubuntu execution and immutable identity; publication preparation authorized',
 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'problem': ID, 'reviewer': '/root',
 'reviewer_role': case['role'], 'candidate': case['candidate'], 'run': case['run'], 'all_jobs_and_steps_success': 12,
 'canonical_status': 'Solved, unchanged at acceptance', 'matched_candidate_inputs': len(names),
 'frozen_proof_inputs': case['freeze_count'], 'original_source_Git_blobs': 10,
 'operational_report_sha256': case['report_sha'], 'operational_evidence_manifest_sha256': case['evidence_sha'],
 'all_evidence_files_verified': len(actual), 'all_nested_manifests_retained': True,
 'theorems': config['theorem_names'], 'actual_standard_three_reports': len(axioms),
 'graph_jobs_not_fresh_dependency_compile_counts': case['graphs'], 'exact_dependency_checkouts': 10,
 'official_Mathlib_cache_files': 8690, 'full_dependency_source_rebuild_claim': False,
 'actual_Comparator_and_default_kernel': 'accepted', 'two_actual_control_suites': 'all required phases observed',
 'nested_bwrap_limit': 'UID-map creation denied before any inner write, not evidence that inner write executed',
 'LeanCert_role': case['LeanCert'], 'locked_tool_sources': 58, 'archives': archives,
 'full_run_log_entries': 152, 'full_run_log_zip_sha256': sha(E / 'run-logs.zip'),
 'reading_scope': 'Root read complete operational report, actual project Comparator, kernel/regression/native/sorry/sandbox logs and structured receipts; independently rechecked all immutable inputs, actual GitHub run/artifact metadata, full inventories and both required control suites. The two independent mathematical referees are leancert_examples and formal_review_standards; root coauthored the proof and does not claim an independent mathematical review. No new local proof build is claimed.',
 'next_gate': 'Separate publication metadata and rendered canonical-document review, normal fork push and individual upstream PR'}
(O / 'ROOT-CHECKS.json').write_text(json.dumps(record, indent=2) + '\n')
shutil.copyfile(Path(__file__), O / Path(__file__).name)
fm = {f.relative_to(O).as_posix(): {'sha256': sha(f), 'bytes': f.stat().st_size}
      for f in sorted(O.rglob('*')) if f.is_file() and f != O / 'EVIDENCE-MANIFEST.json'}
(O / 'EVIDENCE-MANIFEST.json').write_text(json.dumps({'files': fm, 'file_count': len(fm),
    'inventory_rule': 'Every file below this directory excluding only its exact outer manifest path'}, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'problem': ID, 'root_acceptance_sha256': sha(O / 'ROOT-CHECKS.json'),
                  'root_manifest_sha256': sha(O / 'EVIDENCE-MANIFEST.json'), 'root_evidence_files': len(fm)}))
