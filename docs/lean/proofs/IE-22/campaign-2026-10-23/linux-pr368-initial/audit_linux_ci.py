#!/usr/bin/env python3
"""Offline independent audit of the original PR368 IE22 Linux CI receipt.

Reads retained GitHub metadata, original ZIP, decoded raw job log and immutable
Git objects. Does not run Lean, Comparator, a sandbox, CI or network requests.
"""
import argparse
import ast
from collections import Counter
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import zipfile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--evidence', type=Path,
                    default=Path(__file__).resolve().parent / 'retained')
args = parser.parse_args()
ROOT, OUT, EVIDENCE = args.repo.resolve(), args.output.resolve(), args.evidence.resolve()
OUT.mkdir(parents=True, exist_ok=True)
HEAD = '06f31cdd4f76d90c7590b5582b8db4975a0055d8'
BASE = '35b0d5c87779483beaa324b1bc7af4ba9e55ca18'
SOURCE = '353ebcfcbbcfc08184c32f391ecb6068c7d9098f'
PUBLISHED = '5487945e5a72abd952b0c89915915de8cc9b3e65'
PROJECT = 'linear-systems-and-elimination/IE-22/lean'
PROBLEM = 'linear-systems-and-elimination/IE-22/'
DOC = 'docs/lean/proofs/IE-22/campaign-2026-10-23/'
RUN, JOB, ARTIFACT = 40255260833, 121355717650, 12622124226
ZIP_SHA = '006c1919528d800bc18903d9f7f99633408cd0178f03d429bf57bd3489ef5468'
RAW_SHA = 'd679fea63d8044b0051bdafa2b53ff004a063f7395b187605a191a4952730d27'
NAMES = ['NLA.Proofs.IE22.' + n for n in
         ['uniform_squared_upper', 'near_sharp_unit_row_witness', 'target']]
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
checks = []
sha = lambda b: hashlib.sha256(b).hexdigest()
git = lambda *a: subprocess.check_output(['git', *a], cwd=ROOT)
read = lambda c, p: git('show', c + ':' + p)
load = lambda p: json.loads((EVIDENCE / p).read_text())


def check(name, passed, **details):
    checks.append(dict(name=name, passed=bool(passed), **details))
    if not passed:
        raise AssertionError(name)


run, jobs, pr, listing, art = (load(p) for p in
    ['run.json', 'jobs-raw.json', 'pr.json', 'artifacts.json', 'artifact-metadata.json'])
check('actual-workflow-terminal-success', run['id'] == RUN and
      run['event'] == 'pull_request' and run['status'] == 'completed' and
      run['conclusion'] == 'success' and run['head_sha'] == HEAD and run['run_attempt'] == 1)
check('run-PR368-head-base-binding', len(run['pull_requests']) == 1 and
      run['pull_requests'][0]['number'] == 368 and
      run['pull_requests'][0]['head']['sha'] == HEAD and
      run['pull_requests'][0]['base']['sha'] == BASE)
job = next(j for j in jobs['jobs'] if j['id'] == JOB)
check('exact-real-project-job-success', job['run_id'] == RUN and job['head_sha'] == HEAD and
      job['status'] == 'completed' and job['conclusion'] == 'success' and
      job['name'] == 'verify (IE-22, ' + PROJECT + ')')
check('all-required-project-steps-actually-succeeded', all(
      any(s['name'] == n and s['conclusion'] == 'success' for s in job['steps']) for n in
      ['Validate formalization manifest', 'Fresh sandboxed statement, axiom and kernel verification',
       'Retain verification logs']))
check('no-mislabelled-separate-checker-job', any(j['name'] == 'checker-controls' and
      j['conclusion'] == 'skipped' for j in jobs['jobs']))
check('live-PR-exact-head-base', pr['number'] == 368 and pr['head']['sha'] == HEAD and
      pr['base']['sha'] == BASE)
check('exact-original-artifact-listing-entry', listing['total_count'] == 1 and
      listing['artifacts'] == [art] and art['id'] == ARTIFACT and
      art['name'] == 'lean-IE-22' and not art['expired'] and
      art['workflow_run']['id'] == RUN and art['workflow_run']['head_sha'] == HEAD)
zip_data = (EVIDENCE / 'original-artifact.zip').read_bytes()
check('original-ZIP-digest-and-size', sha(zip_data) == ZIP_SHA and len(zip_data) == 18506 and
      art['digest'] == 'sha256:' + ZIP_SHA and art['size_in_bytes'] == len(zip_data))
gzip_data = (EVIDENCE / f'job-{JOB}.log.gz').read_bytes()
raw_data = gzip.decompress(gzip_data)
raw = raw_data.decode('utf-8')
check('exact-decoded-raw-job-UTF8-including-BOM-and-ANSI', sha(raw_data) == RAW_SHA and
      len(raw_data) == 106057 and raw.startswith('\ufeff') and '\x1b[' in raw)
# Derive the executed commit from the actual checkout command; do not infer it
# from head_sha or from today's synthetic-merge API field.
matches = re.findall(r'fetch[^\n]*\+([0-9a-f]{40}):refs/remotes/pull/368/merge', raw)
check('one-actual-PR368-merge-checkout', len(matches) == 1)
MERGE = matches[0]
check('raw-checkout-and-actual-git-log-agree',
      'git checkout --progress --force refs/remotes/pull/368/merge' in raw and
      f'HEAD is now at {MERGE[:8]} Merge {HEAD} into {BASE}' in raw and
      re.search(r'git log -1 --format=%H\n[^\n]* ' + MERGE + r'\n', raw) is not None)
check('actual-merge-object-parents-and-PR-corroboration',
      git('show', '-s', '--format=%P', MERGE).decode().split() == [BASE, HEAD] and
      pr['merge_commit_sha'] == MERGE)
check('raw-upload-digest-size-artifact-ID-URL', all(t in raw for t in
      ['SHA256 digest of uploaded artifact zip is ' + ZIP_SHA,
       f'Artifact lean-IE-22.zip successfully finalized. Artifact ID {ARTIFACT}',
       f'Final size is 18506 bytes. Artifact ID is {ARTIFACT}',
       f'/actions/runs/{RUN}/artifacts/{ARTIFACT}']))
members = {}
with zipfile.ZipFile(io.BytesIO(zip_data)) as z:
    check('original-ZIP-CRC-integrity', z.testzip() is None)
    for item in z.infolist():
        path = PurePosixPath(item.filename)
        check('safe-unique-ordinary-archive-member:' + item.filename,
              not item.is_dir() and not path.is_absolute() and '..' not in path.parts and
              '\\' not in item.filename and item.filename not in members and
              (item.external_attr >> 16) & 0o170000 != 0o120000 and not item.flag_bits & 1)
        members[item.filename] = z.read(item)
check('exact-fifteen-original-artifact-members', len(members) == 15)
rp = [p for p in members if p.endswith('/result.json')]
check('one-actual-harness-result', len(rp) == 1)
prefix = rp[0].removesuffix('result.json')
result = json.loads(members[rp[0]])
check('actual-receipt-executed-merge-project', result['repository_commit'] == MERGE and
      result['project'] == PROJECT)
check('actual-Comparator-and-LeanCert-kernel-acceptance',
      result['result'] == 'comparator-accepted' and
      result['lean_cert_proof_trust'] == 'kernel-checked' and
      result['verifier_profile'] == 'default')
cfg = result['config']
check('exact-three-Comparator-names-and-no-definition-holes',
      cfg == dict(challenge_module='Challenge', solution_module='Solution',
                  theorem_names=NAMES, definition_names=[],
                  permitted_axioms=['propext', 'Classical.choice', 'Quot.sound']))
expected = result['input_sha256']
head_paths = git('ls-tree', '-r', '--name-only', HEAD, PROJECT).decode().splitlines()
merge_paths = git('ls-tree', '-r', '--name-only', MERGE, PROJECT).decode().splitlines()
check('exact54-package-inputs-and-head-merge-file-sets', len(expected) == 54 and
      head_paths == merge_paths and
      set(expected) == {p.removeprefix(PROJECT + '/') for p in merge_paths})
check('exact27-Lean-inputs', sum(p.endswith('.lean') for p in expected) == 27)
inputs = []
for path, digest in expected.items():
    b = read(MERGE, PROJECT + '/' + path)
    check('all54-exact-head-merge-input:' + path,
          sha(b) == digest and b == read(HEAD, PROJECT + '/' + path))
    inputs.append(dict(path=path, sha256=digest, head_merge_equal=True))
checkpoint = json.loads(read(SOURCE, DOC + 'FULL_SOURCE_CHECKPOINT.json'))
copies = []
for x in checkpoint['files']:
    src = x['path']
    dest = src.removeprefix('lean-statements/')
    b = read(SOURCE, src)
    check('all23-reviewed-shared-canonical-copies:' + dest,
          sha(b) == x['sha256'] == expected[dest] and len(b) == x['bytes'] and
          b == read(HEAD, src) == read(MERGE, src) == read(MERGE, PROJECT + '/' + dest))
    copies.append(dict(shared_path=src, package_path=dest, sha256=x['sha256']))
check('reviewed-source-count23-proof-count19', len(copies) == 23 and
      sum(x['package_path'].startswith('NLA/Proofs/IE22/') for x in copies) == 19)
check('exact-approved-Challenge-config-and-frozen-identity',
      expected['Challenge.lean'] == 'bd20cbb3d4495ff312192ab29fe7722463c8b74861f0a00ae83dd9b98ed4ec79' and
      cfg == json.loads(read(MERGE, PROJECT + '/comparator.json')) and
      'NLA.Statements.IE22.Target = NLA.ReviewedStatements.IE22.Target := rfl' in
      read(MERGE, PROJECT + '/Identity.lean').decode())
check('original-canonical-target-page-ID-registry-preserved',
      read(MERGE, 'problem_ids.json') == read(PUBLISHED, 'problem_ids.json') and
      read(MERGE, PROBLEM + 'README.md') == read(PUBLISHED, PROBLEM + 'README.md') and
      b'**Status:** Solved' in read(MERGE, PROBLEM + 'README.md') and
      read(MERGE, PROBLEM + 'ORIGINAL.md') == read(PUBLISHED, PROBLEM + 'README.md'))
meta = json.loads(read(MERGE, PROJECT + '/formalization.yaml'))
check('verified-artifact-prepromotion-metadata-is-honest',
      meta['status']['whole_problem_verified'] is False and
      meta['status']['canonical_status'] != 'Lean verified' and
      [x['declaration'] for x in meta['status']['main_results']] == NAMES)
check('published-verifier-and-workflows-unchanged',
      git('diff', '--name-only', PUBLISHED, MERGE, '--', 'tools/lean', '.github/workflows') == b'')
lock_data = read(MERGE, 'tools/lean/source-lock.json')
lock = json.loads(lock_data)
tool = result['tool_receipt']
check('locked-Forsythe-tools-and-receipt-source-lock',
      sha(lock_data) == result['source_lock_sha256'] == tool['source_lock_sha256'] and
      lock['commit'] == tool['forsythe_commit'] == '8d1b0c0545a77b40245e84705aa7d273e6c81e62' and
      tool['profile'] == 'default')
check('actual-official-pinned-Linux-Lean-runtime',
      tool['lean_toolchain'] == 'leanprover/lean4:v4.33.1' and
      tool['lean_version'] == 'Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)' and
      tool['lean_version'] in raw and tool['platform'].startswith('Linux-') and
      tool['go_version'] == 'go version go1.27.1 linux/amd64')
# Recreate the audited deterministic consumer and independently invoke only
# the same frozen pure source-generating function, not the full harness.
lines = ['import Solution', 'import LeanCert.Tactic.Verification',
         'set_option autoImplicit false', 'set_option leancert.trust "kernel"', '',
         'open Lean Elab Command in',
         'elab "#assert_proof_constant " n:ident : command => do',
         '  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n',
         '  match (← getEnv).find? decl with',
         '  | some (.thmInfo _) => pure ()',
         '  | _ => throwErrorAt n "expected a proved theorem constant"', '']
for name in NAMES:
    lines += ['#assert_proof_constant ' + name, '#assert_trust kernel ' + name, '#print axioms ' + name]
consumer = '\n'.join(lines) + '\n'
harness_data = read(MERGE, 'tools/lean/harness.py')
tree = ast.parse(harness_data.decode())
fn = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'proof_trust_source')
ns = dict(MODULE=re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z"))
exec(compile(ast.Module(body=[fn], type_ignores=[]), '<frozen-pure-consumer-generator>', 'exec'), ns)
check('actual-generated-consumer-theorem-kind-kernel-hash',
      ns['proof_trust_source'](cfg) == consumer and
      sha(consumer.encode()) == result['lean_cert_proof_trust_source_sha256'])
log = lambda n: members[prefix + n + '.log'].decode()
trust = log('leancert-proof-trust')
check('actual-generated-consumer-executed-under-AF_UNIX-restriction',
      'ProofTrustAudit.lean' in trust and 'RestrictAddressFamilies=~AF_UNIX' in trust and
      trust.rstrip().endswith('EXIT_STATUS=0'))
axioms = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", trust)
check('all-three-actual-transitive-axiom-reports-standard-only',
      [n for n, _ in axioms] == NAMES and
      all({a.strip() for a in ax.split(',')} == STANDARD for _, ax in axioms))
comparator = log('comparator')
exports = [l for l in comparator.splitlines() if l.startswith('Exporting #[')]
check('actual-Comparator-exact-three-exports-both-modules', len(exports) == 2 and
      exports[0].endswith('from Challenge') and exports[1].endswith('from Solution') and
      all([n for n in re.findall(r'NLA\.Proofs\.IE22\.[A-Za-z_]+', line)] == NAMES
          for line in exports))
check('actual-default-kernel-and-Comparator-acceptance-raw-log',
      all(t in comparator for t in ['Building Challenge', 'Building Solution',
      'Running Lean default kernel on solution.', 'Lean default kernel accepts the solution',
      'Your solution is okay!']) and comparator.rstrip().endswith('EXIT_STATUS=0'))
kernel = log('kernel-controls')
for marker in ['RETURN honest_with_inductives_and_quotients: accepted',
               'RETURN invalid_raw_proof: rejected:',
               '(kernel) declaration type mismatch',
               'RETURN quotient_postcheck_mismatch: rejected:',
               'Quotient post-check rejects the solution',
               'PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']:
    check('actual-builtin-kernel-control:' + marker, marker in kernel)
reg = log('comparator-controls')
for name, code, marker in [
    ('simple_match', 0, 'Your solution is okay!'),
    ('simple_mismatch', 1, "Challenge and solution constant kind don't match: 'comm'"),
    ('simple_axiom_issue', 1, "Illegal axiom detected: 'helper'"),
    ('simple_kind_mismatch', 1, "Illegal axiom detected: 'helper'"),
    ('type_mismatch', 1, "Challenge and solution theorem statement do not match: 'checked'")]:
    check('actual-Comparator-regression:' + name,
          f'PASS {name}: exit {code}, expected {code}; required phase: {marker}' in reg)
check('all-five-real-Comparator-regressions-complete', 'PASS: all five Comparator regressions' in reg)
sandbox = log('sandbox')
check('real-build-and-export-sandbox-modes', 'MODE build: exit=0' in sandbox and
      'MODE export: exit=0' in sandbox)
for marker in ['outside .lake write-open: denied', 'outside .lake truncate: denied',
    'outside .lake read-only truncate-open: denied', 'symlink from .lake to outside write: denied',
    'outside .lake creation: denied', 'user namespace: private', 'pid namespace: private',
    'mnt namespace: private', 'net namespace: private', 'ipc namespace: private',
    'uts namespace: private', 'host parent: absent from private /proc',
    'host parent signal lookup: denied', 'host loopback listener: unreachable',
    'AF_UNIX socket creation: denied', 'effective capabilities: none', 'no_new_privs: set',
    'nested namespace write attempt: rejected']:
    check('both-real-sandbox-modes:' + marker, sandbox.count('PASS ' + marker) == 2)
check('only-designated-build-lake-writable-export-readonly', all(t in sandbox for t in
      ['PASS build .lake write: allowed', 'PASS export .lake write-open: denied',
       'PASS export .lake truncate: denied',
       'Outer and export fixture contents unchanged; only designated build fixture written.']))
for marker in ['unknown option', 'unexpected --rw', 'unexpected --rwx', 'relative --rwx']:
    check('actual-negative-sandbox-option:' + marker, 'NEGATIVE ' + marker + ': exit=2' in sandbox)
check('actual-sorry-admission-rejected', "Illegal axiom detected: 'sorryAx'" in
      log('negative-sorry') and log('negative-sorry').rstrip().endswith('EXIT_STATUS=1'))
check('actual-native-evaluation-axiom-rejected',
      "Illegal axiom detected: 'checked._native.native_decide.ax_1_1'" in log('negative-native') and
      log('negative-native').rstrip().endswith('EXIT_STATUS=1'))
manifest = json.loads(read(MERGE, PROJECT + '/lake-manifest.json'))
dependencies = log('dependencies')
check('ten-actual-pinned-dependencies', len(manifest['packages']) == 10)
for p in manifest['packages']:
    check('actual-dependency-pin:' + p['name'],
          "checking out revision '" + p['rev'] + "'" in dependencies)
pins = {p['name']: p['rev'] for p in manifest['packages']}
check('reviewed-Mathlib-LeanCert-pins',
      pins['mathlib'] == '0df444a360eaa60ab8c11dca51a86af692955474' and
      pins['leancert'] == '621a43d7cf21f87872392a01e874f2f1dbddc926')
check('actual-LeanCert-consumer-library-build-and-user-service',
      'lake build LeanCert.Tactic.Verification' in log('leancert-build') and
      'RestrictAddressFamilies=~AF_UNIX' in log('user-service'))
check('actual-bootstrap-pinned-checker-exporter-landrun-built',
      'lake build lean4export comparator' in members['bootstrap/comparator-build.log'].decode() and
      'go build -mod=readonly -buildvcs=false' in members['bootstrap/landrun-build.log'].decode())
# Every retained artifact log body must occur in order in the separately
# fetched raw GitHub job log; no reliance on result.json markers alone.
raw_lines = [re.sub(r'^\ufeff?\d{4}-\d\d-\d\dT[^ ]+Z ', '', l) for l in raw.splitlines()]
for path, b in sorted(members.items()):
    if not path.endswith('.log'):
        continue
    ls = b.decode().splitlines()
    expected_status = 1 if path.endswith(('negative-native.log', 'negative-sorry.log')) else 0
    check('actual-log-exit-status:' + path, ls[-1] == 'EXIT_STATUS=' + str(expected_status))
    check('actual-command-in-separate-raw-job:' + path, ls[0].startswith('$ ') and
          'Running ' + ls[0][2:] in raw_lines)
    position = 0
    for line in ls[1:]:
        if line and not line.startswith('EXIT_STATUS='):
            position = raw_lines.index(line, position) + 1
    check('every-log-body-line-bound-to-separate-raw-job:' + path, True)
check('raw-job-complete-fresh-harness-success',
      'PASS: fresh Comparator run and all controls. Evidence:' in raw)

retained = OUT / 'retained'
retained.mkdir(exist_ok=True)
for p in EVIDENCE.iterdir():
    if p.is_file() and p.resolve() != (retained / p.name).resolve():
        shutil.copyfile(p, retained / p.name)
for path, b in members.items():
    dest = retained / 'artifact' / path
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(b)
(OUT / 'reconstructed_ProofTrustAudit.lean.txt').write_text(consumer)
report = dict(
    reviewer='/root/inventory', date='2026-10-26', authored_IE22_proof_sources=[],
    scope='Independent audit of actual retained Linux GitHub CI evidence, with independent connector retrieval. No new local Lean, Comparator, sandbox or Linux replay.',
    verdict='APPROVE exact original PR368 Linux receipt for all three reviewed IE22 endpoints, including the literal unchanged full Target.',
    run=RUN, job=JOB, artifact=ARTIFACT, source_pr_head=HEAD, base=BASE,
    actual_executed_synthetic_merge=MERGE, reviewed_complete_source=SOURCE,
    archive_sha256=sha(zip_data), archive_bytes=len(zip_data), raw_job_utf8_sha256=sha(raw_data),
    raw_job_utf8_bytes=len(raw_data), raw_job_gzip_sha256=sha(gzip_data),
    run_completed_at=run['updated_at'], job_completed_at=job['completed_at'],
    input_count=len(expected), lean_input_count=27, reviewed_copy_count=len(copies),
    actual_selected_exports=NAMES, replaceable_definitions=[], permitted_axioms=sorted(STANDARD),
    proof_trust=result['lean_cert_proof_trust'], result=result['result'],
    result_sha256=sha(members[rp[0]]), consumer_sha256=sha(consumer.encode()),
    harness_sha256=sha(harness_data), source_lock_sha256=sha(lock_data), tool_receipt=tool,
    all54_head_merge_inputs=inputs, all23_reviewed_shared_copies=copies,
    artifact_member_sha256={p: sha(b) for p, b in sorted(members.items())},
    retained_original_source_sha256={p.name: sha(p.read_bytes()) for p in retained.iterdir() if p.is_file()},
    checks=checks, check_count=len(checks), passed=all(c['passed'] for c in checks),
    auditor_sha256=sha(Path(__file__).read_bytes()),
    limits=['The executed commit is the actual synthetic merge, not head06f31; all54 project inputs are identical at head and merge.',
            'The separate checker-controls job is skipped; the project verify job actually executes and retains the kernel, Comparator, sandbox and negative controls audited here.',
            'The artifact does not itself review English-to-Lean fidelity. Independent frozen pre-proof/source/package reviews separately establish that correspondence.',
            'This approval binds immutable receipt/source bytes; it does not promote status or claim merged/published main.'])
(OUT / 'INVENTORY_REVIEW.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: report[k] for k in ['passed', 'check_count', 'input_count', 'lean_input_count',
      'reviewed_copy_count', 'archive_sha256', 'actual_executed_synthetic_merge', 'verdict']}, indent=2))
