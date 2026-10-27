#!/usr/bin/env python3
"""Independent non-author offline audit of genuine final TR26 promotion Linux receipt bytes.

The inspected frozen author parser is extended with independently retrieved
connector/CLI originals, prior own package approval, all source/review mappings
and exact source-compile scope checks. No Lean, Comparator, sandbox or new CI
is executed here; those executions are proved by the genuine retained job.
"""
import argparse
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import zipfile
import functools

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo', type=Path, required=True)
p.add_argument('--evidence', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
p.add_argument('--head', required=True)
p.add_argument('--run', type=int, required=True)
p.add_argument('--compare-head', default='')
p.add_argument('--metadata', type=Path, required=True)
p.add_argument('--approved-package-review', type=Path, required=True)
p.add_argument('--promotion-review',type=Path,required=True)
p.add_argument('--expected-receipt',type=Path,required=True)
a = p.parse_args()
ROOT, EVIDENCE, OUT = a.repo.resolve(), a.evidence.resolve(), a.output.resolve()
OUT.mkdir(parents=True, exist_ok=True)
PROJECT = 'tensor-computations/TR-26/lean'
DOC = 'docs/lean/proofs/TR-26/campaign-2026-10-26/'
PUBLISHED = '5487945e5a72abd952b0c89915915de8cc9b3e65'
NAMES = ['NLA.Proofs.TR26.nonisotropic_degree', 'NLA.Proofs.TR26.isotropic_degree', 'NLA.Proofs.TR26.target']
SOURCE = 'ecc597cb68b65b473aecce9ac635e27d35c09694'
SUPERSEDED = 'f0fc0691c3496822e330894de60a9d6e94b7890a'
CANDIDATE='fa85c05acc70bbaa05bb3346fb43b57b1546af67'
PROMOTION='240e607ddc8f74d19f04e9ea1a64fe2bad1762b2'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
checks, details = [], {}
sha = lambda b: hashlib.sha256(b).hexdigest()
git = lambda *v: subprocess.check_output(['git', *v], cwd=ROOT)
# One persistent read-only Git object reader avoids thousands of separate
# Git startup/pack-index scans; every requested immutable blob is unchanged.
object_reader=subprocess.Popen(['git','cat-file','--batch'],cwd=ROOT,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
@functools.lru_cache(None)
def read(c,q):
    assert '\n' not in c+q and '\r' not in c+q
    object_reader.stdin.write((c+':'+q+'\n').encode());object_reader.stdin.flush()
    header=object_reader.stdout.readline().decode().rstrip('\n').split()
    if len(header)!=3 or header[1]!='blob':raise ValueError('Expected immutable Git blob: '+c+':'+q+' '+repr(header))
    body=object_reader.stdout.read(int(header[2]))
    if len(body)!=int(header[2]) or object_reader.stdout.read(1)!=b'\n':raise ValueError('Truncated Git batch blob: '+q)
    return body
load = lambda n: json.loads((EVIDENCE / n).read_text())

def check(name, passed, **extra):
    checks.append(dict(name=name, passed=bool(passed), **extra))
    if not passed:
        raise AssertionError(name)

def audit():
    run, jobs, listing, pr = (load(n) for n in ['run.json', 'jobs.json', 'artifacts.json', 'pr.json'])
    check('actual-PR369-workflow-terminal-success', run['id'] == a.run and
          run['event'] == 'pull_request' and run['status'] == 'completed' and
          run['conclusion'] == 'success' and run['head_sha'] == a.head and run['run_attempt'] == 1)
    prs = [x for x in run['pull_requests'] if x['number'] == 369]
    check('actual-run-head-commit-and-PR-identity', len(prs) == 1 and run['head_commit']['id'] == a.head)
    nested_base = prs[0]['base']['sha']
    project_jobs = [j for j in jobs['jobs'] if j['name'] == 'verify (TR-26, ' + PROJECT + ')']
    check('exact-one-actual-TR26-project-job', len(project_jobs) == 1)
    job = project_jobs[0]
    check('actual-project-job-success', job['run_id'] == a.run and job['head_sha'] == a.head and
          job['status'] == 'completed' and job['conclusion'] == 'success')
    check('actual-required-project-steps-succeeded', all(
          any(s['name'] == n and s['conclusion'] == 'success' for s in job['steps']) for n in
          ['Validate formalization manifest', 'Fresh sandboxed statement, axiom and kernel verification',
           'Retain verification logs']))
    artifacts = [x for x in listing['artifacts'] if x['name'] == 'lean-TR-26']
    check('exact-original-TR26-artifact-listing', len(artifacts) == 1)
    art = artifacts[0]
    check('artifact-bound-to-actual-run-head', not art['expired'] and
          art['workflow_run']['id'] == a.run and art['workflow_run']['head_sha'] == a.head and
          art == load('artifact-metadata.json'))
    archive = (EVIDENCE / 'original-artifact.zip').read_bytes()
    check('original-ZIP-API-digest-and-size', art['digest'] == 'sha256:' + sha(archive) and
          art['size_in_bytes'] == len(archive))
    raw_bytes = (EVIDENCE / f'job-{job["id"]}.log').read_bytes()
    raw_gzip = (EVIDENCE / f'job-{job["id"]}.log.gz').read_bytes()
    check('retained-raw-log-gzip-byte-identity', gzip.decompress(raw_gzip) == raw_bytes)
    raw = raw_bytes.decode('utf-8')
    merges = re.findall(r'fetch[^\n]*\+([0-9a-f]{40}):refs/remotes/pull/369/merge', raw)
    check('one-actually-executed-PR-merge-checkout', len(merges) == 1)
    merge = merges[0]
    checkout_summaries = re.findall(r'HEAD is now at ([0-9a-f]+) Merge ([0-9a-f]{40}) into ([0-9a-f]{40})', raw)
    check('one-actual-raw-checkout-summary',len(checkout_summaries)==1)
    base = checkout_summaries[0][2]
    check('actual-checkout-command-and-git-log',
          'git checkout --progress --force refs/remotes/pull/369/merge' in raw and
          len(checkout_summaries) == 1 and merge.startswith(checkout_summaries[0][0]) and
          checkout_summaries[0][1:] == (a.head, base) and
          re.search(r'git log -1 --format=%H\n[^\n]* ' + merge + r'\n', raw) is not None)
    check('executed-merge-object-parents', git('show', '-s', '--format=%P', merge).decode().split() == [base, a.head])
    check('exact-CCC-base-and240e-final-promotion-parents',base=='ccc7864f5034cf7c4602f7577ceaf083ebf63d52' and a.head==PROMOTION)
    check('actual-upload-artifact-digest-ID-size', all(t in raw for t in [
          'SHA256 digest of uploaded artifact zip is ' + sha(archive),
          f'Artifact lean-TR-26.zip successfully finalized. Artifact ID {art["id"]}',
          f'Final size is {len(archive)} bytes. Artifact ID is {art["id"]}',
          f'/actions/runs/{a.run}/artifacts/{art["id"]}']))
    members = {}
    with zipfile.ZipFile(io.BytesIO(archive)) as z:
        check('original-ZIP-CRC-integrity', z.testzip() is None)
        for info in z.infolist():
            q = PurePosixPath(info.filename)
            check('safe-unique-ordinary-member:' + info.filename,
                  not info.is_dir() and not q.is_absolute() and '..' not in q.parts and
                  '\\' not in info.filename and info.filename not in members and
                  (info.external_attr >> 16) & 0o170000 != 0o120000 and not info.flag_bits & 1)
            members[info.filename] = z.read(info)
    results = [q for q in members if q.endswith('/result.json')]
    check('one-actual-harness-receipt', len(results) == 1)
    prefix = results[0].removesuffix('result.json')
    result = json.loads(members[results[0]])
    check('actual-receipt-executed-merge-and-project', result['repository_commit'] == merge and result['project'] == PROJECT)
    check('actual-Comparator-and-LeanCert-kernel-acceptance', result['result'] == 'comparator-accepted' and
          result['lean_cert_proof_trust'] == 'kernel-checked' and result['verifier_profile'] == 'default')
    cfg = result['config']
    check('three-exact-full-target-exports-no-replaceable-definitions', cfg == dict(challenge_module='Challenge',
          solution_module='Solution', theorem_names=NAMES, definition_names=[],
          permitted_axioms=['propext', 'Classical.choice', 'Quot.sound']))
    inputs = result['input_sha256']
    paths = git('ls-tree', '-r', '--name-only', a.head, PROJECT).decode().splitlines()
    check('exact857-input-set-856-lock-plus-lock-itself', len(paths) == len(inputs) == 857 and
          set(inputs) == {q.removeprefix(PROJECT + '/') for q in paths})
    check('head-and-executed-merge-package-file-sets-identical', paths ==
          git('ls-tree', '-r', '--name-only', merge, PROJECT).decode().splitlines())
    package_lock = json.loads(read(a.head, PROJECT + '/PACKAGE_LOCK.json'))
    check('exact856-package-lock-entries', len(package_lock['files']) == 856 and
          set(package_lock['files']) == set(inputs) - {'PACKAGE_LOCK.json'})
    review_binding = json.loads(read(a.head, PROJECT + '/reviews/FULL_SOURCE_REVIEW_BINDINGS.json'))
    omitted = 'reviews/full-target-review/verification/__pycache__/reproduce.cpython-313.pyc'
    check('corrected-full-review-binding-is-complete', review_binding['proof_source_ref'] == SOURCE and
          len(review_binding['files']) == 332 and
          len(review_binding['omitted_regenerable_artifacts']) == 1 and
          review_binding['omitted_regenerable_artifacts'][0]['path'] == omitted and
          omitted not in inputs and omitted not in package_lock['files'])
    for entry in review_binding['files']:
        q = entry['path']
        check('all332-existing-review-evidence-bindings:' + q,
              inputs[q] == entry['sha256'] == package_lock['files'][q]['sha256'] and
              entry['bytes'] == package_lock['files'][q]['bytes'])
    for q, digest in inputs.items():
        b = read(a.head, PROJECT + '/' + q)
        check('exact-head-merge-input:' + q, sha(b) == digest and b == read(merge, PROJECT + '/' + q))
        if q in package_lock['files']:
            e = package_lock['files'][q]
            check('exact-reviewed-package-lock:' + q, e['sha256'] == digest and e['bytes'] == len(b))
        if a.compare_head:
            check('exact-metadata-correction-head-package-input:' + q, b == read(a.compare_head, PROJECT + '/' + q))
    runtime = [q for q in inputs if q.endswith('.lean') and not q.startswith('reviews/')]
    check('exact84-runtime-Lean-sources', len(runtime) == 84)
    executable_and_pins = runtime + ['controls/ChallengeTrustRejection.lean.txt',
        'controls/CustomAxiomRejection.lean.txt', 'controls/DefinitionKindRejection.lean.txt',
        'comparator.json', 'lake-manifest.json', 'lakefile.toml', 'lean-toolchain', 'reproduce.py']
    check('exact92-executable-and-pin-inputs', len(executable_and_pins) == 92)
    for q in executable_and_pins:
        check('corrected92-executable-and-pin-inputs-unchanged:' + q,
              read(a.head, PROJECT + '/' + q) == read(SUPERSEDED, PROJECT + '/' + q))
    correction = json.loads(read(a.head, DOC + 'FULL_PACKAGE_EXPORT_CORRECTION.json'))
    check('correction-record-binds-actual-complete-lock',
          correction['superseded_candidate'] == SUPERSEDED and
          correction['corrected_locked_inputs'] == 856 and correction['corrected_total_files'] == 857 and
          correction['corrected_package_lock_sha256'] == sha(read(CANDIDATE, PROJECT+'/PACKAGE_LOCK.json')) and
          correction['unchanged_executable_or_pin_inputs'] == 92 and correction['proof_source_ref'] == SOURCE)
    checkpoint = json.loads(read(SOURCE, DOC + 'FULL_TARGET_SOURCE_FREEZE.json'))
    preparation = json.loads(read(a.head, DOC + 'FULL_TARGET_PACKAGE_PREPARATION.json'))
    check('full-package-binds-exact-reviewed-full-source', package_lock['proof_source_ref'] == SOURCE and
          preparation['proof_source_ref'] == SOURCE and preparation['locked_inputs'] == 856 and
          preparation['total_files'] == 857 and preparation['runtime_Lean_inputs'] == 84 and
          preparation['shared_runtime_copies'] == 80 and preparation['selected_theorems'] == NAMES)
    for entry in checkpoint['proof_inputs'] + checkpoint['shared_inputs']:
        q = entry['path'].removeprefix('lean-statements/')
        b = read(SOURCE, entry['path'])
        check('exact-reviewed-full-source-shared-runtime-copy:' + q,
              sha(b) == entry['sha256'] == inputs[q] and len(b) == entry['bytes'] and
              b == read(a.head, entry['path']) == read(merge, entry['path']) == read(merge, PROJECT + '/' + q))
    check('exact77-proof-plus3-shared-runtime-copies', len(checkpoint['proof_inputs']) == 77 and
          len(checkpoint['shared_inputs']) == 3)
    preproof = json.loads(read(a.head, DOC + 'preproof/INPUT_LOCK.json'))
    check('exact24-frozen-original-inputs', len(preproof['reviewed_inputs']) == 24)
    for entry in preproof['reviewed_inputs']:
        b=read(a.head,'tensor-computations/TR-26/ORIGINAL.md') if entry['path']=='tensor-computations/TR-26/README.md' else read(a.head,entry['path'])
        merged_original=read(merge,'tensor-computations/TR-26/ORIGINAL.md') if entry['path']=='tensor-computations/TR-26/README.md' else read(merge,entry['path'])
        check('frozen-original-preserved:' + entry['path'],sha(b)==entry['sha256'] and len(b)==entry['bytes'] and b==merged_original)
    check('approved-Challenge-and-Comparator-config', inputs['Challenge.lean'] ==
          '122ad60aaddf59e91dacd627637cf7237b8614d83b6d2eead381a76a698d7aba' and
          json.loads(read(merge, PROJECT + '/comparator.json')) == cfg)
    endpoint_audit = read(merge, PROJECT + '/EndpointAudit.lean').decode()
    check('full-package-retains-all-three-proved-theorem-kind-guards',
          all('#package_theorem ' + n in endpoint_audit and '#assert_trust kernel ' + n in endpoint_audit
              for n in NAMES) and '#package_absent' not in endpoint_audit)
    check('literal-full-frozen-Target-identity',
          'NLA.Statements.TR26.Target = NLA.ReviewedStatements.TR26.Target := rfl' in
          read(merge, PROJECT + '/Identity.lean').decode() and
          'NLA.Proofs.TR26.target' in endpoint_audit)
    formal = json.loads(read(merge, PROJECT + '/formalization.yaml'))
    check('final-promoted-metadata-full-target-exact', formal['status']['whole_problem_verified'] is True and
          formal['status']['canonical_status'] == 'Lean verified' and formal['status']['phase'] == 'full-target-verified' and
          [x['declaration'] for x in formal['status']['main_results']] == NAMES)
    check('original-ID-registry-and-target-preserved', read(merge, 'problem_ids.json') == read(PUBLISHED, 'problem_ids.json') and
          read(merge, 'tensor-computations/TR-26/ORIGINAL.md') == read(PUBLISHED, 'tensor-computations/TR-26/README.md') and
          read(merge, PROJECT + '/sources/ORIGINAL.md') == read(PUBLISHED, 'tensor-computations/TR-26/README.md') and
          read(merge, 'docs/lean/statements/TR-26/ORIGINAL.md') == read(PUBLISHED, 'tensor-computations/TR-26/README.md'))
    previous_README=read(PUBLISHED,'tensor-computations/TR-26/README.md').decode()
    current_README=read(merge,'tensor-computations/TR-26/README.md').decode()
    check('entire-promoted-mathematical-historical-suffix-unchanged',current_README[current_README.index('## Problem statement'):]==previous_README[previous_README.index('## Problem statement'):])
    insertion_start=current_README.index('## Lean proof and verification evidence')
    insertion_end=current_README.index('## Problem statement')
    restored=(current_README[:insertion_start]+current_README[insertion_end:]).replace('**Status:** Lean verified','**Status:** Solved').replace('**Last checked:** 2026-10-26','**Last checked:** 2026-09-11')
    check('only-explicit-status-date-Lean-evidence-addition',restored==previous_README)
    check('exact-final-canonical-metadata-lock-input-bytes',inputs['formalization.yaml']=='fc273a6f7c4610acf3392cb5b318b8be0c38b78068c38fd8d2deb7bb4a8d3475' and inputs['PACKAGE_LOCK.json']=='bf8432fa222f7cfb33047b7ebd51dbaf1b89d5153106469045acc0cdbc313aaf')
    check('published-harness-and-workflows-unchanged',
          git('diff', '--name-only', PUBLISHED, merge, '--', 'tools/lean', '.github/workflows') == b'')
    lock_data = read(merge, 'tools/lean/source-lock.json')
    lock, tool = json.loads(lock_data), result['tool_receipt']
    check('exact-locked-Forsythe-checker-source', sha(lock_data) == result['source_lock_sha256'] == tool['source_lock_sha256'] and
          lock['commit'] == tool['forsythe_commit'] == '8d1b0c0545a77b40245e84705aa7d273e6c81e62' and tool['profile'] == 'default')
    check('actual-tool-binary-and-environment-digest-fields-complete',set(tool['executables'])=={'.tools/comparator/.lake/build/bin/comparator','.tools/lean4export/.lake/build/bin/lean4export','.tools/bin/landrun'} and all(re.fullmatch(r'[0-9a-f]{64}',v) is not None for v in list(tool['executables'].values())+[tool['env_sha256']]))
    check('actual-official-Linux-Lean-platform', tool['lean_toolchain'] == 'leanprover/lean4:v4.33.1' and
          tool['lean_version'] == 'Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)' and
          tool['lean_version'] in raw and tool['platform'].startswith('Linux-') and
          tool['go_version'] == 'go version go1.27.1 linux/amd64')
    harness = read(merge, 'tools/lean/harness.py')
    harness_tree=ast.parse(harness.decode())
    validated_fn=next(n for n in harness_tree.body if isinstance(n,ast.FunctionDef) and n.name=='validated_tools')
    verify_fn=next(n for n in harness_tree.body if isinstance(n,ast.FunctionDef) and n.name=='verify')
    validated_text=ast.get_source_segment(harness.decode(),validated_fn)
    check('actual-published-harness-validates-each-tool-binary-before-verification',any(isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='validated_tools' for n in ast.walk(verify_fn)) and all(t in validated_text for t in ['for name, expected in receipt["executables"].items():','if digest(file) != expected:','modified checker executable:','if digest(tool_dir / ".tools/env.sh") != receipt["env_sha256"]:']))
    fn = next(n for n in ast.parse(harness.decode()).body if isinstance(n, ast.FunctionDef) and n.name == 'proof_trust_source')
    ns = dict(MODULE=re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z"))
    exec(compile(ast.Module(body=[fn], type_ignores=[]), '<frozen-pure-source-generator>', 'exec'), ns)
    consumer = ns['proof_trust_source'](cfg)
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
    expected_consumer = '\n'.join(lines) + '\n'
    check('actual-generated-theorem-kind-kernel-consumer-hash', consumer == expected_consumer and
          sha(consumer.encode()) == result['lean_cert_proof_trust_source_sha256'])
    log = lambda n: members[prefix + n + '.log'].decode()
    trust, comparator = log('leancert-proof-trust'), log('comparator')
    check('actual-kernel-consumer-ran-under-restriction', 'ProofTrustAudit.lean' in trust and
          'RestrictAddressFamilies=~AF_UNIX' in trust and trust.rstrip().endswith('EXIT_STATUS=0'))
    axioms = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", trust)
    check('actual-selected-theorem-transitive-axioms-standard-only', [n for n, _ in axioms] == NAMES and
          all({x.strip() for x in xs.split(',')} == STANDARD for _, xs in axioms))
    exports = [line for line in comparator.splitlines() if line.startswith('Exporting #[')]
    check('actual-Comparator-compared-three-exact-full-target-exports', len(exports) == 2 and
          exports[0].endswith('from Challenge') and exports[1].endswith('from Solution') and
          all(re.findall(r'NLA\.Proofs\.TR26\.[A-Za-z_]+', line) == NAMES for line in exports))
    check('actual-default-kernel-and-Comparator-acceptance', all(t in comparator for t in
          ['Building Challenge', 'Building Solution', 'Running Lean default kernel on solution.',
           'Lean default kernel accepts the solution', 'Your solution is okay!']) and comparator.rstrip().endswith('EXIT_STATUS=0'))
    for marker in ['RETURN honest_with_inductives_and_quotients: accepted',
                   'RETURN invalid_raw_proof: rejected:', '(kernel) declaration type mismatch',
                   'RETURN quotient_postcheck_mismatch: rejected:', 'Quotient post-check rejects the solution',
                   'PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']:
        check('actual-kernel-control:' + marker, marker in log('kernel-controls'))
    for name, code, marker in [
            ('simple_match', 0, 'Your solution is okay!'),
            ('simple_mismatch', 1, "Challenge and solution constant kind don't match: 'comm'"),
            ('simple_axiom_issue', 1, "Illegal axiom detected: 'helper'"),
            ('simple_kind_mismatch', 1, "Illegal axiom detected: 'helper'"),
            ('type_mismatch', 1, "Challenge and solution theorem statement do not match: 'checked'")]:
        check('actual-Comparator-regression:' + name,
              f'PASS {name}: exit {code}, expected {code}; required phase: {marker}' in log('comparator-controls'))
    check('actual-five-Comparator-regressions-complete', 'PASS: all five Comparator regressions' in log('comparator-controls'))
    check('actual-sandbox-build-and-export-modes', 'MODE build: exit=0' in log('sandbox') and
          'MODE export: exit=0' in log('sandbox'))
    for marker in ['outside .lake write-open: denied', 'outside .lake truncate: denied',
                   'outside .lake read-only truncate-open: denied', 'symlink from .lake to outside write: denied',
                   'outside .lake creation: denied', 'user namespace: private', 'pid namespace: private',
                   'mnt namespace: private', 'net namespace: private', 'ipc namespace: private', 'uts namespace: private',
                   'host parent: absent from private /proc', 'host parent signal lookup: denied',
                   'host loopback listener: unreachable', 'AF_UNIX socket creation: denied',
                   'effective capabilities: none', 'no_new_privs: set', 'nested namespace write attempt: rejected']:
        check('actual-build-and-export-isolation:' + marker, log('sandbox').count('PASS ' + marker) == 2)
    check('only-designated-build-lake-writable-export-readonly', all(t in log('sandbox') for t in
          ['PASS build .lake write: allowed', 'PASS export .lake write-open: denied',
           'PASS export .lake truncate: denied',
           'Outer and export fixture contents unchanged; only designated build fixture written.']))
    for marker in ['unknown option', 'unexpected --rw', 'unexpected --rwx', 'relative --rwx']:
        check('actual-negative-sandbox-option:' + marker,
              'NEGATIVE ' + marker + ': exit=2' in log('sandbox'))
    check('actual-sorry-rejection', "Illegal axiom detected: 'sorryAx'" in log('negative-sorry') and
          log('negative-sorry').rstrip().endswith('EXIT_STATUS=1'))
    check('actual-native-axiom-rejection', "Illegal axiom detected: 'checked._native.native_decide.ax_1_1'" in
          log('negative-native') and log('negative-native').rstrip().endswith('EXIT_STATUS=1'))
    manifest = json.loads(read(merge, PROJECT + '/lake-manifest.json'))
    pins = {x['name']: x['rev'] for x in manifest['packages']}
    check('exact-Mathlib-and-LeanCert-pins', pins['mathlib'] == '0df444a360eaa60ab8c11dca51a86af692955474' and
          pins['leancert'] == '621a43d7cf21f87872392a01e874f2f1dbddc926' and len(pins) == 10)
    for name, rev in pins.items():
        check('actual-dependency-pin:' + name, "checking out revision '" + rev + "'" in log('dependencies'))
    check('actual-LeanCert-library-build-and-user-service',
          'lake build LeanCert.Tactic.Verification' in log('leancert-build') and
          'RestrictAddressFamilies=~AF_UNIX' in log('user-service'))
    check('actual-bootstrap-built-pinned-checker-and-landrun',
          'lake build lean4export comparator' in members['bootstrap/comparator-build.log'].decode() and
          'go build -mod=readonly -buildvcs=false' in members['bootstrap/landrun-build.log'].decode())
    raw_lines = [re.sub(r'^\ufeff?\d{4}-\d\d-\d\dT[^ ]+Z ', '', line) for line in raw.splitlines()]
    for q, body in sorted(members.items()):
        if not q.endswith('.log'):
            continue
        lines = body.decode().splitlines()
        status = 1 if q.endswith(('negative-native.log', 'negative-sorry.log')) else 0
        check('actual-log-exit-status:' + q, lines[-1] == 'EXIT_STATUS=' + str(status))
        check('artifact-command-in-separate-raw-job:' + q, lines[0].startswith('$ ') and
              'Running ' + lines[0][2:] in raw_lines)
        position = 0
        for line in lines[1:]:
            if line and not line.startswith('EXIT_STATUS='):
                position = raw_lines.index(line, position) + 1
        check('all-artifact-log-lines-bound-to-raw-job:' + q, True)
    check('raw-job-complete-harness-success', 'PASS: fresh Comparator run and all controls. Evidence:' in raw)
    check('actual-ubuntu2404-GitHub-project-runner',job['labels']==['ubuntu-24.04'] and job['runner_name'].startswith('GitHub Actions '))
    probe_bytes=read(merge,'docs/lean/verification/2026-09-12/source/forsythe/reproduction/checks/sandbox_probe.py')
    probe_pin=next(x for x in lock['files'] if x['destination']=='reproduction/checks/sandbox_probe.py')
    check('original-sandbox-probe-source-lock-byte-binding',sha(probe_bytes)==probe_pin['sha256'] and len(probe_bytes)==probe_pin['bytes'])
    probe_fn=next(n for n in ast.parse(harness.decode()).body if isinstance(n,ast.FunctionDef) and n.name=='ci_probe_source')
    probe_ns={'Path':Path}
    exec(compile(ast.Module(body=[probe_fn],type_ignores=[]),'<frozen-CI-probe-generator>','exec'),probe_ns)
    class ProbeSource:
        def __truediv__(self,q): return self
        def read_text(self): return probe_bytes.decode()
    probe_generated=probe_ns['ci_probe_source'](ProbeSource())
    check('actual-generated-CI-sandbox-probe-source-byte-binding',sha(probe_generated.encode())==tool['ci_sandbox_probe_sha256'])
    proof_modules=[x['path'].removeprefix('lean-statements/').removesuffix('.lean').replace('/','.') for x in checkpoint['proof_inputs']]
    check('all77-actual-proof-modules-built-in-Linux-Comparator',len(proof_modules)==77 and all(re.search(r'(?:Built|Replayed) '+re.escape(m)+r'\b',comparator) is not None for m in proof_modules))
    # Non-author extensions bind independently fetched connector/CLI bytes to
    # the already independently reviewed complete canonical source snapshot.
    expected_bytes=a.expected_receipt.read_bytes();expected=json.loads(expected_bytes)
    check('fixed-expected-real-final-run-job-artifact-identities',a.run==40400589674 and job['id']==121845350715 and a.head==PROMOTION and expected['run']==a.run and expected['head']==a.head and expected['job']==job['id'] and expected['artifact']==art['id'])
    check('fixed-original-final-ZIP-and-raw-log-byte-hashes',sha(archive)==expected['archive_sha256'] and len(archive)==expected['archive_bytes'] and sha(raw_bytes)==expected['raw_log_sha256'] and len(raw_bytes)==expected['raw_log_bytes'])
    check('original-UTF8-BOM-ANSI-preserved',raw.startswith('\ufeff') and '\x1b[' in raw)
    connector_art=json.loads((a.metadata/'connector-artifacts.json').read_text())['artifacts']
    check('independently-fetched-GitHub-connector-artifact-agrees',len(connector_art)==1 and all(connector_art[0][k]==art[k] for k in ['id','name','size_in_bytes','digest','expired','workflow_run']))
    connector_jobs=json.loads((a.metadata/'connector-jobs.json').read_text())['jobs']
    cj=next(x for x in connector_jobs if x['id']==job['id'])
    check('independently-fetched-GitHub-connector-job-agrees',all(cj[k]==job[k] for k in ['id','name','run_id','status','conclusion']))
    connector_log=json.loads((a.metadata/'connector-job-log.json').read_text())['content']
    check('independently-fetched-connector-job-log-exact-UTF8-bytes',connector_log.encode()==raw_bytes)
    approved_bytes=a.approved_package_review.read_bytes();approved=json.loads(approved_bytes)
    check('prior-own-independent-full-package-review-hash',sha(approved_bytes)=='4fca0135b43a804f9f68c59d62e12f7f87e7533c841f05d205014d5dec0c1d73' and approved['passed'] and approved['reviewer']=='/root/inventory' and approved['commit']==CANDIDATE and approved['check_count']==2373)
    package_delta=sorted(q for q in inputs if approved['all_package_sha256'].get(q)!=inputs[q])
    check('only-three-approved-promotion-metadata-files-change-from-accepted-candidate',set(approved['all_package_sha256'])==set(inputs) and package_delta==['PACKAGE_LOCK.json','README.md','formalization.yaml'])
    promotion_bytes=a.promotion_review.read_bytes();promotion=json.loads(promotion_bytes)
    check('prior-own-exact2393-check-immutable-promotion-approval',sha(promotion_bytes)=='200e774d5784d6d8d9de89f3f72eaf7101ea8b07478a91a1da44e88adade90b5' and promotion['passed'] and promotion['check_count']==2393 and promotion['reviewer']=='/root/inventory' and promotion['commit']==PROMOTION)
    check('all857-CI-inputs-identical-to-own-approved-promoted-package',promotion['all_package_sha256']==inputs)
    candidate_receipt_bytes=(a.metadata/'prior-independent-approvals/CANDIDATE_LINUX_REVIEW.json').read_bytes();candidate_receipt=json.loads(candidate_receipt_bytes)
    check('prior-own-independent-real-candidate-Linux-approval',sha(candidate_receipt_bytes)=='9de7404a9b21c2e02ddd668cecfc7def09ded7da9c21e36f4b5a736147675344' and candidate_receipt['passed'] and candidate_receipt['check_count']==2934 and candidate_receipt['head']==CANDIDATE)
    runtime_markers={q.removesuffix('.lean').replace('/','.'):re.search(r'(?:Built|Replayed) '+re.escape(q.removesuffix('.lean').replace('/','.'))+r'\b',comparator) is not None for q in runtime}
    check('exact81-actual-Linux-runtime-build-markers',sum(runtime_markers.values())==81 and sorted(k for k,v in runtime_markers.items() if not v)==['EndpointAudit','Identity','Reviewed.TR26'])
    (OUT/'COMPILE_SCOPE.json').write_text(json.dumps(dict(scope='All84 input-bound; all77proofs+2live statements+Challenge+Solution show actual Linux build/replay markers. Three unused helpers were separately own local-compiled; generated kernel consumer runs separately.',runtime_inputs=84,actual_Linux_build_markers=81,markers=runtime_markers,comparator_log_sha256=sha(members[prefix+'comparator.log'])),indent=2)+'\n')

    source_map=json.loads(read(a.head,PROJECT+'/SOURCE_MAP.json'))
    check('all278-copy-mappings-plus80-runtime-source-scope',len(source_map['copies'])==278 and source_map['proof_source_ref']==SOURCE)
    for entry in source_map['copies']:
        body=read(entry['source_ref'],entry['source_path']);q=entry['path']
        check('all278-actual-source-map-copy-bindings:'+q,sha(body)==entry['sha256']==inputs[q] and len(body)==entry['bytes'] and body==read(merge,PROJECT+'/'+q))
    old_binding=json.loads(read(a.head,PROJECT+'/reviews/SOURCE_REVIEW_BINDINGS.json'))
    check('all221-historical-source-review-bindings-present',len(old_binding['files'])==221)
    for entry in old_binding['files']:
        q=entry['path'];check('all221-historical-review-hash-bindings:'+q,inputs[q]==entry['sha256'] and package_lock['files'][q]['bytes']==entry['bytes'])
    check('precise-truthful-omitted-Python-bytecode-record',review_binding['omitted_regenerable_artifacts'][0]['sha256']=='3e7b89cb7098ef4b5d1b0d3a35f4fc81dadc1c6e0677b8f546df2f5923677556' and review_binding['omitted_regenerable_artifacts'][0]['bytes']==35478)
    for entry in preproof['reviewed_inputs']:
        check('all24-originals-byte-equal-published-base:'+entry['path'],(read(merge,'tensor-computations/TR-26/ORIGINAL.md') if entry['path']=='tensor-computations/TR-26/README.md' else read(merge,entry['path']))==read(PUBLISHED,entry['path']))
    check('all217-permanent-IDs-retained',len(json.loads(read(merge,'problem_ids.json')))==217)
    check('separate-checker-controls-job-is-skipped-not-acceptance-evidence',any(x['name']=='checker-controls' and x['conclusion']=='skipped' for x in jobs['jobs']))
    check('exact15-original-artifact-members',len(members)==15)
    check('harness-does-not-claim-semantic-source-review',result['semantic_review']=='not-performed-by-this-command')
    for q, body in members.items():
        dest = OUT / 'artifact' / q
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(body)
    (OUT / 'reconstructed_ProofTrustAudit.lean.txt').write_text(consumer)
    return dict(run=a.run, job=job['id'], artifact=art['id'], source_head=a.head, source_base=base,
                actual_executed_synthetic_merge=merge, live_PR_head_at_retrieval=pr['head']['sha'],
                run_PR_nested_head_at_retrieval=prs[0]['head']['sha'],
                live_PR_merge_at_retrieval=pr['merge_commit_sha'],
                comparison_head=a.compare_head, independently_observed_receipt_sha256=sha(expected_bytes), promotion_approval_sha256=sha(promotion_bytes), actual_Linux_build_markers=81, archive_sha256=sha(archive), archive_bytes=len(archive),
                raw_log_sha256=sha(raw_bytes), raw_log_bytes=len(raw_bytes), result_sha256=sha(members[results[0]]),
                consumer_sha256=sha(consumer.encode()), harness_sha256=sha(harness), tool_receipt=tool,
                selected_theorems=NAMES, input_count=len(inputs), runtime_Lean_sources=len(runtime),
                reviewed_proof_copies=len(checkpoint['proof_inputs']), shared_runtime_copies=80,
                reviewed_full_source=SOURCE, superseded_incomplete_candidate=SUPERSEDED,
                unchanged_executable_and_pin_inputs=92, pins=pins,
                artifact_member_sha256={q: sha(body) for q, body in sorted(members.items())})

error = None
try:
    details = audit()
except Exception as exc:
    error = str(exc)
report = dict(reviewer='/root/inventory', authored_TR26_proof_sources=[], role='Independent non-author receipt reviewer', inspected_author_auditor_sha256='496b7f9093abbb2fa6583abd0e2ba386c792912335325dca405d29e5a3d2ebf6',
              scope='Independent offline audit of independently fetched actual GitHub Linux/Comparator original bytes; prior own full source and package reviews bound separately; no new local Linux execution.',
              passed=error is None and all(x['passed'] for x in checks), error=error,
              driver_sha256=sha(Path(__file__).read_bytes()), checks=checks, check_count=len(checks), **details,
              limits=['This is independent non-author receipt review using newly fetched originals and GitHub connector corroboration.',
                      'This receipt accepts the actual exact final240e promotion source; prior independent mathematical/package/promotion reviews remain separately bound. No later source head is inferred.',
                      'The executed commit is the checkout proved by the raw job log, not an inferred current merge SHA.',
                      'The run pull_requests nested head may reflect the later live PR head; immutable run head_sha/head_commit, job head_sha, raw checkout and Git parents bind the executed source.',
                      'No local build is described as actual Linux execution.'])
(OUT / 'INVENTORY_CI_RECEIPT.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: report[k] for k in ['passed', 'error', 'check_count']}, indent=2))
object_reader.stdin.close();object_reader.wait()
raise SystemExit(0 if report['passed'] else 1)
