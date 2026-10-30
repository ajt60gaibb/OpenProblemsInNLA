#!/usr/bin/env python3
"""Offline author audit of retained, genuine GitHub Linux full-target RE06 CI evidence.

This driver reads original API metadata, the separately retrieved raw job log,
the original artifact ZIP, and immutable Git objects. It never executes Lean,
Comparator, the harness, a sandbox, or network requests. An independent reviewer
must separately audit this author-collected receipt.
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

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo', type=Path, required=True)
p.add_argument('--evidence', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
p.add_argument('--head', required=True)
p.add_argument('--run', type=int, required=True)
p.add_argument('--compare-head', default='')
a = p.parse_args()
ROOT, EVIDENCE, OUT = a.repo.resolve(), a.evidence.resolve(), a.output.resolve()
OUT.mkdir(parents=True, exist_ok=True)
PROJECT = 'randomized-and-low-rank-approximation/RE-06/lean'
DOC = 'docs/lean/proofs/RE-06/campaign-2026-10-26/'
PUBLISHED = '099805ef1ce7347d373e47cccc3b2d7cf580a99e'
NAMES = ['NLA.Proofs.RE06.' + n for n in ['svd_total', 'query_bound', 'successful', 'original_claim', 'explicit_claim', 'target']]
SOURCE = '181c365dc426875aaa61984c901478b1b7c696e6'
SUPERSEDED = 'dd72168242c8fb2148bb22089acec9c109e4e376'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
checks, details = [], {}
sha = lambda b: hashlib.sha256(b).hexdigest()
git = lambda *v: subprocess.check_output(['git', *v], cwd=ROOT)
read = lambda c, q: git('show', c + ':' + q)
load = lambda n: json.loads((EVIDENCE / n).read_text())

def check(name, passed, **extra):
    checks.append(dict(name=name, passed=bool(passed), **extra))
    if not passed:
        raise AssertionError(name)

def audit():
    run, jobs, listing, pr = (load(n) for n in ['run.json', 'jobs.json', 'artifacts.json', 'pr.json'])
    check('actual-PR371-workflow-terminal-success', run['id'] == a.run and
          run['event'] == 'pull_request' and run['status'] == 'completed' and
          run['conclusion'] == 'success' and run['head_sha'] == a.head and run['run_attempt'] == 1)
    prs = [x for x in run['pull_requests'] if x['number'] == 371]
    check('actual-run-head-commit-and-PR-identity', len(prs) == 1 and run['head_commit']['id'] == a.head)
    base = prs[0]['base']['sha']
    project_jobs = [j for j in jobs['jobs'] if j['name'] == 'verify (RE-06, ' + PROJECT + ')']
    check('exact-one-actual-RE06-project-job', len(project_jobs) == 1)
    job = project_jobs[0]
    check('actual-project-job-success', job['run_id'] == a.run and job['head_sha'] == a.head and
          job['status'] == 'completed' and job['conclusion'] == 'success')
    check('actual-required-project-steps-succeeded', all(
          any(s['name'] == n and s['conclusion'] == 'success' for s in job['steps']) for n in
          ['Validate formalization manifest', 'Fresh sandboxed statement, axiom and kernel verification',
           'Retain verification logs']))
    artifacts = [x for x in listing['artifacts'] if x['name'] == 'lean-RE-06']
    check('exact-original-RE06-artifact-listing', len(artifacts) == 1)
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
    merges = re.findall(r'fetch[^\n]*\+([0-9a-f]{40}):refs/remotes/pull/371/merge', raw)
    check('one-actually-executed-PR-merge-checkout', len(merges) == 1)
    merge = merges[0]
    checkout_summaries = re.findall(r'HEAD is now at ([0-9a-f]+) Merge ([0-9a-f]{40}) into ([0-9a-f]{40})', raw)
    check('actual-checkout-command-and-git-log',
          'git checkout --progress --force refs/remotes/pull/371/merge' in raw and
          len(checkout_summaries) == 1 and merge.startswith(checkout_summaries[0][0]) and
          checkout_summaries[0][1:] == (a.head, base) and
          re.search(r'git log -1 --format=%H\n[^\n]* ' + merge + r'\n', raw) is not None)
    check('executed-merge-object-parents', git('show', '-s', '--format=%P', merge).decode().split() == [base, a.head])
    check('actual-upload-artifact-digest-ID-size', all(t in raw for t in [
          'SHA256 digest of uploaded artifact zip is ' + sha(archive),
          f'Artifact lean-RE-06.zip successfully finalized. Artifact ID {art["id"]}',
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
    check('six-exact-full-target-exports-no-replaceable-definitions', cfg == dict(challenge_module='Challenge',
          solution_module='Solution', theorem_names=NAMES, definition_names=[],
          permitted_axioms=['propext', 'Classical.choice', 'Quot.sound']))
    inputs = result['input_sha256']
    paths = git('ls-tree', '-r', '--name-only', a.head, PROJECT).decode().splitlines()
    check('exact295-canonical-input-positive-set', len(paths) == len(inputs) == 295 and
          set(inputs) == {q.removeprefix(PROJECT + '/') for q in paths})
    check('head-and-executed-merge-package-file-sets-identical', paths ==
          git('ls-tree', '-r', '--name-only', merge, PROJECT).decode().splitlines())
    package_lock = json.loads(read(a.head, PROJECT + '/PACKAGE_LOCK.json'))
    check('exact294-package-lock-entries', len(package_lock['files']) == 294 and
          set(package_lock['files']) == set(inputs) - {'PACKAGE_LOCK.json'} and
          package_lock['proof_source_ref'] == SOURCE)
    check('exact-promoted-v2-package-lock', inputs['PACKAGE_LOCK.json'] ==
          'e712ded5fbc472ab9fa999de9a1fa885aa86b0b88276f2a55afbc01a7a7a921a')
    for q, digest in inputs.items():
        b = read(a.head, PROJECT + '/' + q)
        check('exact-head-merge-input:' + q, sha(b) == digest and b == read(merge, PROJECT + '/' + q))
        if q in package_lock['files']:
            e = package_lock['files'][q]
            check('exact-reviewed-package-lock:' + q, e['sha256'] == digest and e['bytes'] == len(b))
        check('no-regenerable-artifact:' + q, not q.endswith(('.olean', '.ilean', '.pyc', '.pyo')) and
              '__pycache__' not in q.split('/'))
        if a.compare_head:
            check('same-package-at-comparison-head:' + q, b == read(a.compare_head, PROJECT + '/' + q))
    source_map = json.loads(read(a.head, PROJECT + '/SOURCE_MAP.json'))
    runtime = source_map['runtime_lean_order']
    actual_runtime = [q for q in inputs if q.endswith('.lean') and not q.startswith('reviews/')]
    check('exact91-live-runtime-source-positive-set', len(runtime) == 91 and
          len(set(runtime)) == 91 and set(runtime) == set(actual_runtime))
    for q in runtime:
        check('v2-runtime-bytes-identical-to-v1:' + q,
              read(a.head, PROJECT + '/' + q) == read(SUPERSEDED, PROJECT + '/' + q))
    check('exact278-positive-upstream-copies', len(source_map['copies']) == 278 and
          len({e['path'] for e in source_map['copies']}) == 278 and
          source_map['proof_source_ref'] == SOURCE)
    for e in source_map['copies']:
        b = read(e['source_ref'], e['source_path'])
        check('upstream-copy-binding:' + e['path'], sha(b) == e['sha256'] == inputs[e['path']] and
              len(b) == e['bytes'] and b == read(a.head, PROJECT + '/' + e['path']))
    checkpoint = json.loads(read(SOURCE, DOC + 'FULL_TARGET_SOURCE_FREEZE.json'))
    check('exact-frozen-full-source-epoch', sha(read(SOURCE, DOC + 'FULL_TARGET_SOURCE_FREEZE.json')) ==
          source_map['full_source_freeze_sha256'] ==
          '93df2eabffe17df3c1d9a2950a60bc0cfcea103e8b4285cbd117b7f945d21e8b')
    check('exact82-proof-plus5-shared-inputs', len(checkpoint['proof_inputs']) == 82 and
          len(checkpoint['shared_inputs']) == 5)
    for e in checkpoint['proof_inputs'] + checkpoint['shared_inputs']:
        q = e['path'].removeprefix('lean-statements/')
        b = read(SOURCE, e['path'])
        check('full-reviewed-actual-source-copy:' + q, sha(b) == e['sha256'] == inputs[q] and
              len(b) == e['bytes'] and b == read(a.head, e['path']) == read(merge, e['path']) ==
              read(merge, PROJECT + '/' + q))
    derivation = json.loads(read(a.head, PROJECT + '/CHALLENGE_DERIVATION.json'))
    original = read(a.head, PROJECT + '/reviews/preproof/Challenge.lean')
    challenge = read(a.head, PROJECT + '/Challenge.lean')
    removed = derivation['removed_lines']
    original_lines = original.decode().splitlines(keepends=True)
    check('diagnostic-only-canonical-Challenge-derivation', len(removed) == 12 and
          all(sum(line.strip() == x for line in original_lines) == 1 for x in removed) and
          ''.join(line for line in original_lines if line.strip() not in removed).encode() == challenge and
          sha(original) == derivation['original']['sha256'] ==
          '21f59e23c4c4b0168eb031de49b0fe8c31c72179713f1479c895a8020bc7d1a8' and
          sha(challenge) == derivation['canonical_reference_sha256'] and
          derivation['declaration_headers_changed'] is False and derivation['reference_placeholders'] == 6)
    control = read(a.head, PROJECT + '/' + derivation['negative_control']).decode()
    check('moved-controls-preserve-original-namespace',
          control.startswith('import Challenge\n') and 'namespace NLA.Proofs.RE06' in control and
          control.rstrip().endswith('end NLA.Proofs.RE06') and
          all(sum(line.strip() == x for line in control.splitlines()) == 1 for x in removed))
    endpoint = read(merge, PROJECT + '/EndpointAudit.lean').decode()
    check('all-six-genuine-theorem-kind-and-kernel-guards-retained', all(
          '#re06_theorem ' + n in endpoint and '#assert_trust kernel ' + n in endpoint for n in NAMES))
    identity = read(merge, PROJECT + '/Identity.lean').decode()
    check('literal-frozen-Target-rfl-identity-retained',
          'NLA.Statements.RE06.Target =' in identity and 'NLA.ReviewedStatements.RE06.Target := rfl' in identity)
    formal = json.loads(read(merge, PROJECT + '/formalization.yaml'))
    check('promoted-status-matches-accepted-complete-proof', formal['status']['whole_problem_verified'] is True and
          formal['status']['canonical_status'] == 'Lean verified' and formal['status']['phase'] == 'full-target-verified' and
          [x['declaration'] for x in formal['status']['main_results']] == NAMES)
    preproof = json.loads(read(a.head, PROJECT + '/reviews/preproof/INPUT_LOCK.json'))
    check('permanent-ID-registry-preserved', read(merge, 'problem_ids.json') == read(PUBLISHED, 'problem_ids.json') and
          len(json.loads(read(merge, 'problem_ids.json'))) == 217)
    candidate = '0c6d346763a932eb2d379f555e66d8ab3dbf3255'
    canonical = 'randomized-and-low-rank-approximation/RE-06/README.md'
    for e in preproof['files']:
        b = read(merge, 'docs/lean/proofs/RE-06/ORIGINAL.md' if e['path'] == canonical else e['path'])
        check('preproof-original-preserved-live-or-exact-archive:' + e['path'], sha(b) == e['sha256'] and
              len(b) == e['bytes'])
    old_page, new_page = read(candidate, canonical), read(merge, canonical)
    marker = b'## Context and notation'
    check('entire-original-Context-through-EOF-suffix-preserved',
          old_page[old_page.index(marker):] == new_page[new_page.index(marker):] and
          read(merge, 'docs/lean/proofs/RE-06/ORIGINAL.md') == old_page and
          b'**Status:** Lean verified' in new_page and
          b'## Lean proof and verification evidence' in new_page)
    old_readme = read(candidate, PROJECT + '/README.md')
    check('preceding-candidate-package-README-preserved-verbatim',
          read(merge, 'docs/lean/proofs/RE-06/CANDIDATE_README.md') == old_readme)
    candidate_paths = git('ls-tree', '-r', '--name-only', candidate, PROJECT).decode().splitlines()
    check('exact-candidate-and-promoted-canonical-input-positive-sets', candidate_paths == paths)
    differences = []
    for q in inputs:
        unchanged = read(candidate, PROJECT + '/' + q) == read(a.head, PROJECT + '/' + q)
        if not unchanged:
            differences.append(q)
        if q not in {'formalization.yaml', 'README.md', 'PACKAGE_LOCK.json'}:
            check('every-executable-pin-original-and-control-unchanged:' + q, unchanged)
    check('only-three-independently-reviewed-descriptive-inputs-changed',
          set(differences) == {'formalization.yaml', 'README.md', 'PACKAGE_LOCK.json'})
    check('metadata-honestly-promises-separate-final-receipt', all(
          'will receive a separate source-bound final Linux receipt' in e['verification_status']
          for e in formal['status']['main_results']))
    check('published-harness-and-workflows-unchanged',
          git('diff', '--name-only', PUBLISHED, merge, '--', 'tools/lean', '.github/workflows') == b'')
    lock_data = read(merge, 'tools/lean/source-lock.json')
    lock, tool = json.loads(lock_data), result['tool_receipt']
    check('exact-locked-Forsythe-checker-source', sha(lock_data) == result['source_lock_sha256'] == tool['source_lock_sha256'] and
          lock['commit'] == tool['forsythe_commit'] == '8d1b0c0545a77b40245e84705aa7d273e6c81e62' and tool['profile'] == 'default')
    check('actual-official-Linux-Lean-platform', tool['lean_toolchain'] == 'leanprover/lean4:v4.33.1' and
          tool['lean_version'] == 'Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)' and
          tool['lean_version'] in raw and tool['platform'].startswith('Linux-') and
          tool['go_version'] == 'go version go1.27.1 linux/amd64')
    harness = read(merge, 'tools/lean/harness.py')
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
    check('actual-Comparator-compared-six-exact-full-target-exports', len(exports) == 2 and
          exports[0].endswith('from Challenge') and exports[1].endswith('from Solution') and
          all(re.findall(r'NLA\.Proofs\.RE06\.[A-Za-z_]+', line) == NAMES for line in exports))
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
    compiled = re.findall(r'(?:Built|Replayed) ([A-Za-z_][A-Za-z0-9_.]*)', comparator)
    project_modules = sorted(set(n for n in compiled if n in {'Challenge', 'Solution'} or n.startswith(('NLA.', 'Reviewed.'))))
    check('actual-Linux-module-list-has-full-solution-and-main', 'Solution' in project_modules and
          'Challenge' in project_modules and 'NLA.Proofs.RE06.MainTarget' in project_modules)
    proof_modules = [n for n in project_modules if n.startswith('NLA.Proofs.')]
    check('all81-production-proof-modules-built-by-Linux', len(proof_modules) == 81 and
          'NLA.Proofs.RE06.FullTargetAudit' not in proof_modules)
    details['actual_Linux_import_build_modules'] = project_modules
    details['actual_Linux_import_build_module_count'] = len(project_modules)
    details['actual_Linux_proof_module_count'] = len(proof_modules)

    for q, body in members.items():
        dest = OUT / 'artifact' / q
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(body)
    (OUT / 'reconstructed_ProofTrustAudit.lean.txt').write_text(consumer)
    return dict(run=a.run, job=job['id'], artifact=art['id'], source_head=a.head, source_base=base,
                actual_executed_synthetic_merge=merge, live_PR_head_at_retrieval=pr['head']['sha'],
                run_PR_nested_head_at_retrieval=prs[0]['head']['sha'],
                live_PR_merge_at_retrieval=pr['merge_commit_sha'],
                comparison_head=a.compare_head, archive_sha256=sha(archive), archive_bytes=len(archive),
                raw_log_sha256=sha(raw_bytes), raw_log_bytes=len(raw_bytes), result_sha256=sha(members[results[0]]),
                consumer_sha256=sha(consumer.encode()), harness_sha256=sha(harness), tool_receipt=tool,
                selected_theorems=NAMES, input_count=len(inputs), runtime_Lean_sources=len(runtime),
                reviewed_proof_copies=len(checkpoint['proof_inputs']), shared_runtime_copies=87,
                reviewed_full_source=SOURCE, superseded_control_defect_candidate=SUPERSEDED, accepted_candidate_ref=candidate, descriptive_changes=differences,
                unchanged_live_runtime_Lean_inputs=91, pins=pins,
                artifact_member_sha256={q: sha(body) for q, body in sorted(members.items())})

error = None
try:
    details.update(audit())
except Exception as exc:
    error = str(exc)
report = dict(author='/root', role='Proof author; CI receipt collector',
              scope='Mechanically audit retained actual Linux/Comparator bytes only; no independent source-review claim.',
              passed=error is None and all(x['passed'] for x in checks), error=error,
              driver_sha256=sha(Path(__file__).read_bytes()), checks=checks, check_count=len(checks), **details,
              limits=['This is an author-collected receipt pending independent audit.',
                      'This receipt verifies the independently reviewed descriptive promoted package against the accepted candidate; it does not replace independent package/source review or itself seal the evidence archive.',
                      'The executed commit is the checkout proved by the raw job log, not an inferred current merge SHA.',
                      'The run pull_requests nested head may reflect the later live PR head; immutable run head_sha/head_commit, job head_sha, raw checkout and Git parents bind the executed source.',
                      'No local build is described as actual Linux execution.'])
(OUT / 'AUTHOR_CI_RECEIPT.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: report[k] for k in ['passed', 'error', 'check_count']}, indent=2))
raise SystemExit(0 if report['passed'] else 1)
