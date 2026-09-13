"""Read-only publication audit by a disclosed RA09 proof coauthor.

Independent implementation of the preservation/metadata checks. The complete
candidate-manifest membership rule is adapted from the retained source_audit.py;
the actual inputs, Git blobs, public wrappers and evidence are checked afresh.
No Lean command, network request or Git mutation is performed.
"""
from pathlib import Path
from collections import Counter
import datetime, hashlib, json, os, re, subprocess, traceback, zipfile
import yaml

R = Path('/tmp/nla-lean-ra09-worktree').resolve()
REL = 'randomized-and-low-rank-approximation/RA-09/lean'
P = R / REL
E = P / 'verification/publication-referee-2026-09-13'
O = P / 'verification/publication-2026-09-13'
LINUX = P / 'verification/linux-2026-09-13'
CANDIDATE = '3bcc863070c037fffb1deee3f12d1cd1517727df'
BASE = '5830ed4fb06da0659414a3deb2a40ad327aca052'
consulted = {}
sha = lambda b: hashlib.sha256(b).hexdigest()


def read(p):
    p = Path(p).resolve()
    b = p.read_bytes()
    consulted[os.path.relpath(p, E)] = {'sha256': sha(b), 'bytes': len(b)}
    return b


def js(p):
    return json.loads(read(p))


def git(*args):
    return subprocess.check_output(['git', *args], cwd=R)


def identity(p, h):
    b = read(p)
    expected = h if isinstance(h, str) else h['sha256']
    assert sha(b) == expected, str(p)
    if isinstance(h, dict) and 'bytes' in h:
        assert len(b) == h['bytes'], str(p)
    return b


def manifest(p):
    m = js(p)
    bound = set(m['files'])
    actual = {str(f.relative_to(p.parent)) for f in p.parent.rglob('*')
              if f.is_file() and f != p}
    assert bound == actual, (str(p), actual - bound, bound - actual)
    for rel, h in m['files'].items():
        identity(p.parent / rel, h)
    if 'file_count' in m:
        assert m['file_count'] == len(bound)
    return {'sha256': sha(read(p)), 'bound_files': len(bound)}


def changed_fields(a, b, path=''):
    if isinstance(a, dict) and isinstance(b, dict):
        assert a.keys() == b.keys(), path
        return sum((changed_fields(a[k], b[k], (path + '.' if path else '') + k)
                    for k in a), [])
    return [] if a == b else [path]


result = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'role': 'Independent publication review; RA09 proof coauthor, no extra mathematical approval',
          'candidate': CANDIDATE, 'run': 34738884548, 'status': 'RUNNING'}
try:
    assert git('rev-parse', 'HEAD').decode().strip() == CANDIDATE
    outer = O / 'EVIDENCE-MANIFEST.json'
    identity(outer, '6289e9cb47ccabb2691a34ea472c30ab621cba561ca20351decaa036e58653a1')
    identity(O / 'INTEGRITY-CHECKS.json', '9f92daec61e5de483c6494b248baf9b2d5dce82084e3664bbd2953e0abd45a91')
    result['publication_manifest'] = manifest(outer)
    before = js(O / 'before.json')
    assert before['candidate'] == CANDIDATE and before['base'] == BASE
    archives = {'README.md': O / 'archive/README.linux-candidate.md',
                'formalization.yaml': O / 'archive/formalization.linux-candidate.yaml'}
    for rel, h in before['all_prior_project_files'].items():
        identity(archives.get(rel, P / rel), h)
    assert len(before['all_prior_project_files']) == 1235
    for rel, h in before['immutable_operational_files'].items():
        identity(P / rel, h)
    assert len(before['immutable_operational_files']) == 711
    tree = git('ls-tree', '-r', '-z', CANDIDATE, '--', REL)
    (E / 'candidate-tree.txt').write_bytes(tree.replace(b'\0', b'\n'))
    candidates = {}
    for entry in tree.split(b'\0'):
        if not entry:
            continue
        header, path = entry.split(b'\t')
        mode, kind, blob = header.decode().split()
        assert kind == 'blob' and mode in ('100644', '100755')
        rel = str(Path(path.decode()).relative_to(REL))
        raw = git('cat-file', 'blob', blob)
        assert sha(raw) == before['candidate_inputs'][rel]
        assert raw == identity(archives.get(rel, P / rel), sha(raw))
        assert raw == read(LINUX / 'source' / REL / rel)
        candidates[rel] = {'sha256': sha(raw), 'bytes': len(raw), 'git_blob': blob}
    assert candidates.keys() == before['candidate_inputs'].keys() and len(candidates) == 524
    changed = [n for n in candidates if sha(read(P / n)) != candidates[n]['sha256']]
    assert set(changed) == set(archives)
    result['preservation'] = {'prior_project_files': 1235, 'candidate_inputs': 524,
                              'unchanged_candidate_inputs': 522,
                              'changed_wrappers_exactly': sorted(changed),
                              'operational_files_unchanged': 711}
    nested = {}
    for n in candidates:
        if Path(n).name != 'EVIDENCE-MANIFEST.json':
            continue
        mpath = LINUX / 'source' / REL / n
        m = js(mpath)
        internal = set()
        for rel, h in m['files'].items():
            target = (mpath.parent / rel).resolve()
            relative = str(target.relative_to(LINUX / 'source' / REL))
            identity(target, h)
            assert candidates[relative]['sha256'] == sha(read(target))
            if not rel.startswith('../'):
                internal.add(rel)
        prefix = str(Path(n).parent) + '/'
        assert internal == {s[len(prefix):] for s in candidates if s.startswith(prefix) and s != n}
        nested[n] = {'sha256': sha(read(mpath)), 'bound_files': len(m['files'])}
    assert len(nested) == 13
    result['all_nested_candidate_manifests'] = nested
    for freeze, count in [('reviews/statement-freeze.json', 31), ('verification/proof-freeze.json', 361)]:
        d = js(P / freeze)
        assert len(d['files']) == count and len(d['source_files']) == 17
        for n, h in d['files'].items():
            identity(P / ('verification/pre-candidate-README.md' if n == 'README.md' else n), h)
        for n, h in d['source_files'].items():
            raw = git('show', BASE + ':' + n)
            assert sha(raw) == h and raw == read(LINUX / 'source' / n)
            assert git('rev-parse', BASE + ':' + n).decode().strip() == d['source_git_blobs'][n]
    result['statement_proof_original_counts'] = [31, 361, 17]
    result['linux_manifest'] = manifest(LINUX / 'EVIDENCE-MANIFEST.json')
    result['root_operational_manifest'] = manifest(P / 'verification/root-operational-2026-09-13/EVIDENCE-MANIFEST.json')
    current = yaml.safe_load(read(P / 'formalization.yaml'))
    prior = yaml.safe_load(read(archives['formalization.yaml']))
    fields = changed_fields(prior, current)
    expected = {'status.scope', 'review.status', 'review.notes',
                'review.linux_verification.status', 'review.linux_verification.note',
                'review.candidate_documents.installation'}
    assert set(fields) == expected
    result['exact_six_YAML_fields'] = fields
    config = js(P / 'comparator.json')
    names = config['theorem_names']
    assert len(names) == 17 and config['definition_names'] == []
    assert config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
    assert [r['declaration'] for r in current['status']['main_results']] == names
    assert [r['declaration'] for r in current['alignment']] == names
    for r in current['status']['main_results']:
        assert r['file'] == 'Solution.lean' and r['sorry_count'] == 0 and r['axioms'] == config['permitted_axioms']
    for r in current['review']['proof_reports'] + current['review']['statement_reports']:
        identity(P / r['file'], r['sha256'])
    gate = js(P / 'verification/final-review-acceptance.json')
    assert [r['reviewer'] for r in gate['reports']] == ['/root/ra09_final_referee1', '/root/mf16_final_referee']
    assert [r['actual_standard_three_reports'] for r in gate['reports']] == [66, 50]
    for r in gate['reports']:
        identity(P / r['report'], r['sha256'])
        identity(P / r['evidence']['path'], r['evidence']['sha256'])
    canonical = read(P.parent / 'README.md').decode()
    old_canonical = git('show', CANDIDATE + ':' + str((P.parent / 'README.md').relative_to(R))).decode()
    suffix = canonical[canonical.index('## Problem statement'):]
    assert suffix == old_canonical[old_canonical.index('## Problem statement'):]
    assert '**Status:** Lean verified' in canonical
    for n in names:
        assert '`' + n.removeprefix('NLA.RA09.') + '`' in canonical
    for s in ['Lean 4.33.1', CANDIDATE, '0df444a360eaa60ab8c11dca51a86af692955474',
              '621a43d7cf21f87872392a01e874f2f1dbddc926', 'tools/lean/bootstrap.sh',
              'tools/lean/selftest.sh', 'tools/lean/verify.sh']:
        assert s in canonical
    registry = js(R / 'problem_ids.json')
    assert len(registry) == 217 and read(R / 'problem_ids.json') == git('show', BASE + ':problem_ids.json')
    counts = Counter()
    for id_, path in registry.items():
        raw = read(R / path)
        counts[re.search(rb'\*\*Status:\*\* ([^\n]+)', raw).group(1).decode().strip()] += 1
        if id_ != 'RA-09':
            assert raw == git('show', CANDIDATE + ':' + path), id_
    assert counts == {'Open': 53, 'Partially resolved': 72, 'Solved': 75, 'Lean verified': 17}, counts
    result['current_catalog_counts'] = dict(counts)
    pub = js(O / 'INTEGRITY-CHECKS.json')['publication_files']
    assert set(git('diff', '--name-only', 'HEAD').decode().splitlines()) == set(pub)
    for n, h in pub.items():
        identity(R / n, h)
    resolved = read(R / 'RESOLVED.md').decode()
    old_resolved = git('show', CANDIDATE + ':RESOLVED.md').decode()
    pattern = r'\*\*RA-09 \([^\n]+\n'
    assert re.sub(pattern, 'RA09_PUBLICATION_BLOCK\n', resolved) == re.sub(pattern, 'RA09_PUBLICATION_BLOCK\n', old_resolved)
    block = re.search(pattern, resolved).group(0)
    for text in [canonical, read(P / 'README.md').decode(), read(P / 'formalization.yaml').decode(), block]:
        assert 'George Stepaniants' in text and 'Department of Computing and Mathematical Sciences' in text
        assert 'California Institute of Technology' in text and 'Matthew J. Colbrook' in text
        assert not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}', text)
    result['public_inputs'] = pub
    runtime = js(LINUX / 'runtime-verification.json')
    root = js(P / 'verification/root-operational-2026-09-13/ROOT-CHECKS.json')
    assert runtime['candidate'] == root['candidate'] == CANDIDATE
    assert runtime['run'] == root['run'] == 34738884548
    assert runtime['actual_exports'] == root['theorems'] == names
    assert runtime['actual_standard_three_axiom_reports'] == root['actual_standard_three_reports'] == 49
    assert runtime['whole_workflow_all_steps_successful'] and runtime['whole_workflow_jobs'] == 17
    project = LINUX / 'artifacts/lean-RA-09/verify-20260913T045251Z-4175'
    receipt = js(project / 'result.json')
    assert receipt['repository_commit'] == CANDIDATE and receipt['input_sha256'] == before['candidate_inputs']
    log = read(project / 'comparator.log').decode()
    assert 'Lean default kernel accepts the solution' in log and 'Your solution is okay!' in log
    assert log.rstrip().endswith('EXIT_STATUS=0') and '--skip-kernel' not in log
    ax = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log)
    assert len(ax) == 49 and all({a.strip() for a in r.split(',')} == set(config['permitted_axioms']) for r in ax)
    assert 'warning:' not in log.split('Building Solution', 1)[1]
    exports = re.findall(r'Exporting #\[(.*?)\] from (Challenge|Solution)', log)
    assert len(exports) == 2
    for terms, module in exports:
        assert [t.strip() for t in terms.split(',') if t.strip().startswith('NLA.RA09.')] == names
    for folder in [project, LINUX / 'artifacts/lean-checker-controls/selftest-20260913T045300Z-4116']:
        kernel = read(folder / 'kernel-controls.log').decode()
        assert 'RETURN honest_with_inductives_and_quotients: accepted' in kernel
        assert 'RETURN invalid_raw_proof: rejected:' in kernel and 'Quotient constant mismatch on: Quot.lift' in kernel
        for n, needle in [('negative-sorry.log', "Illegal axiom detected: 'sorryAx'"),
                          ('negative-native.log', "Illegal axiom detected: 'checked._native.native_decide.ax_1_1'")]:
            s = read(folder / n).decode()
            assert needle in s and s.rstrip().endswith('EXIT_STATUS=1') and 'from Solution' in s
        controls = read(folder / 'comparator-controls.log').decode()
        assert controls.rstrip().endswith('EXIT_STATUS=0')
        sandbox = read(folder / 'sandbox.log').decode()
        assert 'uid_map' in sandbox and '1001' in sandbox and sandbox.rstrip().endswith('EXIT_STATUS=0')
    for archive in runtime['artifact_identity_checks']:
        raw = read(LINUX / (archive['name'] + '.zip'))
        assert sha(raw) == archive['zip_sha256'] and len(raw) == archive['zip_bytes']
        with zipfile.ZipFile(LINUX / (archive['name'] + '.zip')) as z:
            members = {i.filename for i in z.infolist() if not i.is_dir()}
            assert members == set(archive['complete_extracted_files'])
            for n in members:
                assert z.read(n) == identity(LINUX / 'artifacts' / archive['name'] / n, archive['complete_extracted_files'][n])
    full = js(LINUX / 'whole-run-verification.json')
    identity(LINUX / 'run-logs.zip', full['archive_sha256'])
    with zipfile.ZipFile(LINUX / 'run-logs.zip') as z:
        assert len([i for i in z.infolist() if not i.is_dir()]) == full['archive_file_count'] == 217
    result['actual_evidence_claims_crosschecked'] = {'exports': 17, 'standard_three_reports': 49,
        'kernel': 'accepted', 'both_actual_control_suites': True, 'source_receipt_inputs': 524,
        'archive_members': [13, 10], 'whole_run_archive_entries': 217,
        'role': 'read retained actual records; no new execution or new mathematical review'}
    for policy in ['CONTRIBUTING.md', 'AGENTS.md', 'docs/lean/README.md', 'docs/lean/REVIEW.md',
                   'docs/lean/schema/v0.4.schema.json', 'tools/lean/validate_manifest.py',
                   'tools/lean/HARNESS.md', 'tools/lean/bootstrap.sh', 'tools/lean/selftest.sh', 'tools/lean/verify.sh']:
        read(R / policy)
    (E / 'tracked.diff').write_bytes(git('diff', '--no-ext-diff', 'HEAD'))
    cmds = [
        ['python3', 'tools/validate_problem_ids.py', '--base-ref', 'origin/main'],
        ['python3', 'tools/validate_problem_ids.py', '--base-ref', 'nla-upstream/main'],
        ['/tmp/nla-lean-formalization/venv/bin/python', 'tools/lean/validate_manifest.py', REL],
        ['python3', '-m', 'unittest', 'discover', '-s', 'tests', '-p', 'test_problem_ids.py', '-v'],
        ['python3', 'tools/format_math.py', '--check'], ['git', 'diff', '--check', 'HEAD'],
    ]
    env = os.environ.copy(); env['PYTHONDONTWRITEBYTECODE'] = '1'
    result['fresh_read_only_checks'] = []
    for i, cmd in enumerate(cmds):
        c = subprocess.run(cmd, cwd=R, env=env, capture_output=True)
        raw = c.stdout + c.stderr
        name = f'check-{i+1}.log'; (E / name).write_bytes(raw)
        result['fresh_read_only_checks'].append({'command': cmd, 'exit_code': c.returncode,
                                                'log': name, 'sha256': sha(raw)})
        assert c.returncode == 0, (cmd, raw.decode())
    for n, h in pub.items():
        identity(R / n, h)
    result['no_changed_review_inputs_after_checks'] = True
    result['status'] = 'PASS independent publication checks; report and visual verdict separately sealed'
except BaseException:
    result['status'] = 'FAIL retained reviewer diagnostic'
    result['traceback'] = traceback.format_exc()
finally:
    (E / 'consulted-inputs.json').write_text(json.dumps(consulted, indent=2) + '\n')
    (E / 'checks.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k in ['status', 'traceback', 'preservation',
                  'statement_proof_original_counts', 'current_catalog_counts', 'exact_six_YAML_fields']}, indent=2))
raise SystemExit(0 if result['status'].startswith('PASS') else 1)
