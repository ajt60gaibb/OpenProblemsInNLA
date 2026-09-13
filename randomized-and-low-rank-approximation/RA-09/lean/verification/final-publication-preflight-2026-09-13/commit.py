from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, os, re, subprocess

R = Path('/tmp/nla-lean-ra09-worktree')
P = R / 'randomized-and-low-rank-approximation/RA-09/lean'
D = P / 'verification/publication-2026-09-13'
V = P / 'verification/publication-referee-2026-09-13'
F = P / 'verification/final-publication-preflight-2026-09-13'
report = P / 'reviews/publication-referee-2026-09-13.md'
candidate = '3bcc863070c037fffb1deee3f12d1cd1517727df'
report_sha = 'e2409b48afe317545bb3c3ae6a6ab7555bd8a98f8319d841fefb9b58912cf056'
ref_outer_sha = '2f639e0ec573dace9f30b546d0b40b1312398edf66e81ccdf1473984f1c63479'
h = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
git = lambda *args: subprocess.check_output(['git', *args], cwd=R)

assert not F.exists(), 'One-shot publication acceptance; inspect an existing receipt before resuming'
assert git('rev-parse', 'HEAD').decode().strip() == candidate
assert not git('diff', '--cached', '--name-only')
assert h(report) == report_sha
assert h(V / 'EVIDENCE-MANIFEST.json') == ref_outer_sha
assert h(V / 'FINAL.json') == '7f8d360ed10fc874401f0cc465d3ac56e898f63899bdcbb69a4397f3ba08b67f'
assert h(V / 'checks.json') == 'c243a9ef9e8ffab87794d2ff955be1548953bcab63bdbf69349a120c55412508'
assert h(D / 'INTEGRITY-CHECKS.json') == '9f92daec61e5de483c6494b248baf9b2d5dce82084e3664bbd2953e0abd45a91'
integrity = json.loads((D / 'INTEGRITY-CHECKS.json').read_text())
before = json.loads((D / 'before.json').read_text())
outputs = integrity['publication_files']
assert len(outputs) == 9
for rel, digest in outputs.items():
    assert h(R / rel) == digest, rel
archives = {'README.md': D / 'archive/README.linux-candidate.md',
            'formalization.yaml': D / 'archive/formalization.linux-candidate.yaml'}
assert len(before['all_prior_project_files']) == 1235
for rel, digest in before['all_prior_project_files'].items():
    assert h(archives.get(rel, P / rel)) == digest, rel
for rel, digest in before['immutable_operational_files'].items():
    assert h(P / rel) == digest, rel
assert h(R / 'problem_ids.json') == before['registry_sha256']
assert len(json.loads((R / 'problem_ids.json').read_text())) == 217
canonical = (P.parent / 'README.md').read_text()
assert '**Status:** Lean verified' in canonical
marker = 'Let $`n\\ge2`$'
assert hashlib.sha256(canonical[canonical.index(marker):].encode()).hexdigest() == before['canonical_target_sha256']

dirs = [P / 'verification/linux-2026-09-13',
        P / 'verification/root-operational-2026-09-13', D, V]
outer_expected = ['56dd2e10ca4d4f16367f85d06fde4630f66df2e4ac12dfbace9637e97b49de90',
                  'e80edf4c6d85bcfc58ab3534cd213c4e52b5416721361206682bf0f8223f66b9',
                  '6289e9cb47ccabb2691a34ea472c30ab621cba561ca20351decaa036e58653a1',
                  ref_outer_sha]
retained, inventories = {}, {}
for directory, expected in zip(dirs, outer_expected):
    outer = directory / 'EVIDENCE-MANIFEST.json'
    assert h(outer) == expected
    members = json.loads(outer.read_text())['files']
    internal = set()
    for rel, value in members.items():
        path = (directory / rel).resolve()
        assert path.is_relative_to(R.resolve()), str(path)
        digest = value if isinstance(value, str) else value['sha256']
        assert h(path) == digest, (directory.name, rel)
        if isinstance(value, dict) and 'bytes' in value:
            assert path.stat().st_size == value['bytes'], rel
        retained[str(path.relative_to(R.resolve()))] = digest
        if path.is_relative_to(directory.resolve()):
            internal.add(str(path.relative_to(directory.resolve())))
    assert internal == {str(p.relative_to(directory)) for p in directory.rglob('*')
                        if p.is_file() and p != outer}, directory
    retained[str(outer.relative_to(R))] = expected
    inventories[str(outer.relative_to(P))] = {'sha256': expected, 'bound_files': len(members)}
assert inventories[str((V / 'EVIDENCE-MANIFEST.json').relative_to(P))]['bound_files'] == 1528

expected_tracked = set(outputs)
assert set(git('diff', '--name-only').decode().splitlines()) == expected_tracked
stage = [*sorted(expected_tracked), *[str(p.relative_to(R)) for p in dirs + [report]]]
subprocess.run(['git', 'add', '--', *stage], cwd=R, check=True)
staged = git('diff', '--cached', '--name-only').decode().splitlines()
assert all(p in expected_tracked or any(p == s or p.startswith(s + '/') for s in stage)
           for p in staged)

# Historical raw output is retained verbatim. Exceptions require a reviewed path AND hash.
initial = subprocess.run(['git', 'diff', '--cached', '--check'], cwd=R,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
assert not initial.stderr
exceptions = {}
if initial.returncode:
    for line in initial.stdout.decode().splitlines():
        match = re.match(r'^(.+):\d+: (?:trailing whitespace\.|new blank line at EOF\.)$', line)
        if match:
            path = match.group(1)
            assert path in retained and h(R / path) == retained[path], path
            exceptions[path] = {'sha256': retained[path],
                                'reason': 'Exact sealed historical raw evidence; not normalized'}
        elif re.match(r'^.+:\d+: ', line):
            raise AssertionError(line)
    assert exceptions, initial.stdout.decode()
F.mkdir()
raw = F / 'git-diff-check-initial.log'
raw.write_bytes(initial.stdout)
if any(line.endswith((b' ', b'\t')) for line in initial.stdout.splitlines()) or initial.stdout.endswith(b'\n\n'):
    exceptions[str(raw.relative_to(R))] = {'sha256': h(raw),
                                         'reason': 'Exact raw output of the preceding staged check'}
command = ['git', 'diff', '--cached', '--check', '--', '.'] + [
    ':(exclude)' + p for p in sorted(exceptions)]
check = subprocess.run(command, cwd=R, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
assert check.returncode == 0, check.stdout.decode() + check.stderr.decode()

acceptance = {
    'utc': datetime.now(timezone.utc).isoformat(),
    'problem': 'RA-09',
    'status': 'Root accepts the concrete independent publication approval; commit, normal push and new upstream main PR authorized by user',
    'root_role': 'Publication preparer and mathematical contributor; this acceptance adds no independent mathematical approval',
    'reviewer': '/root/leancert_examples; independent of publication edits, RA09 proof coauthor, no additional mathematical approval',
    'report_sha256': report_sha, 'review_evidence_sha256': ref_outer_sha,
    'root_read_complete_publication_report_and_final_record': True,
    'root_actually_viewed_all_three_final_pages_in_preparation': True,
    'accepted_current_publication_files': outputs,
    'prior_project_files_preserved_through_exact_wrapper_archives': 1235,
    'original_candidate': candidate, 'actual_Linux_run': 34738884548,
    'immutable_operational_files_preserved': 711,
    'candidate_nonwrapper_inputs_preserved': 522,
    'all_217_IDs_and_original_target_preserved': True,
    'complete_sealed_inventories': inventories,
    'exact_hash_bound_whitespace_exceptions': exceptions,
    'successful_whitespace_command': command,
    'no_new_proof_or_Linux_execution_claimed': True,
}
(F / 'ROOT-ACCEPTANCE.json').write_text(json.dumps(acceptance, indent=2) + '\n')
(F / 'commit.py').write_bytes(Path(__file__).read_bytes())
outer = F / 'EVIDENCE-MANIFEST.json'
files = {str(p.relative_to(F)): {'sha256': h(p), 'bytes': p.stat().st_size}
         for p in sorted(F.rglob('*')) if p.is_file()}
outer.write_text(json.dumps({'scope': 'Every file in this directory; exact self exclusion only',
                             'files': files}, indent=2) + '\n')
subprocess.run(['git', 'add', '--', str(F.relative_to(R))], cwd=R, check=True)
subprocess.run(command, cwd=R, check=True)
for row in git('diff', '--cached', '--raw', '--no-abbrev').decode().splitlines():
    metadata, path = row.split('\t', 1)
    fields = metadata.split()
    assert fields[1] in ['100644', '100755']
    assert hashlib.sha256(git('cat-file', 'blob', fields[3])).hexdigest() == h(R / path), path
env = dict(os.environ, GIT_AUTHOR_NAME='George Stepaniants', GIT_COMMITTER_NAME='George Stepaniants',
           GIT_AUTHOR_EMAIL='', GIT_COMMITTER_EMAIL='')
result = subprocess.run(['git', '-c', 'user.name=George Stepaniants', '-c', 'user.email=',
                         '-c', 'commit.gpgsign=false', 'commit', '-m',
                         'Publish Linux-verified RA-09 formalization and reviewed evidence'],
                        cwd=R, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
assert result.returncode == 0, result.stdout.decode() + result.stderr.decode()
assert git('show', '-s', '--format=%ae%x00%ce', 'HEAD').rstrip(b'\n') == b'\0'
assert not git('status', '--porcelain')
receipt = {'problem': 'RA-09', 'commit': git('rev-parse', 'HEAD').decode().strip(),
           'candidate': candidate, 'blank_author_and_committer_emails': True,
           'worktree_clean': True, 'root_publication_acceptance_sha256': h(F / 'ROOT-ACCEPTANCE.json'),
           'root_preflight_manifest_sha256': h(outer), 'exact_whitespace_exceptions': len(exceptions)}
Path('/tmp/nla-lean-formalization/RA-09-final-publication-commit.json').write_text(
    json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
