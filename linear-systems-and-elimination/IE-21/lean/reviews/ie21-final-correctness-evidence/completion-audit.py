#!/usr/bin/env python3
"""Independent retained-evidence binding audit; never invokes Lean or a VM.

The live-file equality checks describe the completion-review freeze, before the
separately reviewed publication documentation/metadata delta.
"""
from pathlib import Path, PurePosixPath
import hashlib
import json
import re
import subprocess
import tarfile

review = Path(__file__).resolve().parent
project = review.parent.parent
repo = project.parents[2]
evidence = project / 'verification/linux'
publication = '1eb284b84ecc0d3c958d022b3e020be7fa111391'
guest = 'bd72d630841a1660b9f7652d469186c11728925f'
prefix = 'linear-systems-and-elimination/IE-21/lean'
sha = lambda data: hashlib.sha256(data).hexdigest()
digest = lambda path: sha(path.read_bytes())
read = lambda path: json.loads(path.read_text())
git = lambda *args: subprocess.check_output(['git', *args], cwd=repo)

inputs = read(evidence / 'input-receipt.json')
expected = inputs['input_sha256']
assert len(expected) == 289
paths = git('ls-tree', '-r', '--name-only', publication, '--', prefix).decode().splitlines()
blobs = {p[len(prefix)+1:]: sha(git('show', publication + ':' + p)) for p in paths}
assert blobs == expected
for p, h in expected.items():
    assert digest(project / p) == digest(evidence / 'source' / p) == h, p
    assert '.lake' not in PurePosixPath(p).parts
    assert PurePosixPath(p).suffix not in {'.olean', '.ilean', '.o', '.so', '.a'}
prep = read(evidence / 'preparation.json')
result = read(evidence / 'successful-verification/result.json')
dep = read(evidence / 'dependency-evidence/dependency-receipt.json')
auth = read(evidence / 'input-authentication.json')
assert expected == prep['input_sha256'] == result['input_sha256']
assert expected == dep['snapshot_input_sha256'] == auth['source_sha256']
assert inputs['publication_commit'] == prep['publication_commit'] == auth['publication_commit'] == publication
assert result['repository_commit'] == prep['guest_repository_commit'] == guest != publication
assert digest(evidence / 'input-receipt.json') == prep['receipt_sha256'] == auth['receipt_sha256']

archive = evidence / 'input.tar'
assert digest(archive) == inputs['archive_sha256'] == '6b61efee12a30cde167f1e2ac22b1b0662be0324475e37b222e3cd8ee466c6dd'
assert archive.stat().st_size == inputs['archive_bytes'] == 1228800
with tarfile.open(archive) as t:
    rows = {}
    for m in t.getmembers():
        path = PurePosixPath(m.name)
        assert not path.is_absolute() and '..' not in path.parts
        assert m.isdir() or m.isfile()
        if m.isfile():
            p = str(path.relative_to(prefix))
            assert p not in rows
            rows[p] = sha(t.extractfile(m).read())
    assert rows == expected
export = read(evidence / 'evidence-export-receipt.json')
archive = evidence / 'verification-evidence.tar.gz'
assert digest(archive) == export['sha256'] == 'ba04ba6bc5973591c25b3fe6729c683d85966d3dac375bbd2083c8e58d1d5853'
assert archive.stat().st_size == export['bytes'] == 346734
archive_count = 0
with tarfile.open(archive) as t:
    seen = set()
    for m in t.getmembers():
        p = PurePosixPath(m.name)
        assert not p.is_absolute() and '..' not in p.parts
        assert m.isdir() or m.isfile()
        if m.isfile():
            assert m.name not in seen
            seen.add(m.name)
            assert t.extractfile(m).read() == (evidence / p).read_bytes(), m.name
            archive_count += 1
manifest = read(evidence / 'EVIDENCE-MANIFEST.json')
assert digest(evidence / 'EVIDENCE-MANIFEST.json') == 'e684400fe12bb40fe5b685bdb9ff64241fe8435e30b1ebaf6e0362dec13528ab'
assert len(manifest['files']) == 350
for p, h in manifest['files'].items():
    assert digest(evidence / p) == h, p

freeze = read(project / 'reviews/package-source-freeze.json')
own = read(review / 'final-source-review-receipt.json')
assert digest(project / 'reviews/package-source-freeze.json') == own['package_freeze_sha256'] == 'b4ab97645ec9f8c46c7130aabc4bac48cbab48af0c96d4f454ad58c32a981744'
assert freeze['source_sha256'] == own['source_package_sha256']
assert len(freeze['source_sha256']) == 41
for p, h in freeze['source_sha256'].items():
    assert expected[p] == h, p
assert digest(review / 'final-source-review-receipt.json') == '2fdb5369b3ca6525b3118958eaca320c4484544213b3878621422db2de752c33'
for p, h in own['review_evidence_sha256'].items():
    assert digest(review / p) == h, p
statement = read(project / 'reviews/statement-freeze.json')
for p, h in {**statement['mathematical_boundary_sha256'], **statement['approvals']}.items():
    assert expected[p] == h, p
for key in ['canonical_readme', 'retained_manuscript']:
    original = own['read_coverage'][key]
    assert digest(repo / original['path']) == original['sha256']
    assert sha(git('show', publication + ':' + original['path'])) == original['sha256']

boot = read(evidence / 'bootstrap.json')
lock = read(evidence / 'checker-source/source-lock.json')
assert boot == result['tool_receipt']
assert digest(evidence / 'checker-source/source-lock.json') == boot['source_lock_sha256'] == result['source_lock_sha256']
assert lock['commit'] == boot['forsythe_commit'] == '8d1b0c0545a77b40245e84705aa7d273e6c81e62'
assert lock['lean_toolchain'] == boot['lean_toolchain'] == 'leanprover/lean4:v4.33.1'
for p in (evidence / 'checker-source').iterdir():
    assert p.read_bytes() == git('show', publication + ':tools/lean/' + p.name), p.name
assert digest(evidence / 'checker-runtime-source/env.sh') == boot['env_sha256']
assert digest(evidence / 'checker-runtime-source/sandbox_probe_ci.py') == boot['ci_sandbox_probe_sha256']
adapter = next(f for f in lock['files'] if f['destination'] == 'scripts/strict_landrun.py')
assert digest(evidence / 'checker-runtime-source/strict_landrun.py') == adapter['sha256']
preflight = read(evidence / 'prerequisite-inspection.json')
assert preflight['validated_tools'] == 'PASS' and preflight['tool_receipt'] == boot
for p, h in preflight['driver_sha256'].items():
    assert digest(evidence / 'checker-source' / p) == h
repair = read(evidence / 'environment-repair.json')
assert digest(repo / repair['policy_source']) == repair['policy_sha256']
assert [s['exit_code'] for s in repair['steps']] == [0, 0, 0]
assert repair['steps'][-1]['output'].strip().endswith('= 0')

pins = read(project / 'lake-manifest.json')['packages']
assert len(pins) == len(dep['packages']) == 10
for p in pins:
    d = next(d for d in dep['packages'] if d['name'] == p['name'])
    assert p['rev'] == d['manifest_revision'] == d['actual_git_head']
    assert p['url'] == d['url']
assert digest(evidence / 'dependency-evidence/LeanCert-Verification.lean') == dep['LeanCert_Verification_sha256'] == '2c576708b528acdde17796b0b715b83079f9cad377182dbd87c248323ff0a58c'
assert dep['LeanCert_Verification_bytes_match_pinned_git_blob'] is True

names = read(project / 'comparator.json')['theorem_names']
assert len(names) == len(set(names)) == 23
assert names == inputs['theorem_names'] == prep['theorem_names'] == result['config']['theorem_names']
solution = (project / 'Solution.lean').read_text()
assert re.findall(r'^#assert_trust kernel (\S+)$', solution, re.M) == names
assert re.findall(r'^#print axioms (\S+)$', solution, re.M) == names
log = (evidence / 'successful-verification/comparator.log').read_text()
exports = re.findall(r'^Exporting #\[(.*?)\] from (Challenge|Solution)$', log, re.M)
assert [x[1] for x in exports] == ['Challenge', 'Solution']
for declarations, module in exports:
    assert [x for x in declarations.split(', ') if x.startswith('NLA.IE21.')] == names
closures = re.findall(r"^info: Solution\.lean:\d+:\d+: '([^']+)' depends on axioms: \[([^]]+)\]$", log, re.M)
assert [name for name, _ in closures] == names
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert set(result['config']['permitted_axioms']) == allowed
assert all(set(ax.split(', ')) == allowed for _, ax in closures)
modules = {p.stem for p in (project / 'NLA/IE21').glob('*.lean')}
assert len(modules) == 31
assert set(re.findall(r'Built NLA\.IE21\.(\w+) \(', log)) == modules
assert len(re.findall(r'^warning: Challenge\.lean:', log, re.M)) == 23
assert not re.search(r'^warning: (?!Challenge\.lean:)|^error:', log, re.M)
assert log.index('from Challenge') < log.index('Building Solution')
assert 'Built LeanCert.Tactic.Verification' in log
assert 'Lean default kernel accepts the solution\nYour solution is okay!' in log
assert log.rstrip().endswith('EXIT_STATUS=0')
runner = read(evidence / 'runner-result-attempt-1.json')
assert runner['status'] == 'finished' and runner['exit_code'] == 0
assert runner['verification_log_directories'] == ['/home/admin/nla-lean-tools/logs/verify-20260922T205303Z-973']
assert result['result'] == 'comparator-accepted'

print('PASS independent Git blob / live / source / archive / four-receipt equality: 289 inputs')
print('PASS evidence archive member equality:', archive_count, 'ordinary files; manifest: 350 hashes')
print('PASS original source review unchanged, all41 approved files, all4 preproof boundaries and approvals')
print('PASS unchanged shared checker sources, pinned runtime receipts and authentic LeanCert source binding')
print('PASS all10 manifest URLs and exact observed dependency Git heads')
print('PASS all31 project modules built; all23 authentic assertions, exact axioms and separate exports')
print('PASS actual Comparator kernel acceptance; detailed controls also inspected individually by reviewer')
print('SCOPE: retained evidence audit only; no new Lean, Comparator, dependency build or VM execution')
