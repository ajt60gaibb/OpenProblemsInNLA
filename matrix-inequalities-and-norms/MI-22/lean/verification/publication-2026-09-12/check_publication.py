"""Check MI-22 publication metadata against immutable verified inputs and evidence.

Read-only with respect to proof, original Linux artifacts and canonical files.
Only this publication-evidence directory receives check receipts.
"""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess

OUT = Path(__file__).resolve().parent
PROJECT = OUT.parents[1]
REPO = PROJECT.parents[2]
LINUX = PROJECT / 'verification/linux-2026-09-12'
CANDIDATE = '26f526cf8b6232af9528b30616076dc7a2c66ac6'
BASE = 'f41f1f9ffa2171550d4bb795862c6170c4f26070'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args):
    return subprocess.run(['git', *args], cwd=REPO, capture_output=True, check=True).stdout


checks = []
commands = [
    ('permanent-ids', ['python3', 'tools/validate_problem_ids.py', '--base-ref', 'origin/main']),
    ('id-tests', ['python3', '-m', 'unittest', 'discover', '-s', 'tests', '-p', 'test_problem_ids.py', '-v']),
    ('manifest', ['/tmp/nla-lean-formalization/venv/bin/python', 'tools/lean/validate_manifest.py',
                  'matrix-inequalities-and-norms/MI-22/lean']),
    ('final-format', ['python3', 'tools/format_math.py', '--check', 'MI-22']),
    ('scoped-diff-check', ['git', 'diff', '--check', 'HEAD', '--',
                         ':!**/verification/linux-2026-09-12/**']),
    ('linux-evidence-offline', ['python3', str(LINUX / 'verify_evidence.py')])
]
for name, args in commands:
    result = subprocess.run(args, cwd=REPO, capture_output=True)
    log = OUT / (name + '.log')
    log.write_bytes(result.stdout + result.stderr)
    checks.append({'command': args, 'exit_code': result.returncode, 'log': log.name,
                   'log_sha256': digest(log)})
    print(name, result.returncode, flush=True)
    result.check_returncode()
(OUT / 'final-checks.json').write_text(json.dumps(checks, indent=2) + '\n')

receipt = json.loads((LINUX / 'artifacts/lean-MI-22/verify-20260912T214303Z-4163/result.json').read_text())
assert receipt['repository_commit'] == CANDIDATE and receipt['result'] == 'comparator-accepted'
inputs = receipt['input_sha256']
assert len(inputs) == 177
changed_inputs = {}
for name, old_hash in inputs.items():
    path = PROJECT / name
    assert path.is_file(), name
    committed = git('show', CANDIDATE + ':' + str(path.relative_to(REPO)))
    assert hashlib.sha256(committed).hexdigest() == old_hash, name
    assert digest(LINUX / 'source' / path.relative_to(REPO)) == old_hash, name
    if digest(path) != old_hash:
        changed_inputs[name] = {'verified_sha256': old_hash, 'current_sha256': digest(path)}
assert set(changed_inputs) == {'README.md', 'formalization.yaml'}, changed_inputs
for name, archive in [('README.md', 'README.linux-candidate.md'),
                      ('formalization.yaml', 'formalization.linux-candidate.yaml')]:
    assert digest(OUT / archive) == inputs[name]

freeze = json.loads((PROJECT / 'verification/proof-freeze.json').read_text())
assert len(freeze['files']) == 104
assert all(digest(PROJECT / name) == info['sha256'] for name, info in freeze['files'].items()
           if name != 'README.md')
canonical_changes = set()
for name, expected in freeze['source_files'].items():
    assert digest(LINUX / 'source' / name) == expected
    if digest(REPO / name) != expected:
        canonical_changes.add(name)
expected_canonical = {'matrix-inequalities-and-norms/MI-22/' + name
                      for name in ['README.md', 'problem.tex', 'problem.pdf']}
assert canonical_changes == expected_canonical
old_readme = git('show', freeze['source_commit'] + ':matrix-inequalities-and-norms/MI-22/README.md')
current_readme = (REPO / 'matrix-inequalities-and-norms/MI-22/README.md').read_bytes()
assert old_readme.split(b'## Problem statement', 1)[1] == current_readme.split(b'## Problem statement', 1)[1]
assert b'**Status:** Lean verified' in current_readme

outer = LINUX / 'EVIDENCE-MANIFEST.json'
assert digest(outer) == '1247b0cb6deb563d8f32e05f0831432554e68b3536eef5f6b1abae6278a3c18a'
assert digest(LINUX / 'OPERATIONAL-REVIEW.md') == '792d6d49b4a4c8fae6fb489c93c55269c18b7b58adfa640ab2568a0b0c8f9e9e'
evidence = json.loads(outer.read_text())
actual_paths = {str(p.relative_to(LINUX)) for p in LINUX.rglob('*') if p.is_file() and p != outer}
assert actual_paths == set(evidence['files']) and len(actual_paths) == 303
assert all(digest(LINUX / name) == h['sha256'] and (LINUX / name).stat().st_size == h['bytes']
           for name, h in evidence['files'].items())

for name in ['problem_ids.json', 'AGENTS.md', 'CONTRIBUTING.md']:
    assert (REPO / name).read_bytes() == git('show', BASE + ':' + name)
assert not git('diff', BASE, '--', 'tools/', '.github/')
identity = git('show', '-s', '--format=%an%x00%ae%x00%cn%x00%ce', 'HEAD').rstrip(b'\n').split(b'\0')
assert identity == [b'George Stepaniants', b'', b'George Stepaniants', b'']
tracked = git('diff', '--name-only', 'HEAD').decode().splitlines()
allowed = {'CATALOG.md', 'README.md', 'RESOLVED.md', 'matrix-inequalities-and-norms/README.md',
           *expected_canonical,
           'matrix-inequalities-and-norms/MI-22/lean/README.md',
           'matrix-inequalities-and-norms/MI-22/lean/formalization.yaml'}
assert set(tracked) <= allowed, tracked
record = {
    'verdict': 'PASS', 'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'verified_candidate': CANDIDATE, 'integrated_upstream': BASE,
    'integration_head': git('rev-parse', 'HEAD').decode().strip(),
    'verified_project_input_count': 177, 'unchanged_nonwrapper_inputs': 175,
    'permitted_wrapper_changes': changed_inputs,
    'proof_freeze_nonREADME_inputs_unchanged': 103,
    'original_source_snapshots_unchanged': 8,
    'original_informal_proof_inputs_unchanged': 5,
    'current_canonical_publication_outputs_changed': sorted(canonical_changes),
    'entire_original_problem_statement_and_references_byte_identical': True,
    'Linux_evidence_bound_files_unchanged': 303, 'Linux_evidence_total_files_unchanged': 304,
    'Linux_evidence_outer_sha256': digest(outer),
    'author_and_committer_names': 'George Stepaniants', 'both_email_fields': '',
    'registry_and_shared_harness_unchanged': True,
    'tracked_publication_diff': tracked,
    'current_publication_outputs': {n: {'bytes': (REPO / n).stat().st_size,
                                        'sha256': digest(REPO / n)} for n in tracked},
    'no_publication_commit_or_push': True
}
(OUT / 'integrity.json').write_text(json.dumps(record, indent=2) + '\n')
print('Integrity PASS: 175 nonwrapper inputs, 103 frozen proof inputs, 304 Linux evidence files unchanged', flush=True)
