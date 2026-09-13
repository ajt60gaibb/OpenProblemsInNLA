"""Seal the IS03 author statement boundary once; never silently overwrite a freeze."""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess

P = Path(__file__).resolve().parents[1]
W = P.parents[2]
R = P / 'reviews'
freeze = R / 'statement-freeze.json'
assert not freeze.exists(), 'A frozen boundary already exists; retain it and request a new review explicitly.'
assert not (P / 'Solution.lean').exists() and not (P / 'NLA/IS03/Proof.lean').exists()


def sha(f):
    return hashlib.sha256(Path(f).read_bytes()).hexdigest()


inputs = json.loads((P / 'source-inputs.json').read_text())
for path, record in inputs['sources'].items():
    assert sha(W / path) == record['sha256']
    raw = subprocess.check_output(['git', 'show', inputs['base'] + ':' + path], cwd=W)
    assert hashlib.sha256(raw).hexdigest() == record['sha256']
assert not subprocess.check_output(['git', 'diff', '--name-only'], cwd=W)
exclude = {'reviews/statement-freeze.json', 'reviews/statement-handoff.md'}
files = {}
for path in sorted(P.rglob('*')):
    if path.is_file():
        relative = path.relative_to(P).as_posix()
        assert '.lake' not in path.relative_to(P).parts
        assert path.suffix not in {'.olean', '.ilean', '.trace'}
        if relative not in exclude:
            files[relative] = sha(path)
result = {
    'phase': 'statement-only-before-two-independent-approvals',
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'base': inputs['base'],
    'branch': subprocess.check_output(['git', 'branch', '--show-current'], cwd=W).decode().strip(),
    'canonical_status': 'Solved, unchanged',
    'statement_authors': ['/root', '/root/solved_statement_inventory'],
    'independent_reviewers_assigned': ['/root/leancert_examples', '/root/formal_review_standards'],
    'independent_approvals_present_at_freeze': False,
    'file_count': len(files), 'files': files,
    'source_file_count': len(inputs['sources']),
    'source_files': {path: record['sha256'] for path, record in inputs['sources'].items()},
    'source_git_blobs': {path: record['git_blob'] for path, record in inputs['sources'].items()},
    'boundary': ['NLA/IS03/Definitions.lean', 'Challenge.lean', 'NUMERICAL_TARGETS.md'],
    'requirements': ('No proof before two independent approvals of these bytes. Seven intentional '
                     'Challenge holes are not proofs and must stay outside the future Solution '
                     'environment. Preserve all exact quantifiers, definitions, numerical targets '
                     'and pins. Kernel-only LeanCert and standard-three axioms for the eventual '
                     'complete exports; actual Linux verification remains pending.')}
freeze.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'freeze': str(freeze), 'sha256': sha(freeze),
                  'project_files': len(files), 'source_files': len(inputs['sources']),
                  'boundary': {name: files[name] for name in result['boundary']}}, indent=2))
