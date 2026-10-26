#!/usr/bin/env python3
"""Read-only immutable IE22 metadata promotion review; does not rerun CI."""
import argparse
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
p.add_argument('--commit', default='6202e6668a889a0286120533f160ca61de4d0cf4')
a = p.parse_args()
ROOT, OUT, COMMIT = a.repo.resolve(), a.output.resolve(), a.commit
OUT.mkdir(parents=True, exist_ok=True)
HEAD = '06f31cdd4f76d90c7590b5582b8db4975a0055d8'
SOURCE = '353ebcfcbbcfc08184c32f391ecb6068c7d9098f'
ORIGINAL = '5487945e5a72abd952b0c89915915de8cc9b3e65'
PUBLISHED = '01ed3c64648d2d8350ba80c4018894b6d785d2c9'
PACKAGE = 'linear-systems-and-elimination/IE-22/lean/'
PROBLEM = 'linear-systems-and-elimination/IE-22/'
DOC = 'docs/lean/proofs/IE-22/campaign-2026-10-23/'
NAMES = ['NLA.Proofs.IE22.' + n for n in ['uniform_squared_upper', 'near_sharp_unit_row_witness', 'target']]
sha = lambda b: hashlib.sha256(b).hexdigest()
git = lambda *x: subprocess.check_output(['git', *x], cwd=ROOT)
read = lambda c, q: git('show', c + ':' + q)
obj = lambda q: json.loads(read(COMMIT, q))
paths = lambda c, q: git('ls-tree', '-r', '--name-only', c, q).decode().splitlines()
checks = []
def check(name, passed, **details):
    checks.append(dict(name=name, passed=bool(passed), **details))

proofs = [q for q in paths(COMMIT, PACKAGE) if q.endswith('.lean')]
check('all27canonicalLean-input-set-preserved', len(proofs) == 27 and proofs == [q for q in paths(HEAD, PACKAGE) if q.endswith('.lean')])
for q in proofs:
    check('all27Lean-byte-identical-to-actual-Linux-head:' + q, read(COMMIT, q) == read(HEAD, q))
checkpoint = json.loads(read(SOURCE, DOC + 'FULL_SOURCE_CHECKPOINT.json'))
for x in checkpoint['files']:
    check('all23reviewed-shared-canonical-copies:' + x['path'],
          read(COMMIT, x['path']) == read(SOURCE, x['path']) == read(COMMIT, PACKAGE + x['path'].removeprefix('lean-statements/')) and
          sha(read(COMMIT, x['path'])) == x['sha256'])
pre = obj(DOC + 'preproof/INPUT_LOCK.json')
for x in pre['reviewed_inputs']:
    old = read(ORIGINAL, x['path'])
    check('all32original-inputs-frozen:' + x['path'],
          old == read(COMMIT, DOC + 'preproof/frozen/' + x['path']) and sha(old) == x['sha256'] and len(old) == x['bytes'])
    if x['path'].startswith(PACKAGE) and old != read(COMMIT, x['path']):
        check('every-replaced-original-scaffold-archived:' + x['path'],
              old == read(COMMIT, PACKAGE + 'original-scaffold/' + x['path'].removeprefix(PACKAGE) + '.txt'))
for q in [PROBLEM + 'ORIGINAL.md', 'docs/lean/statements/IE-22/ORIGINAL.md']:
    check('whole-original-canonical-page-retained:' + q, read(COMMIT, q) == read(ORIGINAL, PROBLEM + 'README.md'))
old = read(HEAD, PROBLEM + 'README.md').decode()
new = read(COMMIT, PROBLEM + 'README.md').decode()
check('exact-original-mathematical-target-tail-preserved', old.split('## Problem statement\n', 1)[1] == new.split('## Problem statement\n', 1)[1])
old_pre = old.split('## Lean formalization scaffold\n', 1)[0]
new_pre = new.split('## Lean proof and verification evidence\n', 1)[0]
normalize = lambda s: re.sub(r'\*\*Last checked:\*\* [^\n]+', '**Last checked:** <date>', re.sub(r'\*\*Status:\*\* [^\n]+', '**Status:** <status>', s))
check('only-authorized-status-date-before-progress-section', normalize(old_pre) == normalize(new_pre))
registry = obj('problem_ids.json')
check('registry217IDs-paths-byte-identical', len(registry) == 217 and read(COMMIT, 'problem_ids.json') == read(HEAD, 'problem_ids.json') == read(PUBLISHED, 'problem_ids.json') == read(ORIGINAL, 'problem_ids.json'))
statuses = {}
status_delta = []
for identity, q in registry.items():
    status = re.search(r'\*\*Status:\*\* ([^\n]+)', read(COMMIT, q).decode()).group(1).strip()
    prev = re.search(r'\*\*Status:\*\* ([^\n]+)', read(HEAD, q).decode()).group(1).strip()
    statuses[identity] = status
    if status != prev:
        status_delta.append([identity, prev, status])
check('onlyIE22status-promotion', status_delta == [['IE-22', 'Solved', 'Lean verified']])
counts = dict(Counter(statuses.values()))
check('actualcanonical-status-counts85verified33Solved', counts.get('Lean verified') == 85 and counts.get('Solved') == 33)
for q in ['README.md', 'CATALOG.md']:
    check('generated-catalog-correct-counts:' + q, '**Resolution evidence:** 33 solved (published or independently audited); 85 solved with Lean verification.' in read(COMMIT, q).decode())
package_files = paths(COMMIT, PACKAGE)
before_files = paths(HEAD, PACKAGE)
new_reviews = {
    'reviews/full-source-inventory.md': 'full-source-review-inventory/SOURCE_REVIEW_INVENTORY.md',
    'reviews/full-source-verification.md': 'full-source-and-kernel-review-verification/REVIEW.md',
    'reviews/package-inventory.md': 'package-review-inventory/PACKAGE_REVIEW_INVENTORY.md',
    'reviews/preproof-inventory.md': 'preproof/PRE_REVIEW_INVENTORY.md',
    'reviews/preproof-verification.md': 'preproof/PRE_REVIEW_VERIFICATION.md',
}
check('59package-inputs-exactly-five-review-additions', len(package_files) == 59 and set(package_files) - set(before_files) == {PACKAGE + q for q in new_reviews} and not set(before_files) - set(package_files))
for dest, src in new_reviews.items():
    check('verbatim-review-copy:' + dest, read(COMMIT, PACKAGE + dest) == read(COMMIT, DOC + src))
changed = {q.removeprefix(PACKAGE) for q in git('diff', '--name-only', HEAD, COMMIT, '--', PACKAGE).decode().splitlines()}
check('canonical-delta-only-four-descriptions-and-five-reviews', changed == set(new_reviews) | {'formalization.yaml', 'README.md', 'BLOCKERS.md', 'STATEMENT_REVIEW.md'})
promotion = obj(DOC + 'PROMOTION_INPUT_LOCK.json')
expected = {q.removeprefix(PACKAGE): sha(read(COMMIT, q)) for q in package_files}
check('promotion-lock-exact59-input-set-digests-sizes', {x['path']: x['sha256'] for x in promotion['package_inputs']} == expected and all(x['bytes'] == len(read(COMMIT, PACKAGE + x['path'])) for x in promotion['package_inputs']))
check('promotion-lock-honest-initial-execution-and-pending-newCI', promotion['initial_accepted_head'] == HEAD and promotion['initial_actual_merge'] == '88b9366e6cfcef7e60a2d740ff8a7101399bf1a8' and promotion['proof_statement_source_commit'] == SOURCE and promotion['source_count'] == 27 and promotion['initial_package_input_count'] == 54 and 'Fresh committed promotion CI still to run' in promotion['scope'])
check('promotion-validation-base-current-published-main', promotion['published_base_for_ID_validation'] == PUBLISHED)
linux = obj(DOC + 'linux-pr368-initial/INVENTORY_REVIEW.json')
check('exact-independent220receipt-and-nonauthor-scope', linux['passed'] and linux['check_count'] == 220 and linux['reviewer'] == '/root/inventory' and linux['authored_IE22_proof_sources'] == [] and linux['source_pr_head'] == HEAD and linux['actual_selected_exports'] == NAMES and linux['replaceable_definitions'] == [])
# Bind every retained initial receipt file to the actual independently reviewed
# original bundle, not to a newly composed metadata-level success statement.
initial = Path(__file__).resolve().parents[2] / 'ie22-linux-ci'
receipt_copies = []
for q in paths(COMMIT, DOC + 'linux-pr368-initial/'):
    rel = q.removeprefix(DOC + 'linux-pr368-initial/')
    local = initial / rel
    check('byte-exact-independent-Linux-bundle-copy:' + rel, local.is_file() and local.read_bytes() == read(COMMIT, q))
    receipt_copies.append(dict(path=q, sha256=sha(read(COMMIT, q))))
cfg = obj(PACKAGE + 'comparator.json')
meta = obj(PACKAGE + 'formalization.yaml')
check('acceptance-boundary-and-pins-not-mutated', all(read(COMMIT, PACKAGE + q) == read(HEAD, PACKAGE + q) for q in ['comparator.json', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain']))
check('whole-target-promotion-metadata-exact3results-standard3', meta['status']['phase'] == 'complete' and meta['status']['whole_problem_verified'] is True and meta['status']['canonical_status'] == 'Lean verified' and [x['declaration'] for x in meta['status']['main_results']] == NAMES == cfg['theorem_names'] and cfg['definition_names'] == [] and set(meta['status']['axioms']) == {'propext', 'Classical.choice', 'Quot.sound'})
for x in meta['status']['main_results']:
    check('all-results-honest-initial-CI-identity:' + x['declaration'], all(t in x['verification_status'] for t in ['40255260833', '121355717650', '88b9366e6cfcef7e60a2d740ff8a7101399bf1a8', 'all54', 'All27', 'receives fresh']) and x['sorry_count'] == 0 and set(x['axioms']) == {'propext', 'Classical.choice', 'Quot.sound'})
check('metadata-AI-credit-qualitative-source-limit-explicit', 'Matthew J. Colbrook' in json.dumps(meta) and 'not external human peer review' in json.dumps(meta) and 'quantitative convergence rate is not claimed' in json.dumps(meta))
inventory = obj('docs/lean/statements/inventory.json')
entry = next(x for x in inventory['entries'] if x['id'] == 'IE-22')
check('inventory-IE22-not-stale-axiom-gap', not any('full target is an axiom' in s.lower() for s in entry['exactness_concerns']) and entry['completeness'] != 'known-scope-gap', actual_concerns=entry['exactness_concerns'], actual_completeness=entry['completeness'])
author_script = read(COMMIT, DOC + 'audit_package.py').decode()
# The old startswith comparison includes the two intentionally changed fields.
check('author-preservation-auditor-supports-intended-promotion', 'current_text.startswith(before)' not in author_script or old_pre == new_pre)
if 'def reviewed_readme_preserved' in author_script:
    fn = next(n for n in ast.parse(author_script).body if isinstance(n, ast.FunctionDef) and n.name == 'reviewed_readme_preserved')
    ns = {}
    exec(compile(ast.Module(body=[fn], type_ignores=[]), '<frozen-pure-README-guard>', 'exec'), ns)
    cases = [('original', old, True), ('exact-authorized-promotion', new, True),
             ('changed-credit', new.replace('Matthew J. Colbrook', 'Changed credit', 1), False),
             ('changed-target', new.replace('## Problem statement\n', '## Problem statement\nChanged target\n', 1), False),
             ('wrong-status', new.replace('**Status:** Lean verified', '**Status:** Open', 1), False),
             ('wrong-date', new.replace('**Last checked:** 2026-10-26', '**Last checked:** 2026-10-27', 1), False),
             ('altered-historical-suffix', new + '\nChanged historical suffix\n', False)]
    for label, candidate, expected_result in cases:
        check('independent-actual-README-guard-control:' + label, ns['reviewed_readme_preserved'](old, candidate) == expected_result)
    author = obj(DOC + 'PACKAGE_AUTHOR_AUDIT.json')
    check('corrected-author-report-driver-binding', author['pass'] and author['checks_total'] == 271 and author['checks_failed'] == 0 and author['script_sha256'] == sha(author_script.encode()))
    check('old-author-driver-receipt-retained-with-explicit-prepromotion-scope',
          read(COMMIT, DOC + 'author-prepromotion-audit/audit_package.py') == read('6202e6668a889a0286120533f160ca61de4d0cf4', DOC + 'audit_package.py') and
          read(COMMIT, DOC + 'author-prepromotion-audit/PACKAGE_AUTHOR_AUDIT.json') == read('6202e6668a889a0286120533f160ca61de4d0cf4', DOC + 'PACKAGE_AUTHOR_AUDIT.json') and
          b'pre-promotion package checked at06f31cdd4f76d90c7590b5582b8db4975a0055d8' in read(COMMIT, DOC + 'author-prepromotion-audit/SCOPE.md'))
if COMMIT == '53ddb09ee25f863f483a05f91b3f02ff1ad7b0d6':
    final_head = '799077c8d8b10bd9e266185a9ecc0c4c06abccd3'
    check('post-finalCI-canonical59inputs-unchanged', all(read(COMMIT, q) == read(final_head, q) for q in package_files))
    check('exact53two-file-coverage-only-delta', git('diff', '--name-only', final_head, COMMIT).decode().splitlines() == ['docs/lean/statements/COVERAGE.md', 'tools/statement_inventory.py'])
    generator = read(COMMIT, 'tools/statement_inventory.py').decode()
    scope_gaps = ast.literal_eval(next(n.value for n in ast.parse(generator).body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'SCOPE_GAPS' for t in n.targets)))
    check('derived-correct-five-current-scope-gaps', len(scope_gaps) == 5 and 'IE-22' not in scope_gaps and '{len(SCOPE_GAPS)} existing scope gaps' in generator and 'The 5 existing scope gaps remain explicit' in read(COMMIT, 'docs/lean/statements/COVERAGE.md').decode())
    final_receipt_path = Path(__file__).resolve().parents[2] / 'ie22-linux-ci-final/INVENTORY_REVIEW.json'
    final_receipt_bytes = final_receipt_path.read_bytes()
    final_receipt = json.loads(final_receipt_bytes)
    check('actual-final-promotion-Linux-receipt-approved313', sha(final_receipt_bytes) == '81825a0cf1cea1e65317ed55d89a2dc2f78a740234ee2b6e5b1307a37c65b84e' and final_receipt['passed'] and final_receipt['check_count'] == 313 and final_receipt['source_pr_head'] == final_head and final_receipt['actual_executed_synthetic_merge'] == '12bf4d153f725cbc326d40d694c1993d6f098eb4')
report = dict(date='2026-10-26', reviewer='/root/inventory', commit=COMMIT, initial_Linux_head=HEAD, reviewed_source=SOURCE, published_validation_base=PUBLISHED,
    scope='Independent read-only source-copy, original/ID, catalog/status and exact-evidence promotion audit; no proof edits or new local Linux run.',
    passed=all(x['passed'] for x in checks), check_count=len(checks), checks=checks, findings=[x for x in checks if not x['passed']],
    all59_package_inputs=expected, original_Linux_bundle_copies=receipt_copies, canonical_status_counts=counts, canonical_status_delta=status_delta,
    promotion_lock_sha256=sha(read(COMMIT, DOC + 'PROMOTION_INPUT_LOCK.json')), auditor_sha256=sha(Path(__file__).read_bytes()),
    verdict='APPROVE' if all(x['passed'] for x in checks) else 'REQUEST METADATA CORRECTIONS; complete proof/source/Linux evidence remains approved')
(OUT / 'PROMOTION_REVIEW.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: report[k] for k in ['commit', 'passed', 'check_count', 'findings', 'canonical_status_counts', 'verdict']}, indent=2))
raise SystemExit(0 if report['passed'] else 1)
