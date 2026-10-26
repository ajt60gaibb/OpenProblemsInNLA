#!/usr/bin/env python3
"""Check exact TR06 pre-promotion originals, boundary and source identities.

This is a source-preservation audit; it does not execute Lean or accept a proof.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

REPO = Path(__file__).resolve().parents[5]
PROJECT = 'tensor-computations/TR-06/lean'
BASE = 'c4c7be592c51c8ba81d1579082813310a22b356d'
PUBLISHED = '3da7a876b97815c99ebde0f4f9c17932096345a2'
STATEMENT_BASE = '36767fa430309f13d04dc6ebe080d470f5c2444a'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
checks = []
def sha(data): return hashlib.sha256(data).hexdigest()
def git_source(ref, path):
    return subprocess.check_output(['git', 'show', f'{ref}:{path}'], cwd=REPO)
def check(name, passed, **evidence):
    checks.append({'name': name, 'passed': bool(passed), **evidence})
def read_json(path): return json.loads((REPO/path).read_text())
registry = read_json('problem_ids.json')
check('all-217-ID-path-pairs-unchanged', len(registry) == 217 and registry == json.loads(git_source(BASE, 'problem_ids.json')))
readme_records = []
for ident, name in registry.items():
    old = git_source(BASE, name)
    current = (REPO/name).read_bytes()
    readme_records.append({'id': ident, 'path': name, 'sha256': sha(current), 'unchanged': old == current})
check('all-217-canonical-pages-unchanged-before-promotion', all(r['unchanged'] for r in readme_records), count=len(readme_records))
archive = read_json('docs/lean/proofs/TR-06/originals-c4c7be59/manifest.json')
archive_records = []
for item in archive['records']:
    original = git_source(BASE, item['source'])
    frozen = (REPO/item['archive']).read_bytes()
    current = (REPO/item['source']).read_bytes()
    archive_records.append({**item, 'base_matches': sha(original) == item['sha256'],
                            'archive_matches': frozen == original, 'current_matches': current == original})
check('all-five-originals-exact-archive-and-current', len(archive_records) == 5 and all(r['base_matches'] and r['archive_matches'] and r['current_matches'] for r in archive_records))
check('canonical-ORIGINAL-exact', (REPO/PROJECT/'ORIGINAL.md').read_bytes() == git_source(BASE, registry['TR-06']))
retained = read_json('docs/lean/proofs/TR-06/campaign-2026-10-18/retained-58-source-lock.json')['records']
retained_records = []
for item in retained:
    old = git_source(PUBLISHED, item['published_path'])
    shared = (REPO/item['campaign_path']).read_bytes()
    destination = PROJECT + '/' + item['campaign_path'].removeprefix('lean-statements/')
    copied = (REPO/destination).read_bytes()
    retained_records.append({**item, 'canonical_path': destination,
                             'passed': sha(old) == item['sha256'] and old == shared == copied})
check('all-58-published-sources-byte-exact-in-both-locations', len(retained_records) == 58 and all(r['passed'] for r in retained_records))
for name in ['NLA/Statements/TR06.lean', 'NLA/Statements/Infrastructure.lean', 'Reviewed/TR06.lean']:
    old = git_source(STATEMENT_BASE, 'lean-statements/' + name)
    check('unchanged-frozen-statement:' + name, old == (REPO/'lean-statements'/name).read_bytes() == (REPO/PROJECT/name).read_bytes())
original_config = json.loads(git_source(PUBLISHED, PROJECT + '/comparator.json'))
config = read_json(PROJECT + '/comparator.json')
check('exact-ten-published-exports-plus-separate-literal-target', config['theorem_names'] == original_config['theorem_names'] + ['NLA.TR06.target'])
check('no-definition-holes-standard-three-axioms', config['definition_names'] == [] and config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound'])
old_challenge = git_source(PUBLISHED, PROJECT + '/Challenge.lean').decode()
challenge = (REPO/PROJECT/'Challenge.lean').read_text()
added = """
namespace NLA.TR06

/-- The separate unchanged intrinsic target, including the exact volume-Gaussian
normalizer and intrinsic angular derivative. Comparison placeholder only. -/
theorem target : NLA.Statements.TR06.Target := by
  sorry

end NLA.TR06
"""
check('complete-published-Challenge-preserved', challenge == old_challenge.replace('import NLA.TR06.Definitions\n', 'import NLA.TR06.Definitions\nimport NLA.Statements.TR06\n', 1) + added)
check('exactly-eleven-intentional-Challenge-placeholders', len(re.findall(r'^  sorry$', challenge, re.M)) == 11)
solution = (REPO/PROJECT/'Solution.lean').read_text()
check('literal-Solution-target-closed-proof-no-Challenge-import', 'theorem target : NLA.Statements.TR06.Target := by\n  exact NLA.Proofs.TR06.target' in solution and not re.search(r'^import\s+Challenge\b', solution, re.M) and not re.search(r'\bsorry\b', solution))
proof_lock = read_json(PROJECT + '/proof-source-lock.json')
check('exact-140-source-copy-records-80-proofs-58-retained', len(proof_lock['copies']) == proof_lock['actual_copied_source_count'] == 140 and proof_lock['actual_proof_source_count'] == 80 and proof_lock['retained_source_count'] == 58)
copy_records = []
for item in proof_lock['copies']:
    source = (REPO/item['source']).read_bytes(); dest = (REPO/item['destination']).read_bytes()
    copy_records.append({'source': item['source'], 'destination': item['destination'], 'passed': source == dest and sha(source) == item['source_sha256'] == item['destination_sha256']})
check('all-140-copies-exact', all(r['passed'] for r in copy_records))
expected = {item['destination'].removeprefix(PROJECT + '/') for item in proof_lock['copies']} | {'Challenge.lean', 'Identity.lean', 'Solution.lean', 'Reviewed/TR06.lean'}
actual = {str(p.relative_to(REPO/PROJECT)) for p in (REPO/PROJECT).rglob('*.lean') if '.lake' not in p.relative_to(REPO/PROJECT).parts}
check('exact-144-Lean-input-set', len(expected) == 144 and expected == actual)
creation = read_json('docs/lean/proofs/TR-06/canonical-boundary-before-solution/SOLUTION_CREATION_RECORD_2026-10-23.json')
check('prior-two-independent-boundary-approvals-hash-bound', len(creation['prior_independent_approvals']) == 2 and all(sha((REPO/name).read_bytes()) == digest for name, digest in creation['prior_independent_approvals'].items()))
check('Solution-matches-creation-record', sha(solution.encode()) == creation['Solution_sha256'] and creation['Solution_absent_before_creation'] and creation['all70_boundary_inputs_matched_before_creation'])
report = {'scope': 'Pre-promotion source and original identity only; no Lean or Linux acceptance claim', 'base': BASE,
          'checks': checks, 'canonical_pages': readme_records, 'originals': archive_records, 'retained_sources': retained_records, 'copies': copy_records,
          'passed': all(c['passed'] for c in checks)}
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'passed': report['passed'], 'checks': len(checks), 'failed': [c['name'] for c in checks if not c['passed']]}, indent=2))
raise SystemExit(0 if report['passed'] else 1)
