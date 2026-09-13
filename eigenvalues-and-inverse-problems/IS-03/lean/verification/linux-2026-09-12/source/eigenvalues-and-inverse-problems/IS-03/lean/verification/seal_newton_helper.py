"""Record the completed root-owned helper without claiming final independent review."""
from pathlib import Path
import hashlib, json, datetime
P = Path(__file__).resolve().parents[1]
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
latest = json.loads((P / 'verification/newton-development/latest.json').read_text())
run = Path(latest['attempt'])
rec = json.loads((run / 'result.json').read_text())
log = (run / 'Newton.log').read_text()
assert all(x['exit_code'] == 0 for x in rec['commands'])
assert 'sorryAx' not in log and 'error:' not in log and 'warning:' not in log
assert log.count('depends on axioms: [propext, Classical.choice, Quot.sound]') == 3
freeze = json.loads((P / 'reviews/statement-freeze.json').read_text())
for rel, h in freeze['files'].items(): assert sha(P / rel) == h, rel
src = P / 'NLA/IS03/Newton.lean'
assert rec['commands'][-1]['source_sha256'] == sha(src)
record = {
 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'author': '/root', 'role': 'IS-03 proof coauthor, not an independent final referee',
 'module': 'NLA/IS03/Newton.lean', 'source_sha256': sha(src),
 'public_helper': 'NLA.IS03.power_sums_of_derivative_product',
 'hypotheses': 'Arbitrary finite complex family, cardinality six, actual product of X-C(mu i) equal to the complex map of q; no distinctness or spectral assumption',
 'conclusion': 'All seven actual finite power sums equal the source real moments mapped to Complex',
 'method': 'Actual Mathlib Multiset Vieta and MvPolynomial Newton identities; only seven finite antidiagonals expanded, no coordinate enumeration, roots or interval approximation. Elementary values recovered from actual polynomial coefficients. Imports narrowed to actual required modules.',
 'development_result': str(run / 'result.json'), 'development_result_sha256': sha(run / 'result.json'),
 'log_sha256': sha(run / 'Newton.log'), 'all_three_kernel_checks_and_standard_three_axioms': True,
 'unchanged_frozen_statement_inputs': len(freeze['files']),
 'history': 'Development attempts retain their exact source snapshots and raw errors/warnings. An initial handoff assertion caught harmless sequence-focus linter warnings before a handoff was written; those proof lines were simplified and the final run has no warning or error. No frozen statement changed.',
 'scope': 'Iterative macOS helper development using a private project prefix and read-only pinned MI22 dependency objects. Complete fresh final proof checks and two independent final reviews remain pending.'}
out = P / 'verification/newton-helper-handoff.json'
assert not out.exists()
out.write_text(json.dumps(record, indent=2) + '\n')
print(log)
print(json.dumps({'helper_sha256': sha(src), 'handoff_sha256': sha(out),
                  'statement_inputs_preserved': len(freeze['files'])}))
