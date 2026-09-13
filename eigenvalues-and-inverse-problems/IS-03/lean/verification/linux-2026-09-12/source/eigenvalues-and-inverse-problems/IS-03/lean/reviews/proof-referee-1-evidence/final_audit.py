"""Final preservation and actual-evidence checks before independent sealing."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

OUT = Path(__file__).resolve().parent
P = OUT.parents[1]
REPO = P.parents[2]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda r: json.loads((OUT / r).read_text())
c = load('context.json')
assert sha(P / 'verification/proof-freeze.json') == c['freeze_sha256']
assert sha(P / 'reviews/proof-completion.md') == c['completion_sha256']
f = json.loads((P / 'verification/proof-freeze.json').read_text())
for r, h in f['files'].items():
    assert sha(P / r) == h, r
for r, h in f['source_files'].items():
    original = subprocess.check_output(['git', '-C', str(REPO), 'show', f['base'] + ':' + r])
    assert (REPO / r).read_bytes() == original
    assert hashlib.sha256(original).hexdigest() == h
assert len(f['files']) == 203 and len(f['source_files']) == 10
fresh = load('fresh-checks.json')
assert fresh['result'] == 'PASS' and len(fresh['commands']) == 10
for r in fresh['commands']:
    assert r['exit_code'] == 0 and sha(P / r['source']) == r['source_sha256']
    assert sha(OUT / r['log']) == r['log_sha256']
    for obj, h in r['fresh_objects'].items():
        assert sha(Path(fresh['fresh_prefix']) / obj) == h
cert = load('certificate-check.json')
assert cert['exit_code'] == 0 and cert['LEAN_PATH'] == fresh['LEAN_PATH']
assert sha(P / cert['source']) == cert['source_sha256']
assert sha(OUT / 'Certificate.log') == cert['log_sha256']
allowed = ['propext', 'Classical.choice', 'Quot.sound']
extra_axioms = []
for n in ['reviews-proof-referee-1-evidence-Inspect.log', 'Certificate.log']:
    for declaration, values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", (OUT / n).read_text()):
        values = [x.strip() for x in values.split(',') if x.strip()]
        assert values == allowed
        extra_axioms.append({'declaration': declaration, 'axioms': values, 'log': n})
assert len(extra_axioms) == 6
candidate = load('candidate-axioms.json')
assert candidate['count'] == 18
assert len({r['declaration'] for r in candidate['reports']}) == 18
for r in candidate['reports']:
    assert r['axioms'] == allowed
inspection = (OUT / 'reviews-proof-referee-1-evidence-Inspect.log').read_text()
certificate = (OUT / 'Certificate.log').read_text()
assert 'NLA.IS03.numerical_negative_moment._proof_1_7' in inspection
assert 'verify_strict_upper_bound_dyadic_checked' in inspection
assert 'of_decide_eq_true (id (Eq.refl true))' in certificate
assert 'checkStrictUpperBoundDyadicChecked' in certificate
assert '(-53) 10' in certificate
assert 'decide +kernel' in (OUT / 'Certificate.lean').read_text()
deps = load('actual-dependencies.json')
assert deps['project_declarations'] == 61 and len(deps['required_dependencies']) == 33
for n in ['NLA.IS03.numerical_negative_moment', 'NLA.IS03.negative_moment_proved',
          'NLA.IS03.counterexample_proved', 'NLA.IS03.trace_moment_certificate_proved']:
    assert n in deps['required_dependencies']
assert load('reconstruction.json')['status'] == 'PASS'
for d in load('dependency-pins.json'):
    path = d['path']
    assert subprocess.check_output(['git', '-C', path, 'rev-parse', 'HEAD'], text=True).strip() == d['revision']
    assert not subprocess.check_output(['git', '-C', path, 'status', '--porcelain'])
assert not subprocess.check_output(['git', '-C', str(REPO), 'diff', '--name-only'])
report = P / 'reviews/proof-referee-1.md'
assert '**Verdict: APPROVE' in report.read_text()
record = {'verdict': 'APPROVE complete frozen mathematics; local independent final review only',
    'reviewer_role': c['role'], 'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'freeze_sha256': c['freeze_sha256'], 'completion_sha256': c['completion_sha256'],
    'frozen_project_inputs_unchanged': 203, 'frozen_statement_inputs_unchanged': 34,
    'original_sources_unchanged': 10, 'fresh_commands': 10, 'additional_certificate_commands': 1,
    'candidate_kernel_axiom_checks': 18, 'additional_kernel_axiom_checks': extra_axioms,
    'safe_total_project_declarations': 61, 'material_dependencies': 33,
    'exact_headers': load('source-signatures.json')['headers'],
    'proof_source_hashes': load('source-safety.json'),
    'fresh_receipt_sha256': sha(OUT / 'fresh-checks.json'),
    'certificate_receipt_sha256': sha(OUT / 'certificate-check.json'),
    'independent_arithmetic_sha256': sha(OUT / 'reconstruction.json'),
    'report_sha256': sha(report), 'tracked_source_diffs_empty': True,
    'ten_dependency_pins_clean': True, 'Linux_Comparator_run': False,
    'documentation_item': 'D1: preserve/archive historical README before ordinary completed-proof candidate refresh. No frozen mathematical edit requested.'}
(OUT / 'final-audit.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({k: record[k] for k in ['verdict', 'frozen_project_inputs_unchanged', 'fresh_commands',
    'additional_certificate_commands', 'candidate_kernel_axiom_checks', 'safe_total_project_declarations',
    'material_dependencies', 'report_sha256']}, indent=2))
