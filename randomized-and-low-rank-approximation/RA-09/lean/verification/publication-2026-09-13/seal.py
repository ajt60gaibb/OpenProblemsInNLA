from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess, yaml

R = Path('/tmp/nla-lean-ra09-worktree')
E = R/'randomized-and-low-rank-approximation/RA-09'
P = E/'lean'
O = P/'verification/publication-2026-09-13'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
before = json.loads((O/'before.json').read_text())
assert not (O/'EVIDENCE-MANIFEST.json').exists()
archive = {'README.md': O/'archive/README.linux-candidate.md', 'formalization.yaml': O/'archive/formalization.linux-candidate.yaml'}
for rel, digest in before['all_prior_project_files'].items():
    f = archive.get(rel, P/rel)
    assert sha(f) == digest, rel
assert len(before['all_prior_project_files']) == 1235
for rel, digest in before['candidate_inputs'].items(): assert sha(archive.get(rel, P/rel)) == digest, rel
assert len(before['candidate_inputs']) == 524
for rel, digest in before['immutable_operational_files'].items(): assert sha(P/rel) == digest, rel
assert len(before['immutable_operational_files']) == 711
target = (E/'README.md').read_text().split('Let $`n\\ge2`$', 1)[1]
target = 'Let $`n\\ge2`$' + target
assert hashlib.sha256(target.encode()).hexdigest() == before['canonical_target_sha256']
assert sha(R/'problem_ids.json') == before['registry_sha256']
old = yaml.safe_load(archive['formalization.yaml'].read_text())
new = yaml.safe_load((P/'formalization.yaml').read_text())
def differences(a, b, path=''):
    if isinstance(a, dict) and isinstance(b, dict):
        assert set(a) == set(b), path
        return sum((differences(a[k], b[k], path+'.'+str(k) if path else str(k)) for k in a), [])
    return [] if a == b else [path]
fields = differences(old, new)
expected_fields = ['status.scope', 'review.status', 'review.notes', 'review.linux_verification.status', 'review.linux_verification.note', 'review.candidate_documents.installation']
assert set(fields) == set(expected_fields), fields
source_freeze = json.loads((P/'verification/proof-freeze.json').read_text())
statement = json.loads((P/'reviews/statement-freeze.json').read_text())
for freeze, count in [(source_freeze, 361), (statement, 31)]:
    assert len(freeze['files']) == count and len(freeze['source_files']) == 17
    for rel, digest in freeze['files'].items():
        path = P/('verification/pre-candidate-README.md' if rel == 'README.md' else rel)
        assert sha(path) == digest, rel
    for rel, digest in freeze['source_files'].items():
        data = subprocess.check_output(['git', 'show', before['base']+':'+rel], cwd=R)
        assert hashlib.sha256(data).hexdigest() == digest
        assert sha(P/'verification/linux-2026-09-13/source'/rel) == digest, rel
expected = {'CATALOG.md', 'README.md', 'RESOLVED.md', 'randomized-and-low-rank-approximation/README.md',
    str((E/'README.md').relative_to(R)), str((E/'problem.tex').relative_to(R)), str((E/'problem.pdf').relative_to(R)),
    str((P/'README.md').relative_to(R)), str((P/'formalization.yaml').relative_to(R))}
changed = set(subprocess.check_output(['git', 'diff', '--name-only', 'HEAD'], cwd=R, text=True).splitlines())
assert changed == expected, changed
checks = json.loads((O/'checks.json').read_text())
assert len(checks) == 9 and all(c['exit_code'] == 0 for c in checks)
for c in checks: assert sha(O/c['log']) == c['log_sha256']
layout = json.loads((O/'layout-correction.json').read_text())
assert len(layout['checks']) == 2
for c in layout['checks']: assert c['exit_code'] == 0 and sha(O/c['raw_log']) == c['log_sha256']
assert 'Overfull' not in (O/'render-final.log').read_text()
for name, digest in layout['after'].items(): assert sha(E/name) == digest
assert len(layout['pages']) == 3
for path, digest in layout['pages'].items(): assert sha(path) == digest
config = json.loads((P/'comparator.json').read_text())
canonical = (E/'README.md').read_text()
assert '**Status:** Lean verified' in canonical and len(config['theorem_names']) == 17
for name in config['theorem_names']: assert '`'+name.removeprefix('NLA.RA09.')+'`' in canonical
assert 'NLA.RA09.concaveFrobeniusTransferConjecture' in canonical
assert 'tools/lean/bootstrap.sh' in canonical and 'tools/lean/selftest.sh' in canonical and 'tools/lean/verify.sh' in canonical
assert all(k in canonical for k in ['0df444a360eaa60ab8c11dca51a86af692955474','621a43d7cf21f87872392a01e874f2f1dbddc926',before['candidate'],'Lean 4.33.1'])
diff = subprocess.run(['git', 'diff', '--check', 'HEAD'], cwd=R, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(O/'tracked-diff-check.log').write_bytes(diff.stdout)
assert diff.returncode == 0, diff.stdout.decode()
record = {
    'status': 'PASS complete publication preparation; independent publication review pending',
    'utc': datetime.now(timezone.utc).isoformat(), 'problem': 'RA-09', 'candidate': before['candidate'],
    'prior_project_files_preserved_through_exact_wrapper_archives': 1235,
    'candidate_inputs': 524, 'only_two_candidate_wrappers_changed': True,
    'immutable_operational_files': 711, 'statement_inputs': 31, 'proof_inputs': 361,
    'original_source_Git_blobs': 17, 'original_canonical_suffix_unchanged': True,
    'registry_unchanged': True, 'all_217_IDs_and_17_tests_passed': True,
    'manifest_semantic_fields_changed': fields,
    'publication_files': {rel: sha(R/rel) for rel in sorted(expected)},
    'root_visual_review': 'Root displayed every initial and final PDF page. Final three pages are legible and unclipped; original implication and its full explanation remain together on page two. The sole initial overfull shell line was corrected by equivalent line continuations, with the original render and artifacts retained.',
    'final_pdf_sha256': sha(E/'problem.pdf'), 'final_tex_sha256': sha(E/'problem.tex'),
    'actual_final_pages': layout['pages'], 'scope': 'Publication and source-preservation checks, no new mathematical or Linux execution claim',
    'next_gate': 'Independent concrete publication audit before commit, normal push and new upstream main PR',
}
(O/'INTEGRITY-CHECKS.json').write_text(json.dumps(record, indent=2)+'\n')
(O/'seal.py').write_bytes(Path(__file__).read_bytes())
for source in ['prepare_ra09_operational_acceptance.py', 'ra09-root-acceptance-adaptation.json']:
    (O/source).write_bytes((Path('/tmp/nla-lean-formalization')/source).read_bytes())
files = {str(f.relative_to(O)): {'sha256': sha(f), 'bytes': f.stat().st_size} for f in sorted(O.rglob('*')) if f.is_file()}
(O/'EVIDENCE-MANIFEST.json').write_text(json.dumps({'files': files, 'file_count': len(files), 'exact_self_exclusion': 'EVIDENCE-MANIFEST.json', 'inventory_rule': 'Every file below this publication directory, including all nested files; only the exact outer self path is excluded'}, indent=2)+'\n')
print(json.dumps({'publication': 'ready for independent review', 'integrity_sha256': sha(O/'INTEGRITY-CHECKS.json'), 'outer_sha256': sha(O/'EVIDENCE-MANIFEST.json'), 'bound_files': len(files), 'pdf_sha256': sha(E/'problem.pdf')}, indent=2))
