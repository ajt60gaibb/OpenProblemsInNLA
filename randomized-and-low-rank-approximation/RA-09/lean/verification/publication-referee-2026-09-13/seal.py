"""Seal only this referee's report/evidence, preserving every reviewed input."""
from pathlib import Path
import datetime, hashlib, json, os

E = Path(__file__).resolve().parent
P = E.parents[1]
R = P.parents[2]
O = P / 'verification/publication-2026-09-13'
L = P / 'verification/linux-2026-09-13'
REPORT = P / 'reviews/publication-referee-2026-09-13.md'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
row = lambda p: {'sha256': sha(p), 'bytes': Path(p).stat().st_size}

checks = json.loads((E / 'checks.json').read_text())
assert checks['status'].startswith('PASS')
assert sha(E / 'checks.json') == 'c243a9ef9e8ffab87794d2ff955be1548953bcab63bdbf69349a120c55412508'
consulted = json.loads((E / 'consulted-inputs.json').read_text())
for rel, h in consulted.items():
    assert row((E / rel).resolve()) == h, rel
jobs = json.loads((P / 'verification/root-operational-2026-09-13/observed-jobs.json').read_text())
run = json.loads((P / 'verification/root-operational-2026-09-13/observed-run.json').read_text())
assert run['id'] == 34738884548 and run['head_sha'] == '3bcc863070c037fffb1deee3f12d1cd1517727df'
assert run['status'] == 'completed' and run['conclusion'] == 'success'
assert jobs['total_count'] == len(jobs['jobs']) == 17
assert all(j['conclusion'] == 'success' and j['status'] == 'completed' for j in jobs['jobs'])
assert all(s['conclusion'] == 'success' for j in jobs['jobs'] for s in j['steps'])
runtime = json.loads((L / 'runtime-verification.json').read_text())
pins = json.loads((P / 'lake-manifest.json').read_text())['packages']
assert pins == runtime['fresh_dependency_pins'] and len(pins) == 10
dependencies = (L / 'artifacts/lean-RA-09/verify-20260913T045251Z-4175/dependencies.log').read_text()
for pin in pins:
    assert f"{pin['name']}: checking out revision '{pin['rev']}'" in dependencies
cache = (L / 'artifacts/lean-RA-09/verify-20260913T045251Z-4175/mathlib-cache.log').read_text()
assert 'Decompressed 8690 file(s)' in cache
start = json.loads((E / 'START.json').read_text())
assert sha(P.parent / 'problem.pdf') == start['pdf_sha256']
for n, h in start['rendered_pages'].items():
    assert sha(E / 'pages' / n) == h
assert len(start['rendered_pages']) == 3
skill = Path('/Users/georgestepaniants/.codex/plugins/cache/openai-primary-runtime/pdf/26.904.11930/skills/pdf/SKILL.md')
(E / 'PDF-SKILL.md').write_bytes(skill.read_bytes())
verdict = {
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'verdict': 'APPROVE independent publication review',
    'role': 'Proof coauthor; independent of root publication edits; no additional mathematical approval',
    'report': str(REPORT.relative_to(P)), 'report_sha256': sha(REPORT),
    'checks_sha256': sha(E / 'checks.json'),
    'preparer_outer_sha256': sha(O / 'EVIDENCE-MANIFEST.json'),
    'preparer_integrity_sha256': sha(O / 'INTEGRITY-CHECKS.json'),
    'all_consulted_input_identities_preserved': len(consulted),
    'six_fresh_read_only_checks_passed': True,
    'all_17_actual_run_jobs_and_every_step_successful': True,
    'actual_dependency_checkouts_match_all_ten_pins': True,
    'actual_official_cache_count': 8690,
    'pdf_sha256': sha(P.parent / 'problem.pdf'),
    'tex_sha256': sha(P.parent / 'problem.tex'),
    'fresh_rendered_pages': start['rendered_pages'],
    'visual_findings': {
        'page_1': 'Readable credit, source scope, exact exports and continuing verification paragraph; no clipping.',
        'page_2': 'Readable wrapped commands and complete original implication with all quantifiers and same-basis convention; no overflow.',
        'page_3': 'All references and clearly dated historical status audits retained; no missing glyphs or layout defect.',
    },
    'pdf_skill': {'original_path': str(skill), 'sha256': sha(skill),
                  'retained_snapshot': 'PDF-SKILL.md', 'operation': 'read-only audit; no PDF authoring marker required'},
    'reviewer_diagnostics': ['attempt-1: newly added heading was absent in old candidate; actual original suffix checked',
                             'attempt-2: exact Bubblewrap message uses uid map with a space'],
    'publication_corrections_requested': [],
    'mathematical_or_Linux_commands_executed_by_reviewer': [],
    'new_publication_input_edits_or_repository_Git_mutation': False,
    'next_action': 'Coordinator may perform integration, commit, normal push and upstream PR subject to preserving this reviewed scope',
}
(E / 'FINAL.json').write_text(json.dumps(verdict, indent=2) + '\n')
outer = E / 'EVIDENCE-MANIFEST.json'
assert not outer.exists()
files = {f.resolve() for f in E.rglob('*') if f.is_file() and f.resolve() != outer.resolve()}
files.update((E / n).resolve() for n in consulted)
files.add(REPORT.resolve())
inventory = {
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'verdict': verdict['verdict'], 'report_sha256': sha(REPORT),
    'scope': 'Every referee artifact, exact consulted input and this report; pure publication review, no additional mathematical approval',
    'root': '.', 'exact_self_exclusion': 'EVIDENCE-MANIFEST.json',
    'inventory_rule': 'Only this exact outer self path is excluded. Nested same-basename manifests and all raw prior attempts are included.',
    'files': {os.path.relpath(f, E): row(f) for f in sorted(files)},
    'file_count': len(files),
}
outer.write_text(json.dumps(inventory, indent=2) + '\n')
for n, h in inventory['files'].items():
    assert row((E / n).resolve()) == h, n
print(json.dumps({'verdict': verdict['verdict'], 'report_sha256': sha(REPORT),
                  'outer_sha256': sha(outer), 'bound_files': len(files),
                  'final_sha256': sha(E / 'FINAL.json'),
                  'all_identity_rechecks': 'PASS'}, indent=2))
