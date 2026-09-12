"""Validate MI-23 candidate metadata without changing mathematical or canonical files."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

OUT = Path(__file__).resolve().parent
PROJECT = OUT.parents[1]
REPO = PROJECT.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO).decode().strip()


before = json.loads((OUT / 'inputs-before-packaging.json').read_text())
freeze_path = PROJECT / 'reviews/proof-freeze.json'
freeze = json.loads(freeze_path.read_text())
assert sha(freeze_path) == '18fbf9a74e6006ca2b4159be62730c6df4faf38d472250b8ca1e7e54bf392ecb'
assert len(freeze['files']) == 25
for rel, rec in before.items():
    check = OUT / 'frozen-local-proof-README.md' if rel == 'README.md' else PROJECT / rel
    assert sha(check) == rec['sha256'] and check.stat().st_size == rec['bytes'], rel
for rel, rec in freeze['files'].items():
    check = OUT / 'frozen-local-proof-README.md' if rel == 'README.md' else PROJECT / rel
    assert sha(check) == rec['sha256'], rel
assert sha(PROJECT / 'README.md') != before['README.md']['sha256']

commands = [
    (['/tmp/nla-lean-formalization/venv/bin/python', 'tools/lean/validate_manifest.py', str(PROJECT.relative_to(REPO))], 'metadata-validation.log'),
    (['python3', 'tools/validate_problem_ids.py', '--base-ref', 'origin/main'], 'permanent-ids.log'),
    (['python3', '-m', 'unittest', 'discover', '-s', 'tests', '-p', 'test_problem_ids.py', '-v'], 'permanent-id-tests.log'),
]
checks = []
for args, name in commands:
    proc = subprocess.run(args, cwd=REPO, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (OUT / name).write_bytes(proc.stdout)
    checks.append({'argv': args, 'cwd': str(REPO), 'exit_code': proc.returncode,
                   'log': name, 'log_sha256': sha(OUT / name)})
    assert proc.returncode == 0, (args, proc.stdout.decode())

sources = {}
for rel in ['matrix-inequalities-and-norms/MI-23/README.md',
            'matrix-inequalities-and-norms/MI-23/solution.tex',
            'matrix-inequalities-and-norms/MI-23/solution.md',
            'matrix-inequalities-and-norms/MI-23/solution.pdf']:
    data = subprocess.check_output(['git', 'show', freeze['repository_base'] + ':' + rel], cwd=REPO)
    assert (REPO / rel).read_bytes() == data
    sources[rel] = {'sha256': sha(REPO / rel), 'bytes': len(data)}
assert '**Status:** Solved' in (PROJECT.parent / 'README.md').read_text()

pins = []
for pkg in json.loads((PROJECT / 'lake-manifest.json').read_text())['packages']:
    path = PROJECT / '.lake/packages' / pkg['name']
    rev = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path).decode().strip()
    clean = not subprocess.check_output(['git', 'status', '--porcelain'], cwd=path).strip()
    assert rev == pkg['rev'] and clean, pkg['name']
    pins.append({'package': pkg['name'], 'revision': rev, 'clean': clean})
assert len(pins) == 10
(OUT / 'dependencies.json').write_text(json.dumps(pins, indent=2) + '\n')

links = re.findall(r'\]\(([^)]+)\)', (PROJECT / 'README.md').read_text())
for link in links:
    if not re.match(r'\w+://', link):
        assert (PROJECT / link.split('#')[0]).exists(), link
ignored = (PROJECT / '.gitignore').read_text().splitlines()
assert {'.lake/', '*.olean', '*.ilean', '*.trace'} <= set(ignored)
assert git('diff', '--name-only') == '' and git('diff', '--cached', '--name-only') == ''
selected = json.loads((PROJECT / 'comparator.json').read_text())
assert len(selected['theorem_names']) == 8 and selected['definition_names'] == []

reports = {rel: sha(PROJECT / rel) for rel in [
    'reviews/statement-referee-1.md', 'reviews/statement-referee-2.md',
    'reviews/proof-referee-1.md', 'reviews/proof-referee-2.md']}
assert reports['reviews/proof-referee-1.md'] == '37985a31879f155da1b52d1cb9c955bb844d16edc862ccca327b3f0aaade8da1'
assert reports['reviews/proof-referee-2.md'] == '707f40dc07f789e0a201ebf2c158c86897e047ae898e7b776854f92d0f94ff02'
record = {
    'verdict': 'PASS for root review of a Linux candidate; actual Linux verification pending',
    'packager': '/root/solved_statement_inventory',
    'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'branch': git('branch', '--show-current'), 'base_commit': git('rev-parse', 'HEAD'),
    'permanent_id_validation_base': git('rev-parse', 'origin/main'),
    'original_publishable_input_count': len(before),
    'unchanged_original_input_count_excluding_current_readme': len(before) - 1,
    'all_prior_reviews_and_evidence_unchanged': True,
    'all_24_remaining_proof_freeze_inputs_unchanged': True,
    'historical_readme': {'old_sha256': before['README.md']['sha256'],
                          'archive': str((OUT / 'frozen-local-proof-README.md').relative_to(PROJECT)),
                          'current_sha256': sha(PROJECT / 'README.md')},
    'formalization_yaml_sha256': sha(PROJECT / 'formalization.yaml'),
    'proof_freeze_sha256': sha(freeze_path),
    'reports': reports, 'exports': selected['theorem_names'],
    'source_files_unchanged': sources,
    'lean_cert_role': 'One retained kernel-mode scalar gap certificate on a singleton interval, with actual analytic bridges and exact finite matrix arithmetic.',
    'metadata_and_required_checks': checks,
    'readme_links_checked': links,
    'clean_dependency_pins': 10,
    'existing_artifact_exclusions_preserved': True,
    'tracked_and_staged_diff_empty': True,
    'canonical_status': 'Solved, byte-identical',
    'scope': 'Only current README and new v0.4 metadata/evidence packaging. No mathematical, configuration, pin, shared harness, canonical target, ID or prior evidence edits; no index regeneration, commit, push, PR or Linux run.'
}
(OUT / 'packaging-record.json').write_text(json.dumps(record, indent=2) + '\n')
print('PASS: metadata/8 exports, permanent IDs/tests, preserved 120 prior inputs plus archived README, 24 frozen non-README files, all four reports, ten clean pins and canonical Solved status.')
print('README:', sha(PROJECT / 'README.md'))
print('formalization.yaml:', sha(PROJECT / 'formalization.yaml'))
print('packaging-record.json:', sha(OUT / 'packaging-record.json'))
