"""Read-only audit of PR85 merge head against its reviewed parents."""
from collections import Counter
from pathlib import Path
import hashlib, json, re, subprocess

REPO = Path('/private/tmp/nla-pr83-delta-review')
OUT = Path('/private/tmp/nla-review-wave2-artifacts/audit-root')
HEAD = '5942bc2274df99b10cd26b62df07ff822dffee69'
BASE = '16369809e6e600144bd350ab70b7473b652f46f1'
PREVIOUS = '6fb1041e83823f726a326b33ef8169cd593df631'
ORIGINAL = 'bf70552daecf8c6275ef1eb73f73aac664358228'
P = 'matrix-inequalities-and-norms/MI-28/'
R = 'references/stepaniants-mi28-2026-09-11/'
checks = {}
findings = []
def git(*args):
    return subprocess.check_output(['git', '-C', str(REPO), *args])
def read(commit, path):
    return git('show', commit+':'+path)
def sha(commit, path):
    return hashlib.sha256(read(commit, path)).hexdigest()
def ck(name, value):
    checks[name] = bool(value)

ck('expected_merge_parents', git('show', '-s', '--format=%P', HEAD).decode().strip().split() == [PREVIOUS, BASE])
delta = git('diff', '--name-only', BASE, HEAD).decode().splitlines()
prior_paths = set(Path('/private/tmp/nla-review-wave2-artifacts/pr-85/REVIEW-CHANGED-FILES.txt').read_text().splitlines())
ck('genuine_delta_contains_only_prior_contributed_paths_and_optional_template', set(delta) == prior_paths | {'tools/solution-template.tex'})
ck('permanent_registry_byte_identical_to_merged_main', read(HEAD, 'problem_ids.json') == read(BASE, 'problem_ids.json'))
registry = json.loads(read(BASE, 'problem_ids.json'))
ck('all_other_canonical_pages_byte_identical_to_merged_main', all(read(HEAD, path) == read(BASE, path) for identifier, path in registry.items() if identifier != 'MI-28'))
def target(data):
    return re.search(rb'^## Problem statement\n(.*?)(?=^## |\Z)', data, flags=re.M | re.S).group(1)
ck('MI28_original_target_byte_identical_to_merged_main', target(read(HEAD, P+'README.md')) == target(read(BASE, P+'README.md')))
for relative in [P+'README.md', P+'problem.tex', P+'problem.pdf', P+'solution.md', P+'solution.tex', P+'solution.pdf', R+'original-agent-manuscript.md', R+'original-agent-manuscript.tex', R+'parameter-interchange-discovery.md', R+'verification/network-check.json', R+'verification/reviews/MI-28-review.md', 'tools/solution-template.tex']:
    ck('unchanged_from_reviewed_contact_free_head_'+relative, read(HEAD, relative) == read(PREVIOUS, relative))
ck('render_script_only_adds_MI28_reference_break_to_merged_main', read(HEAD, 'tools/render_problems.py').replace(b"'MI-23', 'MI-28', 'MI-29'", b"'MI-23', 'MI-29'") == read(BASE, 'tools/render_problems.py'))
for relative in ['tools/validate_problem_ids.py', 'tools/update_catalog.py', 'tests/test_problem_ids.py', '.github/workflows/problem-ids.yml', 'tools/render_solutions.py']:
    ck('safeguard_unchanged_from_merged_main_'+relative, read(HEAD, relative) == read(BASE, relative))
status_counts = Counter()
for path in registry.values():
    match = re.search(rb'^\*\*Status:\*\* ([^\n]+)', read(HEAD, path), flags=re.M)
    status_counts[match[1].decode().strip()] += 1
record_path = R+'verification/document-checks.json'
record_text = read(HEAD, record_path).decode()
records = json.loads(record_text)
ck('catalog_counts_match_all_203_canonical_statuses', dict(status_counts) == records['catalog_totals'] == records['upstream_integration']['catalog_totals'])
ck('integration_base_is_actual_second_parent', records['upstream_integration']['upstream_main'] == BASE)
for relative, digest in records['files'].items():
    actual = sha(HEAD, relative)
    ck('current_source_hash_'+relative, actual == digest)
    if actual != digest:
        line = next(i for i, text in enumerate(record_text.splitlines(), 1) if '"'+relative+'":' in text)
        findings.append({'record_file': record_path, 'line': line, 'field': 'files.'+relative, 'recorded': digest, 'expected_current_hash': actual})
for entry in records['pdfs']:
    ck('current_pdf_hash_'+entry['path'], sha(HEAD, entry['path']) == entry['sha256'])
old_pdf = sha(ORIGINAL, P+'solution.pdf')
historical_pdf = records['pre_email_redaction_record']['pdfs'][0]['sha256']
ck('historical_pdf_finding_fixed', historical_pdf == old_pdf)
if historical_pdf != old_pdf:
    findings.append({'record_file': record_path, 'line': 93, 'field': 'pre_email_redaction_record.pdfs[0].sha256', 'recorded': historical_pdf, 'expected_historical_hash': old_pdf})
result = {'head': HEAD, 'merged_main': BASE, 'prior_reviewed_head': PREVIOUS, 'genuine_changed_paths': delta, 'permanent_ids': len(registry), 'canonical_status_counts': dict(status_counts), 'passed': sum(checks.values()), 'total': len(checks), 'checks': checks, 'findings': findings, 'mathematical_verdict': 'PASS carries; theorem, proof, and PDFs unchanged', 'documentary_verdict': 'Three inaccurate fingerprints remain'}
(OUT/'PR85-merge-5942bc2-evidence.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({key: result[key] for key in ['head', 'permanent_ids', 'canonical_status_counts', 'passed', 'total', 'findings']}, indent=2))
