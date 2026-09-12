"""Verify FR-12 Linux candidate packaging without rebuilding unchanged mathematics.
Preserves the frozen inputs and original canonical pages, validates current
metadata and records clean actual dependency pins. This is not Linux execution.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess
import time
import yaml

OUT = Path(__file__).resolve().parent
PROJECT = OUT.parents[1]
REPO = PROJECT.parents[2]
FREEZE_SHA = 'c65d4deaa3e02af8c20a584dd81b944dbdc72f262e326630e115e5fc9070aa87'
PYTHON = '/tmp/nla-lean-formalization/venv/bin/python'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def capture(command, cwd=REPO):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()

before = json.loads((OUT / 'inputs-before.json').read_text())
freeze_path = PROJECT / 'reviews/proof-freeze.json'
assert sha(freeze_path) == FREEZE_SHA
freeze = json.loads(freeze_path.read_text())
unchanged = {}
for name, expected in freeze['files'].items():
    if name == 'README.md':
        assert sha(PROJECT / name) != expected
        assert sha(OUT / 'frozen-statement-stage-README.md') == expected
    else:
        assert sha(PROJECT / name) == expected, name
        unchanged[name] = expected
assert len(unchanged) == 73
for name, expected in freeze['source_files'].items():
    assert sha(REPO / name) == expected, name
for name, expected in before['report_sha256'].items():
    assert sha(PROJECT / name) == expected, name
registry = json.loads((REPO / 'problem_ids.json').read_text())
assert sha(REPO / 'problem_ids.json') == before['problem_ids_sha256']
assert len(registry) == 217
for ident, expected in before['canonical_pages'].items():
    assert sha(REPO / registry[ident]) == expected, ident
assert '**Status:** Solved' in (PROJECT.parent / 'README.md').read_text()
assert capture(['git', 'diff', '--name-only']) == ''
assert capture(['git', 'rev-parse', 'HEAD']) == before['head']

metadata = yaml.safe_load((PROJECT / 'formalization.yaml').read_text())
config = json.loads((PROJECT / 'comparator.json').read_text())
assert len(config['theorem_names']) == 7
assert [row['declaration'] for row in metadata['status']['main_results']] == config['theorem_names']
assert [row['declaration'] for row in metadata['alignment']] == config['theorem_names']
assert config['definition_names'] == []
assert metadata['status']['sorry_count'] == metadata['status']['sorry_in_definitions'] == 0
assert metadata['review']['linux_verification']['status'] == 'pending'
assert 'Canonical status remains Solved' in metadata['status']['scope']
assert metadata['project']['authors'] == ['George Stepaniants']
affiliation = metadata['project']['affiliations']['George Stepaniants']
assert affiliation == 'Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'
for section in ['statement_reports', 'proof_reports']:
    for row in metadata['review'][section]:
        assert row['sha256'] == sha(PROJECT / row['file']) == before['report_sha256'][row['file']]
assert metadata['review']['proof_freeze']['sha256'] == sha(freeze_path)
new_content = (PROJECT / 'README.md').read_text() + (PROJECT / 'formalization.yaml').read_text()
assert not re.findall(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}', new_content)
assert 'm!' in new_content and '(2m−1)!!' in new_content

pins = []
for package in json.loads((PROJECT / 'lake-manifest.json').read_text())['packages']:
    path = PROJECT / '.lake/packages' / package['name']
    current = capture(['git', 'rev-parse', 'HEAD'], path)
    dirty = capture(['git', 'status', '--porcelain'], path)
    assert current == package['rev'] and not dirty, package['name']
    pins.append({'name': package['name'], 'expected': package['rev'], 'actual': current,
                 'git_status_porcelain': dirty})
assert len(pins) == 10
(OUT / 'dependency-check.json').write_text(json.dumps(pins, indent=2) + '\n')

commands = [
    ([PYTHON, 'tools/lean/validate_manifest.py', 'frames-and-matrix-designs/FR-12/lean'], 'metadata-validation.log'),
    (['python3', 'tools/validate_problem_ids.py', '--base-ref', 'origin/main'], 'permanent-ids-origin.log'),
    (['python3', 'tools/validate_problem_ids.py', '--base-ref', 'nla-upstream/main'], 'permanent-ids-upstream.log'),
    (['python3', '-m', 'unittest', 'discover', '-s', 'tests', '-p', 'test_problem_ids.py', '-v'], 'permanent-id-tests.log'),
]
checks = []
for command, log in commands:
    started = time.monotonic()
    with (OUT / log).open('w') as output:
        result = subprocess.run(command, cwd=REPO, stdout=output, stderr=subprocess.STDOUT)
    checks.append({'command': command, 'exit_code': result.returncode,
                   'elapsed_seconds': time.monotonic() - started, 'log': log, 'log_sha256': sha(OUT / log)})
    (OUT / 'checks.json').write_text(json.dumps(checks, indent=2) + '\n')
    assert result.returncode == 0, (OUT / log).read_text()
    print(command, 'PASS', flush=True)

for name, expected in unchanged.items():
    assert sha(PROJECT / name) == expected
for name, expected in freeze['source_files'].items():
    assert sha(REPO / name) == expected
record = {
    'result': 'PASS: Linux candidate metadata packaging; actual Linux verification pending',
    'created_utc': datetime.now(timezone.utc).isoformat(),
    'head': capture(['git', 'rev-parse', 'HEAD']),
    'origin_main': capture(['git', 'rev-parse', 'origin/main']),
    'upstream_main_at_check': capture(['git', 'rev-parse', 'nla-upstream/main']),
    'proof_freeze_sha256': FREEZE_SHA,
    'unchanged_73_nonREADME_frozen_project_inputs': unchanged,
    'unchanged_4_original_source_inputs': freeze['source_files'],
    'unchanged_four_review_reports': before['report_sha256'],
    'historical_README_sha256': sha(OUT / 'frozen-statement-stage-README.md'),
    'current_README_sha256': sha(PROJECT / 'README.md'),
    'formalization_yaml_sha256': sha(PROJECT / 'formalization.yaml'),
    'export_names': config['theorem_names'],
    'definition_exceptions': config['definition_names'],
    'permitted_axioms': config['permitted_axioms'],
    'canonical_status': 'Solved',
    'unchanged_canonical_pages': 217,
    'unchanged_registry_entries': 217,
    'registry_sha256': before['problem_ids_sha256'],
    'unchanged_tracked_repository_tree': True,
    'clean_dependency_pins': 10,
    'no_further_mathematical_build_needed_or_claimed_for_metadata_edits': True,
    'actual_Linux_Comparator': 'pending',
    'formal_recurrence': 'm! H(m)^2 ≤ H(2m)',
    'unexported_stronger_source_recurrence': '(2m−1)!! H(m)^2 ≤ H(2m)',
    'LeanCert_scope': 'Actual kernel trust auditing of exact proof; no numerical interval certificate',
    'name_and_department': {'name': 'George Stepaniants', 'affiliation': affiliation},
    'new_email_addresses': [],
    'no_commit_push_PR_or_status_change_by_preparer': True,
}
(OUT / 'packaging-record.json').write_text(json.dumps(record, indent=2) + '\n')
print('PASS: all frozen mathematics/configuration/pins/reviews and 217 canonical pages preserved.')
