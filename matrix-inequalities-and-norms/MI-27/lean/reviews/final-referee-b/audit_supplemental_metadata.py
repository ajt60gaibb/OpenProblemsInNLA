#!/usr/bin/env python3
"""Read-only MI27 metadata/provenance checks; creates private review copies only."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import shutil
import subprocess
import jsonschema

D = Path('/Users/georgestepaniants/Research/OpenProblemsInNLA/.local-recovery-20260918')
S = D / 'final-review-packets/MI27-v1'
P = D / 'development/MI27-publication-metadata-v1'
R = D / 'reviews/MI27-final-referee-b'
T = D / 'verification/MI27-type-preflight-118'
base = '71563f17926cd826a892c2bba0e294894ee57a5c'
def digest(data):
    return hashlib.sha256(data).hexdigest()
def sha(path):
    return digest(path.read_bytes())

delta = json.loads((P / 'PUBLICATION-CONFIG-DELTA.json').read_text())
assert sha(P / 'PUBLICATION-CONFIG-DELTA.json') == '0b405fd5db695ce98ae1210073e2e80a28973edb96db8d208117b62894769971'
assert delta['review_snapshot_sha256'] == sha(S / 'REVIEW-SNAPSHOT.json')
assert delta['before_sha256'] == sha(S / 'lake-manifest.json')
assert delta['after_sha256'] == sha(P / 'lake-manifest.json')
before = json.loads((S / 'lake-manifest.json').read_text())
after = json.loads((P / 'lake-manifest.json').read_text())
assert before['name'] == 'NLANR04' and after['name'] == 'NLAMI27'
before['name'] = 'NLAMI27'
assert before == after
assert 'package NLAMI27' in (S / 'lakefile.toml').read_text() or 'name = "NLAMI27"' in (S / 'lakefile.toml').read_text()

formalization = json.loads((P / 'formalization.yaml').read_text())
schema_path = S / 'source-context/standards/v0.4.schema.json'
jsonschema.validate(formalization, json.loads(schema_path.read_text()))
mapping = json.loads((P / 'IMPLEMENTATION-MAP.json').read_text())
audited = json.loads((R / 'SOURCE-AND-LOCAL-AUDIT.json').read_text())
cfg = json.loads((S / 'comparator.json').read_text())
assert mapping['snapshot_sha256'] == sha(S / 'REVIEW-SNAPSHOT.json')
assert [x['declaration'] for x in mapping['contracts']] == cfg['theorem_names']
assert mapping['contracts'] == formalization['status']['main_results']
for i, item in enumerate(mapping['contracts'], 1):
    assert item['contract'] == f'C{i:02d}'
    assert item['file'] == audited['contracts'][item['declaration']]['module'].replace('.', '/') + '.lean'
    assert item['sorry_count'] == 0
    assert set(item['axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
state = json.loads((P / 'STATE.json').read_text())
assert state['snapshot_sha256'] == sha(S / 'REVIEW-SNAPSHOT.json')
assert state['canonical_Lean_verified'] is False and state['count_increment'] == 0
assert formalization['status']['whole_problem_verified'] is False
assert formalization['status']['completed_original_targets'] == 0
assert formalization['verification']['GitHub_Comparator']['status'] == 'NOT_RUN'
assert formalization['verification']['local_aggregate']['receipt_sha256'] == sha(D / 'verification/MI27-local-20260919/LOCAL-REPLAY-AUDIT.json')
assert formalization['verification']['local_type_preflight']['audit_sha256'] == sha(T / 'AUDIT.json')
assert formalization['toolchain']['dependencies'] == {p['name']:p['rev'] for p in after['packages'] if p['name'] in {'mathlib','leancert'}}
assert formalization['alignment']['canonical_source_revision'] == base
assert formalization['alignment']['canonical_path'] == 'matrix-inequalities-and-norms/MI-27/README.md'
assert formalization['alignment']['extra_substantive_final_hypotheses'] is False
assert formalization['alignment']['definition_names'] == []
assert formalization['alignment']['final_declarations'] == ['NLA.MI27.logarithmic_commutator_bound']

mi24 = {}
for f in sorted((S / 'NLA/MI24').glob('*.lean')):
    base_path = 'matrix-inequalities-and-norms/MI-24/lean/NLA/MI24/' + f.name
    original = subprocess.check_output(['git', 'show', base + ':' + base_path], cwd=D.parent)
    assert original == f.read_bytes(), base_path
    mi24[str(f.relative_to(S))] = {'canonical_base_path':base_path, 'sha256':sha(f)}
assert len(mi24) == 7
assert (T / 'MI27SolutionTypes118.lean').read_text().replace('import Solution\n', 'import Challenge\n', 1) == (T / 'MI27ChallengeTypes118.lean').read_text()

copies = R / 'reviewed-publication-metadata'
copies.mkdir(exist_ok=True)
files = {}
for f in sorted(P.iterdir()):
    assert f.is_file() and not f.is_symlink()
    assert not re.search(r'[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}', f.read_text()), f.name
    shutil.copyfile(f, copies / f.name)
    files[f.name] = sha(f)
result = {
    'verdict':'PASS_READ_ONLY_METADATA_AND_PROVENANCE',
    'time':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'review_snapshot_sha256':sha(S / 'REVIEW-SNAPSHOT.json'),
    'metadata_files':files,
    'schema_sha256':sha(schema_path),
    'schema_validation':'PASS against frozen v0.4 schema',
    'configuration_delta':'Exactly top-level lake-manifest name NLANR04 to NLAMI27; all dependency entries and pins unchanged',
    'all20_contract_map_and_status_entries_match':True,
    'diagnostic_sources_differ_only_in_first_import':True,
    'reused_MI24_sources_equal_canonical_base':mi24,
    'metadata_email_scan':'No email-shaped strings in the six supplemental files',
    'GitHub_Comparator':'NOT_RUN',
    'compiler_invoked_by_reviewer':False,
}
(R / 'SUPPLEMENTAL-METADATA-AUDIT.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k:v for k,v in result.items() if k not in {'metadata_files','reused_MI24_sources_equal_canonical_base'}}, indent=2))
