"""Seal the MI-23 independent operational evidence without omitting nested manifests.
Only the exact outer output manifest is excluded from its own digest list.
"""
from pathlib import Path
import datetime
import hashlib
import json

OUT = Path(__file__).resolve().parent
TARGET = OUT / 'EVIDENCE-MANIFEST.json'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


run = json.loads((OUT / 'run-metadata.json').read_text())
assert run['status'] == 'completed' and run['conclusion'] == 'success'
assert run['head_sha'] == '17194f9060609acae429e14d3dc3c4562b84f2bd'
result = json.loads((OUT / 'identity-verification.json').read_text())
assert result['overall_run_success_observed']
assert result['complete_tracked_source_set_count'] == 133
files = {str(path.relative_to(OUT)): {'sha256': sha(path), 'bytes': path.stat().st_size}
         for path in sorted(OUT.rglob('*')) if path.is_file() and path != TARGET}
nested = [name for name in files if Path(name).name.casefold() == 'evidence-manifest.json']
assert nested and all('/' in name for name in nested)
manifest = {'verdict': 'PASS', 'reviewer': '/root/leancert_examples',
    'date_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'run': run['id'], 'commit': run['head_sha'],
    'scope': 'Original remote Linux MI-23 operational evidence; no new local Linux execution',
    'file_count': len(files), 'nested_manifests_included': nested,
    'excluded_exact_self_path': 'EVIDENCE-MANIFEST.json', 'files': files}
TARGET.write_text(json.dumps(manifest, indent=2) + '\n')
# Check the complete set and every digest, including nested manifests.
actual = {str(path.relative_to(OUT)) for path in OUT.rglob('*')
          if path.is_file() and path != TARGET}
assert set(files) == actual
for name, entry in files.items():
    assert sha(OUT / name) == entry['sha256']
print('PASS:', len(files), 'files,', len(nested), 'nested manifests retained')
print('Operational report SHA256:', sha(OUT / 'OPERATIONAL-REVIEW.md'))
print('Evidence manifest SHA256:', sha(TARGET))
