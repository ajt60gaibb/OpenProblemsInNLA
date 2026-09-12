"""Hash the independent referee report and its retained evidence (no proof writes)."""
from pathlib import Path
import datetime
import hashlib
import json

folder = Path(__file__).resolve().parent
project = folder.parents[1]


def record(path):
    return {'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'bytes': path.stat().st_size}


freeze = json.loads((project / 'reviews/proof-freeze.json').read_text())
assert all(record(project / p) == r for p, r in freeze['files'].items())
report = project / 'reviews/proof-referee-1.md'
result = {
    'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'scope': 'Independent MI-23 local final proof referee 1 evidence; no Linux execution claim.',
    'report': {'path': str(report.relative_to(project)), **record(report)},
    'proof_freeze': record(project / 'reviews/proof-freeze.json'),
    'all_25_proof_freeze_inputs_unchanged': True,
    'files': {str(p.relative_to(folder)): record(p) for p in sorted(folder.rglob('*'))
              if p.is_file() and p.name != 'EVIDENCE-MANIFEST.json'},
}
manifest = folder / 'EVIDENCE-MANIFEST.json'
manifest.write_text(json.dumps(result, indent=2) + '\n')
print('Report SHA-256:', record(report)['sha256'])
print('Evidence manifest SHA-256:', record(manifest)['sha256'])
print('Evidence files:', len(result['files']))
