"""Reviewer-owned, read-only source inventory; normalize CRLF only, without trimming."""
import hashlib
import json
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
SOURCE = Path(__file__).resolve().parents[1] / 'submitted/NLA_partial_results_submission_package'
OUT = Path(__file__).resolve().parent / 'review-source-input-hashes.json'
records = []
for path in sorted(SOURCE.rglob('*')):
    if not path.is_file() or path.suffix not in {'.tex', '.cpp', '.py', '.json', '.txt', '.sh', '.md', '.log'}:
        continue
    raw = path.read_bytes()
    normalized = raw.decode('utf-8').replace('\r\n', '\n').encode('utf-8')
    records.append({'path': path.relative_to(SOURCE).as_posix(), 'raw_bytes': len(raw),
                    'normalized_bytes': len(normalized),
                    'raw_sha256': hashlib.sha256(raw).hexdigest(),
                    'utf8_lf_sha256': hashlib.sha256(normalized).hexdigest()})
OUT.write_text(json.dumps({'source_root': SOURCE.relative_to(REPO).as_posix(),
    'normalization': 'Decode complete bytes as UTF-8, replace CRLF with LF, encode UTF-8; no trimming, BOM removal, or other changes.',
    'files': records}, indent=2) + '\n', encoding='utf-8', newline='\n')
for record in records:
    if record['path'].endswith('.tex'):
        print(record['path'], record['utf8_lf_sha256'])
print(f'Inventoried {len(records)} files in {OUT}')
