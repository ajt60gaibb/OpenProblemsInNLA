"""Verify this independent review's complete inventory, including its report."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent
outer = root / 'EVIDENCE-MANIFEST.json'
data = json.loads(outer.read_text())
internal = {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() and p != outer}
assert set(data['files']) == internal | {'../publication-referee-1.md'}
assert data['file_count'] == len(data['files'])
for rel, record in data['files'].items():
    path = root / rel
    assert not path.is_symlink()
    raw = path.read_bytes()
    assert len(raw) == record['bytes']
    assert hashlib.sha256(raw).hexdigest() == record['sha256'], rel
print(f"PASS: {len(data['files'])} review files, including the exact adjacent report; only the outer manifest itself excluded.")
