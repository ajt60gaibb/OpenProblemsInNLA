"""Verify this review's complete local evidence inventory, including nested files."""
from pathlib import Path
import hashlib, json

root = Path(__file__).resolve().parent
manifest_path = root/'EVIDENCE-MANIFEST.json'
manifest = json.loads(manifest_path.read_text())
actual = {p.relative_to(root).as_posix() for p in root.rglob('*')
          if p.is_file() and p != manifest_path}
actual.add('../statement-referee-2.md')
assert set(manifest['files']) == actual, 'incomplete or unexpected evidence inventory'
for rel, record in manifest['files'].items():
    assert rel == '../statement-referee-2.md' or '..' not in Path(rel).parts
    path = root/rel
    assert path.is_file() and not path.is_symlink(), rel
    assert path.stat().st_size == record['bytes'], rel
    assert hashlib.sha256(path.read_bytes()).hexdigest() == record['sha256'], rel
assert manifest['file_count'] == len(actual)
print(f'PASS: {len(actual)} bound report/evidence files; only the exact outer manifest is excluded from its own inventory')
