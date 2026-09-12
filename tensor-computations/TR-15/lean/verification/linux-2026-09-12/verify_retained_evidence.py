"""Verify the complete retained operational evidence without network or writes."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent
manifest_path = root / 'EVIDENCE-MANIFEST.json'
manifest = json.loads(manifest_path.read_text())
actual = {str(p.relative_to(root)): p for p in root.rglob('*')
          if p.is_file() and p != manifest_path}
assert set(actual) == set(manifest['files']), (
    sorted(set(actual) - set(manifest['files'])),
    sorted(set(manifest['files']) - set(actual)))
for name, file in actual.items():
    data = file.read_bytes()
    expected = manifest['files'][name]
    assert len(data) == expected['bytes'], name
    assert hashlib.sha256(data).hexdigest() == expected['sha256'], name
nested = [name for name in actual if name.endswith('/EVIDENCE-MANIFEST.json')]
assert nested, 'The original project contains a nested packaging manifest.'
print(f'PASS: {len(actual)} retained files, including {len(nested)} nested outer-name manifests; '
      'only the actual outer manifest is excluded.')
