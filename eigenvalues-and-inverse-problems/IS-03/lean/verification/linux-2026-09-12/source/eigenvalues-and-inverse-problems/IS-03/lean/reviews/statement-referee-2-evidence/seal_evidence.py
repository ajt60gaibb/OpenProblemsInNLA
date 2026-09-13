"""Seal referee 2's report and its complete local evidence after successful checks."""
from pathlib import Path
import datetime, hashlib, json

root = Path(__file__).resolve().parent
manifest_path = root/'EVIDENCE-MANIFEST.json'
assert json.loads((root/'fresh-result.json').read_text())['result'] == 'PASS'
assert json.loads((root/'reconstruction.json').read_text())['result'] == 'PASS'
assert json.loads((root/'integrity-after.json').read_text())['result'] == 'PASS'
paths = {p.relative_to(root).as_posix(): p for p in root.rglob('*')
         if p.is_file() and p != manifest_path}
paths['../statement-referee-2.md'] = root/'../statement-referee-2.md'
assert not any(p.is_symlink() for p in paths.values())
files = {name: {'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                'bytes': path.stat().st_size} for name, path in sorted(paths.items())}
manifest = {
    'reviewer': '/root/formal_review_standards', 'phase': 'independent statement referee 2',
    'verdict': 'APPROVE statements only',
    'sealed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'statement_freeze_sha256': '588196a54decb127a814dc4860621505d6874a077295f3e30a782d7f28b8ac6c',
    'file_count': len(files), 'files': files,
    'inventory_rule': 'All files below this evidence directory, including nested files, plus the report. Exclude only this exact outer manifest from its own inventory.',
    'limitations': 'Statement checks and definition trust only. No target proof or scalar certificate, fresh dependency build, Linux Comparator, publication or external human review.'}
manifest_path.write_text(json.dumps(manifest, indent=2)+'\n')
for name, path in [('report', root/'../statement-referee-2.md'), ('manifest', manifest_path)]:
    print(name, hashlib.sha256(path.read_bytes()).hexdigest())
print('bound files', len(files))
