#!/usr/bin/env python3
"""Read-only byte identity check for the integrated sealed TR26 package."""
import hashlib,json
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[6]
BASE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
freeze=ROOT/'docs/lean/proofs/TR-26/campaign-2026-10-26/PROMOTION_SOURCE_FREEZE.json'
d=json.loads(freeze.read_text());project=ROOT/'tensor-computations/TR-26/lean';expected=d['all_package_inputs']
actual={str(p.relative_to(project)) for p in project.rglob('*') if p.is_file() and '.lake' not in p.relative_to(project).parts}
assert actual==set(expected),(sorted(actual-set(expected)),sorted(set(expected)-actual))
for name,rec in expected.items():
 p=project/name
 assert not p.is_symlink() and p.stat().st_size==rec['bytes'] and sha(p)==rec['sha256'],name
r={'recorded_utc':datetime.now(timezone.utc).isoformat(),'passed':True,'scope':'Read-only live working-tree identity with all857 audited promotion/sealed canonical TR26 inputs; no fresh Lean/Linux/Comparator execution','canonical_inputs_verified':len(expected),'source_freeze_sha256':sha(freeze),'checker_sha256':sha(Path(__file__)),'unexpected_files':[],'changed_files':[]}
(BASE/'LIVE_PACKAGE_IDENTITY.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
