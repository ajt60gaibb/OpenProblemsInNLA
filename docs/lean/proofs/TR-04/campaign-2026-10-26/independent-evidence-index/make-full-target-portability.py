#!/usr/bin/env python3
"""Bind the final integrity extension and its retained preparation diagnostic."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json
B=Path(__file__).resolve().parent
REPO=B.parents[5]
def sha(p):
    assert p.is_file() and not p.is_symlink(),str(p)
    return hashlib.sha256(p.read_bytes()).hexdigest()
p=B/'result-through-full-target-v2.json'
assert sha(p)=='6f7b795d432b495f0949c7f6d77c02e4ab3f2f62c89cff227955e9642c918b8e'
index=json.loads(p.read_text())
assert index['passed'] and index['approved_scopes']==42 and not index['authoritative_Linux_Comparator']
artifacts=dict(index['artifact_hashes'])
for path,digest in artifacts.items():assert sha(REPO/path)==digest
names=['result-through-full-target-v2.json','check-evidence-through-full-target.py',
       'check-evidence-through-full-target-attempt-1.py','full-target-index-preparation-diagnostic.json',
       'result-through-full-target-historical-recheck.json','make-full-target-portability.py']
for name in names:artifacts[str((B/name).relative_to(REPO))]=sha(B/name)
diag=json.loads((B/'full-target-index-preparation-diagnostic.json').read_text())
assert diag['passed'] is False and diag['accepted_as_mathematical_or_CI_result'] is False
first=json.loads((B/'result-through-full-target-historical-recheck.json').read_text())
assert first['passed'] and first['approved_scopes']==35
out={'passed':True,'type':'portable_artifact_staging_integrity_only',
     'recorded_utc':datetime.now(timezone.utc).isoformat(),
     'primary_full_Target_integrity_index':{'path':str(p.relative_to(REPO)),'sha256':sha(p)},
     'full_index_approved_scopes':42,'artifact_hashes':artifacts,
     'retained_preparation_failure_accepted_as_proof':False,
     'retained_preparation_failure':'Relative output path serialization only; unchanged historical integrity checker had passed. No proof source, consumer, kernel guard, Lean outcome or historical receipt was changed.',
     'compiled_objects_or_symlinks_in_artifact_set':False,'fresh_Lean_replayed_by_this_check':False,
     'authoritative_Linux_Comparator':False,
     'staging_note':'Use the exact artifact_hashes set plus this sidecar. It includes prior immutable receipts and new full-Target evidence, logs, sources and diagnostics, with no compiled project objects. Existing tracked canonical/shared inputs need no changes.'}
q=B/'full-target-index-portability-review.json'
assert not q.exists()
q.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':True,'bound_artifacts':len(artifacts),'sha256':sha(q)},indent=2))
