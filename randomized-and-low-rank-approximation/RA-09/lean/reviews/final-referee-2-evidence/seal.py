"""Seal all final mathematical referee2 evidence only after completed checks.
Includes nested manifests if any; excludes only this exact outer manifest.
"""
from pathlib import Path
import hashlib,json,datetime
E=Path(__file__).resolve().parent;P=E.parents[1]
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
audit=json.loads((E/'final-audit.json').read_text());assert audit['verdict']=='APPROVE'
assert sha(P/'verification/proof-freeze.json')==audit['proof_freeze_sha256']
manifest=E/'EVIDENCE-MANIFEST.json';assert not manifest.exists()
files=sorted(f for f in E.rglob('*') if f.is_file() and f!=manifest)
rows={str(f.relative_to(E)):{'sha256':sha(f),'bytes':f.stat().st_size} for f in files}
report=P/'reviews/final-referee-2.md';rows['../final-referee-2.md']={'sha256':sha(report),'bytes':report.stat().st_size}
j={'reviewer':'/root/mf16_final_referee','phase':'Independent final mathematical referee2',
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'verdict':'APPROVE complete frozen mathematics; actual Linux, metadata, operational and publication gates are separate',
 'proof_freeze_sha256':audit['proof_freeze_sha256'],'statement_freeze_sha256':audit['statement_freeze_sha256'],
 'internal_file_count':len(files),'file_count':len(rows),
 'inventory_rule':'Every actual internal file plus adjacent report. Only this exact outer EVIDENCE-MANIFEST.json is self-excluded; no blanket manifest, failed-attempt, log, source snapshot or nested-file exclusion.',
 'files':rows}
manifest.write_text(json.dumps(j,indent=2)+'\n')
print(json.dumps({'report_sha256':sha(report),'evidence_manifest_sha256':sha(manifest),'bound_files':len(rows)}))
