"""Seal only this reviewer's evidence; preserve all author and other-reviewer bytes."""
from pathlib import Path
import datetime,hashlib,json,subprocess
out=Path(__file__).resolve().parent;project=out.parents[1];repo=project.parents[2]
subprocess.run(['python3',str(out/'final_audit.py')],check=True)
record=json.loads((out/'final-integrity.json').read_text());assert record['result']=='PASS'
report=out.parent/'proof-referee-2.md'
assert 'Verdict: APPROVE' in report.read_text()
outer=out/'EVIDENCE-MANIFEST.json'
files={str(p.relative_to(out)):p for p in out.rglob('*') if p.is_file() and p!=outer}
files['../proof-referee-2.md']=report
for n,p in files.items():assert not p.is_symlink(),n
manifest={'kind':'Independent IS-03 final proof referee 2 evidence','verdict':'APPROVE',
 'reviewer':'formal_review_standards, independent AI agent; prior statement referee, not proof implementer',
 'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'root':'reviews/proof-referee-2-evidence','self_exclusion_only':'EVIDENCE-MANIFEST.json',
 'proof_freeze_sha256':'636cdb024f5b73ea61edd518de39ee192a604987aad2b9914c4d7e7eeab672e4',
 'bound_file_count':len(files),'files':{n:{'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for n,p in sorted(files.items())},
 'scope':'Full independent mathematical/source review and fresh macOS elaboration/actual-term/kernel checks, with complete original target preserved. Linux Comparator/default-kernel run still pending.'}
outer.write_text(json.dumps(manifest,indent=2)+'\n')
subprocess.run(['python3',str(out/'verify_evidence.py')],check=True)
print(json.dumps({'report_sha256':hashlib.sha256(report.read_bytes()).hexdigest(),'evidence_manifest_sha256':hashlib.sha256(outer.read_bytes()).hexdigest(),'bound_files':len(files),'total_with_outer_manifest':len(files)+1},indent=2))
