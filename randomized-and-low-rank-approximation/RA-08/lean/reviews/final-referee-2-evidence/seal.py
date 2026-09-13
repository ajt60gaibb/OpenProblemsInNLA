from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent
target=E/'EVIDENCE-MANIFEST.json'
assert not target.exists(),'Never overwrite a prior seal'
subprocess.run(['python3',str(E/'final_audit.py')],check=True)
files=sorted(p for p in E.rglob('*') if p.is_file() and p!=target)
rec={str(p.relative_to(E)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in files}
p=E.parent/'final-referee-2.md'
rec['../final-referee-2.md']={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
target.write_text(json.dumps({'reviewer':'/root/mf16_final_referee','phase':'Independent final mathematical review',
'verdict':'APPROVE complete frozen mathematics; Linux, metadata, operational and publication gates remain',
'proof_freeze_sha256':'ab05e2bf801e6906453e88a4d84d5e73191f776db05610fb8b8e5e4a03d4f856',
'internal_file_count':len(files),'file_count':len(rec),
'inventory_rule':'All internal files except only this exact outer manifest, plus the adjacent report. Nested manifests are included.',
'files':rec},indent=2)+'\n')
subprocess.run(['python3',str(E/'verify_evidence.py')],check=True)
