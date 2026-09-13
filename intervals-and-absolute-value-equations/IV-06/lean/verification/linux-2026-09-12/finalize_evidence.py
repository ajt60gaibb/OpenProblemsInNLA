"""Seal accepted IV-06 evidence, then retain it without modifying candidate inputs."""
from pathlib import Path
import hashlib,json,shutil,subprocess
out=Path(__file__).resolve().parent
cfg=json.loads((out/'run-config.json').read_text())
project=Path('/tmp/nla-lean-iv06-worktree')/cfg['project']
target=project/'verification/linux-2026-09-12'
assert not target.exists(), 'Do not overwrite a retained operational audit'
assert json.loads((out/'identity-verification.json').read_text())['overall_run_success_observed']
assert json.loads((out/'control-verification.json').read_text())['result']=='PASS'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
outer=out/'EVIDENCE-MANIFEST.json'
files=sorted(p for p in out.rglob('*') if p.is_file() and p!=outer)
report=out/'OPERATIONAL-REVIEW.md'
assert report in files
report.write_text(report.read_text().replace('@BOUND_COUNT@',str(len(files))).replace('@TOTAL_COUNT@',str(len(files)+1)))
outer.write_text(json.dumps({'scope':'Complete independent IV-06 actual Linux operational evidence; all nested manifests retained, only this exact outer manifest excluded from its own inventory.',
 'commit':cfg['commit'],'run':cfg['run'],'file_count':len(files),
 'files':{p.relative_to(out).as_posix():{'bytes':p.stat().st_size,'sha256':sha(p)} for p in files}},indent=2)+'\n')
subprocess.run(['python3',str(out/'verify_evidence.py')],check=True)
receipt=json.loads(next((out/'artifacts/lean-IV-06').glob('verify-*/result.json')).read_text())
for rel,expected in receipt['input_sha256'].items():assert sha(project/rel)==expected,rel
shutil.copytree(out,target)
subprocess.run(['python3',str(target/'verify_evidence.py')],check=True)
for rel,expected in receipt['input_sha256'].items():assert sha(project/rel)==expected,rel
print(json.dumps({'report_sha256':sha(report),'manifest_sha256':sha(outer),'bound_files':len(files),
 'total_files':len(files)+1,'all_verified_candidate_inputs_preserved':len(receipt['input_sha256']),
 'retained_path':str(target)},indent=2))
