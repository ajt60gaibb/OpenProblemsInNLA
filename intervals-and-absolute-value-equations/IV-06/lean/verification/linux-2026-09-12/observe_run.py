"""Retain a dated read-only status observation; never infer operational approval."""
from pathlib import Path
import datetime,json,subprocess

out=Path(__file__).resolve().parent
config=json.loads((out/'run-config.json').read_text())
gh='/tmp/nla-submission-tools/gh_2.100.0_macOS_arm64/bin/gh'
prefix='repos/sgstepaniants/OpenProblemsInNLA/'
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
target=out/'observations'/stamp;target.mkdir(parents=True,exist_ok=False)
def api(path):return subprocess.check_output([gh,'api',prefix+path])
raw=api(f"actions/runs/{config['run']}"); run=json.loads(raw)
assert run['head_sha']==config['commit'] and run['id']==config['run']
(target/'run.json').write_bytes(raw)
raw=api(f"actions/runs/{config['run']}/jobs?per_page=100");record=json.loads(raw)
assert len(record['jobs'])==record['total_count']
(target/'jobs.json').write_bytes(raw)
print(json.dumps({'run':run['id'],'commit':run['head_sha'],'status':run['status'],
 'conclusion':run['conclusion'],'jobs':[{k:j[k] for k in ['id','name','status','conclusion']}
                                      for j in record['jobs']],
 'scope':'Status observation only; operational review remains pending'},indent=2))
