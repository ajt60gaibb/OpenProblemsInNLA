from pathlib import Path
import datetime,json,subprocess
O=Path(__file__).resolve().parent
C=json.loads((O/'context.json').read_text())
GH='/tmp/nla-submission-tools/gh_2.100.0_macOS_arm64/bin/gh'
P=O/'polls'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
P.mkdir(parents=True,exist_ok=False)
for name,path in [('run',f"actions/runs/{C['run']}"),('jobs',f"actions/runs/{C['run']}/jobs?per_page=100"),('permanent-id-run',f"actions/runs/{C['permanent_id_run']}")]:
 r=subprocess.run([GH,'api','--allow-escape-sequences',f"repos/{C['repository']}/{path}"],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=40)
 (P/(name+'.json' if r.returncode==0 else name+'.error.log')).write_bytes(r.stdout if r.returncode==0 else r.stderr)
 assert r.returncode==0,(name,r.returncode)
 d=json.loads(r.stdout)
 if name=='jobs':print(json.dumps({'jobs':[{k:j[k] for k in ['id','name','status','conclusion']} for j in d['jobs']],'total':d['total_count']}))
 else:print(json.dumps({k:d[k] for k in ['id','head_sha','status','conclusion']}))
