#!/usr/bin/env python3
"""Independent read-only original GitHub API/log/ZIP collection, no proof execution."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import datetime,gzip,hashlib,json,subprocess

ROOT=Path(__file__).resolve().parent
REPOSITORY='ajt60gaibb/OpenProblemsInNLA'
RUN=40415515989
JOB=121897153349
HEAD='0c6d346763a932eb2d379f555e66d8ab3dbf3255'
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
dest=ROOT/'collection'/stamp;dest.mkdir(parents=True)
prefix='repos/'+REPOSITORY
def api(s):return subprocess.check_output(['gh','api','--allow-escape-sequences',prefix+s])
queries={'run.json':f'/actions/runs/{RUN}','jobs.json':f'/actions/runs/{RUN}/jobs?per_page=100','artifacts.json':f'/actions/runs/{RUN}/artifacts?per_page=100','pr.json':'/pulls/371'}
with ThreadPoolExecutor(max_workers=4) as pool:data=dict(zip(queries,pool.map(api,queries.values())))
for n,b in data.items():(dest/n).write_bytes(b)
run,jobs,arts=(json.loads(data[n]) for n in ['run.json','jobs.json','artifacts.json'])
assert run['id']==RUN and run['head_sha']==HEAD and run['head_commit']['id']==HEAD
assert jobs['total_count']<=100 and arts['total_count']<=100
job=next(j for j in jobs['jobs'] if j['id']==JOB)
summary=dict(role='Independent collector /root/re06_counts/inverse_outer_crosscheck',run=RUN,job=JOB,head=HEAD,status=run['status'],conclusion=run['conclusion'],job_status=job['status'],job_conclusion=job['conclusion'],timestamp=stamp,terminal=False,network='Actual GitHub REST API via authenticated gh; originals retained byte-for-byte',no_Lean_or_Comparator_execution=True)
if run['status']=='completed':
    raw=api(f'/actions/jobs/{JOB}/logs');(dest/'job.log').write_bytes(raw);(dest/'job.log.gz').write_bytes(gzip.compress(raw,mtime=0))
    candidates=[a for a in arts['artifacts'] if a['name']=='lean-RE-06'];assert len(candidates)==1
    art=candidates[0];z=api(f'/actions/artifacts/{art["id"]}/zip');(dest/'original-artifact.zip').write_bytes(z)
    assert hashlib.sha256(z).hexdigest()==art['digest'].removeprefix('sha256:') and len(z)==art['size_in_bytes']
    (dest/'artifact-metadata.json').write_text(json.dumps(art,indent=2)+'\n')
    summary.update(terminal=True,artifact_id=art['id'],artifact_sha256=hashlib.sha256(z).hexdigest(),artifact_bytes=len(z),raw_log_sha256=hashlib.sha256(raw).hexdigest(),raw_log_bytes=len(raw))
(dest/'COLLECTION.json').write_text(json.dumps(summary,indent=2)+'\n')
(ROOT/'LATEST_COLLECTION.json').write_text(json.dumps(dict(directory=str(dest),**summary),indent=2)+'\n')
print(json.dumps(summary,indent=2))
