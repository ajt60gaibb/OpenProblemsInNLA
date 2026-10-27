#!/usr/bin/env python3
"""Independent original GitHub collection for final promoted source; no proof execution."""
import argparse,datetime,gzip,hashlib,json,re,subprocess
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
RUN=40419199614
JOB=121910097866
HEAD='669f3cd681b22882836d081a04652880ce39ba24'
REPOSITORY='ajt60gaibb/OpenProblemsInNLA'
def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
 stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ');dest=a.output/'collection'/stamp;dest.mkdir(parents=True)
 def api(s):return subprocess.check_output(['gh','api','--allow-escape-sequences','repos/'+REPOSITORY+s])
 queries={'run.json':f'/actions/runs/{RUN}','jobs.json':f'/actions/runs/{RUN}/jobs?per_page=100','artifacts.json':f'/actions/runs/{RUN}/artifacts?per_page=100','pr.json':'/pulls/371'}
 with ThreadPoolExecutor(max_workers=4) as pool:data=dict(zip(queries,pool.map(api,queries.values())))
 for n,b in data.items():(dest/n).write_bytes(b)
 run,jobs,arts=(json.loads(data[n]) for n in ['run.json','jobs.json','artifacts.json']);assert run['id']==RUN and run['head_sha']==run['head_commit']['id']==HEAD;assert jobs['total_count']<=100 and arts['total_count']<=100
 job=next(e for e in jobs['jobs'] if e['id']==JOB);assert job['head_sha']==HEAD and job['run_id']==RUN
 r={'reviewer':'/root/verification','independent_non_author':True,'run':RUN,'job':JOB,'source_head':HEAD,'status':run['status'],'conclusion':run['conclusion'],'job_status':job['status'],'job_conclusion':job['conclusion'],'run_attempt':run['run_attempt'],'timestamp':stamp,'terminal':False,'network':'Independent authenticated gh read-only GitHub REST; original API/ZIP/job endpoint bytes retained','local_Lean_or_Comparator_execution':False,'collector_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
 if run['status']=='completed':
  raw=api(f'/actions/jobs/{JOB}/logs');(dest/'job.log').write_bytes(raw);(dest/'job.log.gz').write_bytes(gzip.compress(raw,mtime=0))
  merges=re.findall(r'fetch[^\n]*\+([0-9a-f]{40}):refs/remotes/pull/371/merge',raw.decode('utf-8'));assert len(merges)==1;merge=merges[0];(dest/'executed-merge-metadata.json').write_bytes(api('/git/commits/'+merge));(dest/'source-head-metadata.json').write_bytes(api('/git/commits/'+HEAD));r['actually_executed_merge']=merge
  candidates=[e for e in arts['artifacts'] if e['name']=='lean-RE-06'];assert len(candidates)==1;art=candidates[0]
  z=api(f'/actions/artifacts/{art["id"]}/zip');(dest/'original-artifact.zip').write_bytes(z);assert hashlib.sha256(z).hexdigest()==art['digest'].removeprefix('sha256:') and len(z)==art['size_in_bytes'];(dest/'artifact-metadata.json').write_text(json.dumps(art,indent=2)+'\n')
  r.update(terminal=True,artifact_id=art['id'],artifact_sha256=hashlib.sha256(z).hexdigest(),artifact_bytes=len(z),raw_log_sha256=hashlib.sha256(raw).hexdigest(),raw_log_bytes=len(raw),derived_gzip='Lossless deterministic local gzip of exact original job endpoint bytes')
 (dest/'COLLECTION.json').write_text(json.dumps(r,indent=2)+'\n');(a.output/'LATEST_COLLECTION.json').write_text(json.dumps({'directory':str(dest),**r},indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
