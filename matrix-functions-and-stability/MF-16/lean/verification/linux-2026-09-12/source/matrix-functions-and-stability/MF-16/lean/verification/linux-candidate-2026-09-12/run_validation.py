from pathlib import Path
import concurrent.futures,datetime,hashlib,json,os,subprocess,time
E=Path(__file__).resolve().parent;P=E.parents[1];W=P.parents[2]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
python='/tmp/nla-lean-formalization/venv/bin/python'
jobs=[('manifest',[python,'-B','tools/lean/validate_manifest.py',str(P.relative_to(W))]),
('permanent-ids',[python,'-B','tools/validate_problem_ids.py','--base-ref','origin/main'])]
def run(job):
 name,cmd=job;start=time.monotonic()
 r=subprocess.run(cmd,cwd=W,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 log=E/(name+'.log');log.write_bytes(r.stdout)
 return {'name':name,'command':cmd,'cwd':str(W),'exit_code':r.returncode,
 'seconds':time.monotonic()-start,'log':log.name,'log_sha256':sha(log)}
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:rows=list(pool.map(run,jobs))
record={'phase':'Actual metadata and permanent-ID checks only','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'reviewer':'/root/mf16_final_referee','commands':rows,'proof_or_dependency_build':False,
 'Linux_Comparator_run':False,'files':{f:sha(W/f) for f in
 ['tools/lean/validate_manifest.py','tools/validate_problem_ids.py','docs/lean/schema/v0.4.schema.json']}}
(E/'validation-checks.json').write_text(json.dumps(record,indent=2)+'\n')
for r in rows:
 print(r['name'],r['exit_code']);print((E/r['log']).read_text())
assert all(r['exit_code']==0 for r in rows)
