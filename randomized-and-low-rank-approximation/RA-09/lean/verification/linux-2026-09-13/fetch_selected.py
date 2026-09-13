"""Retrieve completed selected Ubuntu jobs and their original artifacts once.

Derived from the retained IS03/campaign retrieval structure. Retrieval is not
operational acceptance. A still-running whole workflow is recorded honestly.
"""
from pathlib import Path,PurePosixPath
import datetime,hashlib,json,subprocess,zipfile
O=Path(__file__).resolve().parent
C=json.loads((O/'context.json').read_text())
GH='/tmp/nla-submission-tools/gh_2.100.0_macOS_arm64/bin/gh'
S=O/'retrieval/selected';S.mkdir(parents=True,exist_ok=True)
def sha(b):return hashlib.sha256(b).hexdigest()
def retain(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    if path.exists():assert path.read_bytes()==data,path
    else:path.write_bytes(data)
def api(endpoint,path):
    if path.exists():return path.read_bytes()
    r=subprocess.run([GH,'api','--allow-escape-sequences',f"repos/{C['repository']}/{endpoint}"],
      stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=45)
    if r.returncode:
        stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ')
        e=O/'api-errors'/stamp;e.mkdir(parents=True,exist_ok=False)
        retain(e/'stderr.log',r.stderr);retain(e/'stdout.log',r.stdout)
        retain(e/'command.json',(json.dumps({'command':r.args,'exit_code':r.returncode},indent=2)+'\n').encode())
        raise RuntimeError('GitHub read failed; raw error retained')
    retain(path,r.stdout);return r.stdout
def pages(endpoint,key,label):
    values=[];i=1
    while True:
        raw=api(endpoint+f'?per_page=100&page={i}',S/f'{label}-page-{i}.json')
        page=json.loads(raw);values+=page[key]
        if len(values)>=page['total_count']:break
        assert page[key];i+=1
    assert len(values)==page['total_count']==len({v['id'] for v in values})
    retain(S/(label+'.json'),(json.dumps({'total_count':len(values),key:values,'source_pages':i},indent=2)+'\n').encode())
    return values
run=json.loads(api(f"actions/runs/{C['run']}",S/'run.json'))
assert run['head_sha']==C['commit'] and run['id']==C['run']
jobs=pages(f"actions/runs/{C['run']}/jobs",'jobs','jobs')
selected=[j for j in jobs if j['name'] in ['select','checker-controls'] or j['name'].startswith(f"verify ({C['problem']},")]
assert len(selected)==3
for j in selected:
    assert j['status']=='completed' and j['conclusion']=='success'
    assert all(s['status']=='completed' and s['conclusion']=='success' for s in j['steps'])
    api(f"actions/jobs/{j['id']}/logs",O/f"job-{j['id']}.log")
artifacts=pages(f"actions/runs/{C['run']}/artifacts",'artifacts','artifacts')
chosen=[a for a in artifacts if a['name'] in [f"lean-{C['problem']}",'lean-checker-controls']]
assert len(chosen)==2
records=[]
for a in chosen:
    assert a['workflow_run']['head_sha']==C['commit'] and not a['expired']
    zpath=O/(a['name']+'.zip')
    data=api(f"actions/artifacts/{a['id']}/zip",zpath)
    assert a['digest']=='sha256:'+sha(data)
    target=O/'artifacts'/a['name'];entries={}
    with zipfile.ZipFile(zpath) as z:
        assert z.testzip() is None
        assert len(z.namelist())==len(set(z.namelist()))
        for item in z.infolist():
            name=PurePosixPath(item.filename)
            assert not name.is_absolute() and '..' not in name.parts
            assert (item.external_attr>>16)&0o170000!=0o120000
            if item.is_dir():continue
            b=z.read(item);retain(target/name,b)
            entries[item.filename]={'sha256':sha(b),'bytes':len(b)}
    actual={str(p.relative_to(target)) for p in target.rglob('*') if p.is_file()}
    assert actual==set(entries)
    records.append({'name':a['name'],'id':a['id'],'original_zip_sha256':sha(data),'zip_bytes':len(data),
      'metadata_digest':a['digest'],'file_count':len(entries),'extracted_files':entries})
idrun=json.loads(api(f"actions/runs/{C['permanent_id_run']}",S/'permanent-id-run.json'))
assert idrun['head_sha']==C['commit'] and idrun['status']=='completed' and idrun['conclusion']=='success'
idjobs=pages(f"actions/runs/{C['permanent_id_run']}/jobs",'jobs','permanent-id-jobs')
for j in idjobs:
    assert j['status']=='completed' and j['conclusion']=='success'
    assert all(s['status']=='completed' and s['conclusion']=='success' for s in j['steps'])
    api(f"actions/jobs/{j['id']}/logs",O/f"permanent-id-job-{j['id']}.log")
result={'phase':'Original completed selected-job retrieval only; no operational verdict',
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'run':C['run'],'candidate':C['commit'],
 'whole_run_status_observed':run['status'],'whole_run_conclusion_observed':run['conclusion'],
 'selected_jobs':[{'id':j['id'],'name':j['name'],'conclusion':j['conclusion']} for j in selected],
 'observed_job_count':len(jobs),'archives':records,'permanent_id_run':C['permanent_id_run'],
 'all_extracted_bytes_checked':True,'original_archives_retained':True,'operational_review_pending':True}
retain(O/'FETCH-SELECTED-IDENTITY.json',(json.dumps(result,indent=2)+'\n').encode())
print(json.dumps({'selected_jobs':'retrieved successful actual jobs','whole_run_status_at_fetch':run['status'],
 'artifact_archives':[{k:r[k] for k in ['name','id','zip_bytes','file_count']} for r in records]}))
