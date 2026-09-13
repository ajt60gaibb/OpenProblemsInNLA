"""Retain the original whole-run archive after actual complete success."""
from pathlib import Path,PurePosixPath
import hashlib,json,subprocess,zipfile
O=Path(__file__).resolve().parent
C=json.loads((O/'context.json').read_text())
S=O/'retrieval/selected'
run=json.loads((S/'run.json').read_text())
jobs=json.loads((S/'jobs.json').read_text())
assert run['id']==C['run'] and run['head_sha']==C['commit']
assert run['status']=='completed' and run['conclusion']=='success'
assert len(jobs['jobs'])==jobs['total_count']==17
assert all(j['status']=='completed' and j['conclusion']=='success' for j in jobs['jobs'])
assert all(s['status']=='completed' and s['conclusion']=='success' for j in jobs['jobs'] for s in j['steps'])
zpath=O/'run-logs.zip'
if not zpath.exists():
    command=['/tmp/nla-submission-tools/gh_2.100.0_macOS_arm64/bin/gh','api','--allow-escape-sequences',
      f"repos/{C['repository']}/actions/runs/{C['run']}/logs"]
    r=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=45)
    if r.returncode:
        (O/'final-api-error.log').write_bytes(r.stderr)
        raise RuntimeError('Whole-run log read failed; raw stderr retained')
    zpath.write_bytes(r.stdout)
sha=lambda b:hashlib.sha256(b).hexdigest()
entries={};associations={}
with zipfile.ZipFile(zpath) as z:
    assert z.testzip() is None and len(z.namelist())==len(set(z.namelist()))
    for item in z.infolist():
        n=PurePosixPath(item.filename)
        assert not n.is_absolute() and '..' not in n.parts
        assert (item.external_attr>>16)&0o170000!=0o120000
        if item.is_dir():continue
        b=z.read(item);entries[item.filename]={'sha256':sha(b),'bytes':len(b)}
    full=[n for n in entries if '/' not in n]
    assert len(full)==len(jobs['jobs'])
    for job in jobs['jobs']:
        if job['name'] not in ['select','checker-controls'] and not job['name'].startswith(f"verify ({C['problem']},"):continue
        candidates=[n for n in full if n.endswith('_'+job['name'].replace('/','_')+'.txt')]
        if not candidates:
            candidates=[n for n in full if (C['problem'] in n if job['name'].startswith('verify (') else n.endswith('_'+job['name']+'.txt'))]
        assert len(candidates)==1,(job['name'],candidates)
        assert z.read(candidates[0])==(O/f"job-{job['id']}.log").read_bytes()
        associations[str(job['id'])]=candidates[0]
result={'result':'PASS original complete successful-run identity and archive checks',
 'candidate':C['commit'],'run':C['run'],'whole_run_status':'completed','whole_run_conclusion':'success',
 'all_jobs_and_steps_successful':True,'whole_job_count':len(jobs['jobs']),'archive_file_count':len(entries),
 'archive_sha256':sha(zpath.read_bytes()),'archive_bytes':zpath.stat().st_size,
 'source':f"https://api.github.com/repos/{C['repository']}/actions/runs/{C['run']}/logs",
 'digest_scope':'Locally recorded SHA of authenticated original download; no GitHub-published checksum claimed for the run-log ZIP.',
 'selected_authenticated_job_logs_identical_to_original_archive_entries':associations,'entries':entries}
(O/'whole-run-verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['result','whole_job_count','archive_file_count','archive_bytes','archive_sha256']}))
