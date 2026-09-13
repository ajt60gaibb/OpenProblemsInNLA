"""Retain completed standalone controls while the IV-06 project is still running.
This is not a project verification verdict. Original bytes can be reused later.
"""
from pathlib import Path,PurePosixPath
import hashlib,json,subprocess,zipfile

out=Path(__file__).resolve().parent
gh='/tmp/nla-submission-tools/gh_2.100.0_macOS_arm64/bin/gh'
repo='sgstepaniants/OpenProblemsInNLA'
configuration=json.loads((out/'run-config.json').read_text())
run_id=configuration['run']
commit=configuration['commit']
def api(path):return subprocess.check_output([gh,'api','--allow-escape-sequences',f'repos/{repo}/'+path])
run_raw=api(f'actions/runs/{run_id}')
run=json.loads(run_raw)
assert run['head_sha']==commit
(out/'initial-control-run-metadata.json').write_bytes(run_raw)
jobs_raw=api(f'actions/runs/{run_id}/jobs?per_page=100')
jobs=json.loads(jobs_raw)['jobs']
job=next(j for j in jobs if j['name']=='checker-controls')
assert job['status']=='completed' and job['conclusion']=='success'
assert all(s['status']=='completed' and s['conclusion']=='success' for s in job['steps'])
(out/'initial-control-jobs.json').write_bytes(jobs_raw)
(out/f"job-{job['id']}.log").write_bytes(api(f"actions/jobs/{job['id']}/logs"))
metadata_raw=api(f'actions/runs/{run_id}/artifacts?per_page=100')
(out/'initial-control-artifact-metadata.json').write_bytes(metadata_raw)
a=next(a for a in json.loads(metadata_raw)['artifacts'] if a['name']=='lean-checker-controls')
assert a['workflow_run']['head_sha']==commit and not a['expired']
archive=api(f"actions/artifacts/{a['id']}/zip")
assert a['digest']=='sha256:'+hashlib.sha256(archive).hexdigest()
path=out/'lean-checker-controls.zip';path.write_bytes(archive)
target=out/'artifacts/lean-checker-controls'
with zipfile.ZipFile(path) as z:
    assert z.testzip() is None
    for entry in z.infolist():
        rel=PurePosixPath(entry.filename)
        assert not rel.is_absolute() and '..' not in rel.parts
        assert (entry.external_attr>>16)&0o170000!=0o120000
        if entry.is_dir():continue
        p=target/rel;p.parent.mkdir(parents=True,exist_ok=True)
        p.write_bytes(z.read(entry))
print(json.dumps({'scope':'Completed standalone controls only; no IV-06 verdict','run_status_at_retrieval':run['status'],'job':job['id'],'artifact':a['id'],'sha256':hashlib.sha256(archive).hexdigest()}))
