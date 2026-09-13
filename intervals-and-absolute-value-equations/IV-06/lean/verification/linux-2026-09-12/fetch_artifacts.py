"""Read-only original GitHub artifact retrieval for the independent IV-06 audit.

Adapted from the MI-03/MI-26 campaign retrieval. Requires a supplied exact
run-config.json and observed full-run success. Retrieval is not audit approval.
"""
from pathlib import Path, PurePosixPath
import hashlib, json, subprocess, zipfile

OUT = Path(__file__).resolve().parent
CONFIG = json.loads((OUT/'run-config.json').read_text())
GH = '/tmp/nla-submission-tools/gh_2.100.0_macOS_arm64/bin/gh'
REPO = 'sgstepaniants/OpenProblemsInNLA'
RUN, COMMIT = CONFIG['run'], CONFIG['commit']
assert CONFIG['problem'] == 'IV-06'

def api(path):
    return subprocess.check_output([GH, 'api', '--allow-escape-sequences',
                                    f'repos/{REPO}/{path}'])

def retain(name, data):
    path = OUT/name
    if path.exists():
        assert path.read_bytes() == data, 'Do not overwrite previously retained evidence: '+name
    else:
        path.write_bytes(data)

raw = api(f'actions/runs/{RUN}')
run = json.loads(raw)
assert run['id'] == RUN and run['head_sha'] == COMMIT
assert run['status'] == 'completed' and run['conclusion'] == 'success'
retain('run-metadata.json', raw)
retain('run-logs.zip', api(f'actions/runs/{RUN}/logs'))
raw = api(f'actions/runs/{RUN}/jobs?per_page=100')
jobs_record = json.loads(raw)
jobs = jobs_record['jobs']
assert len(jobs) == jobs_record['total_count'], 'Unexpected pagination: retain every page before continuing'
assert all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs)
retain('jobs.json', raw)
selected = [j for j in jobs if j['name'] in ['select', 'checker-controls']
            or j['name'].startswith('verify (IV-06,')]
assert len(selected) == 3
for job in selected:
    assert all(s['status'] == 'completed' and s['conclusion'] == 'success' for s in job['steps'])
    retain(f"job-{job['id']}.log", api(f"actions/jobs/{job['id']}/logs"))
raw = api(f'actions/runs/{RUN}/artifacts?per_page=100')
metadata = json.loads(raw)
assert len(metadata['artifacts']) == metadata['total_count'], 'Unexpected artifact pagination'
retain('artifact-metadata.json', raw)
artifacts = [a for a in metadata['artifacts'] if a['name'] in ['lean-IV-06', 'lean-checker-controls']]
assert len(artifacts) == 2 and {a['name'] for a in artifacts} == {'lean-IV-06', 'lean-checker-controls'}
records = []
for artifact in artifacts:
    assert artifact['workflow_run']['head_sha'] == COMMIT and not artifact['expired']
    path = OUT/(artifact['name']+'.zip')
    data = path.read_bytes() if path.exists() else api(f"actions/artifacts/{artifact['id']}/zip")
    digest = hashlib.sha256(data).hexdigest()
    assert artifact['digest'] == 'sha256:'+digest
    retain(path.name, data)
    target = OUT/'artifacts'/artifact['name']
    with zipfile.ZipFile(path) as archive:
        assert archive.testzip() is None
        regular = [item for item in archive.infolist() if not item.is_dir()]
        assert len({item.filename for item in regular}) == len(regular), 'duplicate ZIP entry'
        for item in regular:
            rel = PurePosixPath(item.filename)
            assert not rel.is_absolute() and '..' not in rel.parts
            assert (item.external_attr >> 16) & 0o170000 != 0o120000
            destination = target/rel
            destination.parent.mkdir(parents=True, exist_ok=True)
            content = archive.read(item)
            if destination.exists():
                assert destination.read_bytes() == content
            else:
                destination.write_bytes(content)
    records.append({'name': artifact['name'], 'id': artifact['id'], 'sha256': digest})
retain('FETCH-IDENTITY.json', (json.dumps({
    'run': RUN, 'commit': COMMIT, 'run_status_at_fetch': run['status'],
    'run_conclusion_at_fetch': run['conclusion'],
    'successful_selected_jobs': [{k:j[k] for k in ['id','name','conclusion']} for j in selected],
    'archives': records, 'scope': 'Original archive retrieval and job identity only; raw-log operational review remains required.'},
    indent=2)+'\n').encode())
print(json.dumps({'run': RUN, 'commit': COMMIT, 'observed_run_conclusion': run['conclusion'],
                  'downloaded_original_archives': records}, indent=2))
