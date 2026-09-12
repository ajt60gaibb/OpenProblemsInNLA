"""Read-only retrieval for the independent MI-23 operational audit.

Adapted from the MI-26 retrieval by the campaign. Requires the entire run
and every recorded job/step to have succeeded. Retrieval is not a semantic or
operational approval; the independent reviewer must inspect the actual logs.
"""
from pathlib import Path, PurePosixPath
import hashlib
import json
import subprocess
import zipfile

OUT = Path(__file__).resolve().parent
GH = '/tmp/nla-submission-tools/gh_2.100.0_macOS_arm64/bin/gh'
REPO = 'sgstepaniants/OpenProblemsInNLA'
RUN = 34716784038
COMMIT = '17194f9060609acae429e14d3dc3c4562b84f2bd'


def api(path):
    # Preserve the original job-log bytes (including ANSI escapes) in files;
    # these bytes are never emitted directly to a terminal by this script.
    return subprocess.check_output([GH, 'api', '--allow-escape-sequences',
                                    f'repos/{REPO}/{path}'])


def retain(name, data):
    (OUT / name).write_bytes(data)


run_raw = api(f'actions/runs/{RUN}')
run = json.loads(run_raw)
assert run['id'] == RUN and run['head_sha'] == COMMIT
assert run['status'] == 'completed' and run['conclusion'] == 'success'
retain('run-metadata.json', run_raw)
jobs_raw = api(f'actions/runs/{RUN}/jobs?per_page=100')
jobs = json.loads(jobs_raw)['jobs']
assert all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs)
assert all(s['status'] == 'completed' and s['conclusion'] == 'success' for j in jobs for s in j['steps'])
retain('jobs.json', jobs_raw)
selected_jobs = [j for j in jobs if j['name'] in ['select', 'checker-controls']
                 or j['name'].startswith('verify (MI-23,')]
assert len(selected_jobs) == 3
for job in selected_jobs:
    assert job['status'] == 'completed' and job['conclusion'] == 'success'
    assert all(s['status'] == 'completed' and s['conclusion'] == 'success'
               for s in job['steps'])
    retain(f"job-{job['id']}.log", api(f"actions/jobs/{job['id']}/logs"))
metadata_raw = api(f'actions/runs/{RUN}/artifacts?per_page=100')
metadata = json.loads(metadata_raw)
retain('artifact-metadata.json', metadata_raw)
selected = [a for a in metadata['artifacts'] if a['name'] in
            ['lean-MI-23', 'lean-checker-controls']]
assert {a['name'] for a in selected} == {'lean-MI-23', 'lean-checker-controls'}
assert len(selected) == 2
records = []
for a in selected:
    assert a['workflow_run']['head_sha'] == COMMIT and not a['expired']
    archive = api(f"actions/artifacts/{a['id']}/zip")
    digest = hashlib.sha256(archive).hexdigest()
    assert a['digest'] == 'sha256:' + digest
    zpath = OUT / (a['name'] + '.zip')
    zpath.write_bytes(archive)
    target = OUT / 'artifacts' / a['name']
    with zipfile.ZipFile(zpath) as z:
        for item in z.infolist():
            path = PurePosixPath(item.filename)
            assert not path.is_absolute() and '..' not in path.parts
            assert (item.external_attr >> 16) & 0o170000 != 0o120000
            if item.is_dir():
                continue
            q = target / path
            q.parent.mkdir(parents=True, exist_ok=True)
            data = z.read(item)
            if q.exists():
                assert q.read_bytes() == data
            else:
                q.write_bytes(data)
    records.append({'name': a['name'], 'id': a['id'], 'sha256': digest})
(OUT / 'FETCH-IDENTITY.json').write_text(json.dumps({
    'run': RUN, 'commit': COMMIT, 'run_status_at_fetch': run['status'],
    'run_conclusion_at_fetch': run['conclusion'],
    'successful_selected_jobs': [{k: j[k] for k in ['id', 'name', 'conclusion']}
                                 for j in selected_jobs],
    'archives': records,
    'scope': 'Original artifact retrieval and job identity only. Independent raw-log review required.'
}, indent=2) + '\n')
print(json.dumps({'run_status': run['status'], 'run_conclusion': run['conclusion'],
                  'downloaded_archives': records}, indent=2))
