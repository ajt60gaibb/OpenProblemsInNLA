"""Retain actual IE-23 Linux evidence only after observed complete run success.

Adapted from the MI-03 retrieval driver by /root/formal_review_standards,
itself adapted from /root/solved_statement_inventory's MI-26 driver.
Retrieval and digest checks do not themselves issue an operational verdict.
"""
from pathlib import Path, PurePosixPath
import hashlib
import json
import subprocess
import zipfile

OUT = Path(__file__).resolve().parent
CTX = json.loads((OUT / 'context.json').read_text())
GH = '/tmp/nla-submission-tools/gh_2.100.0_macOS_arm64/bin/gh'
REPO, RUN, COMMIT = CTX['repository'], CTX['run'], CTX['commit']
PROBLEM = CTX['problem']

def api(path):
    # Keep original ANSI job-log bytes in files, never emit them to a terminal.
    return subprocess.check_output([GH, 'api', '--allow-escape-sequences',
                                    f'repos/{REPO}/{path}'])

def retain(name, data):
    (OUT / name).write_bytes(data)

def paginated(path, key, filename):
    pages, values, number = [], [], 1
    while True:
        raw = api(path + f'?per_page=100&page={number}')
        value = json.loads(raw)
        retain(f'{filename.removesuffix(".json")}-page-{number}.json', raw)
        pages.append(value)
        values.extend(value[key])
        if len(values) >= value['total_count']:
            break
        assert value[key], 'Nonprogressing GitHub pagination'
        number += 1
    assert len(values) == pages[-1]['total_count']
    assert len({x['id'] for x in values}) == len(values)
    combined = {'total_count': len(values), key: values,
                'source_pages': len(pages), 'pagination_reconstructed': True}
    retain(filename, (json.dumps(combined, indent=2) + '\n').encode())
    return values

run_raw = api(f'actions/runs/{RUN}')
run = json.loads(run_raw)
assert run['id'] == RUN and run['head_sha'] == COMMIT
assert run['status'] == 'completed' and run['conclusion'] == 'success'
retain('run-metadata.json', run_raw)
retain('run-logs.zip', api(f'actions/runs/{RUN}/logs'))
jobs = paginated(f'actions/runs/{RUN}/jobs', 'jobs', 'jobs.json')
assert all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs)
assert all(s['status'] == 'completed' and s['conclusion'] == 'success'
           for j in jobs for s in j['steps'])
selected_jobs = [j for j in jobs if j['name'] in ['select', 'checker-controls']
                 or j['name'].startswith(f'verify ({PROBLEM},')]
assert len(selected_jobs) == 3
for job in selected_jobs:
    retain(f"job-{job['id']}.log", api(f"actions/jobs/{job['id']}/logs"))
artifacts = paginated(f'actions/runs/{RUN}/artifacts', 'artifacts', 'artifact-metadata.json')
selected = [a for a in artifacts if a['name'] in [f'lean-{PROBLEM}', 'lean-checker-controls']]
assert len(selected) == 2 and {a['name'] for a in selected} == {f'lean-{PROBLEM}', 'lean-checker-controls'}
records = []
for a in selected:
    assert a['workflow_run']['head_sha'] == COMMIT and not a['expired']
    zpath = OUT / (a['name'] + '.zip')
    archive = zpath.read_bytes() if zpath.exists() else api(f"actions/artifacts/{a['id']}/zip")
    digest = hashlib.sha256(archive).hexdigest()
    assert a['digest'] == 'sha256:' + digest
    if not zpath.exists():
        zpath.write_bytes(archive)
    target = OUT / 'artifacts' / a['name']
    with zipfile.ZipFile(zpath) as z:
        assert z.testzip() is None
        names = [f.filename for f in z.infolist()]
        assert len(names) == len(set(names))
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

idrun_raw = api(f"actions/runs/{CTX['permanent_id_run']}")
idrun = json.loads(idrun_raw)
assert idrun['head_sha'] == COMMIT and idrun['status'] == 'completed' and idrun['conclusion'] == 'success'
retain('permanent-id-run.json', idrun_raw)
idjobs = paginated(f"actions/runs/{CTX['permanent_id_run']}/jobs", 'jobs', 'permanent-id-jobs.json')
for j in idjobs:
    assert j['conclusion'] == 'success' and all(s['conclusion'] == 'success' for s in j['steps'])
    retain(f"permanent-id-job-{j['id']}.log", api(f"actions/jobs/{j['id']}/logs"))

retain('FETCH-IDENTITY.json', (json.dumps({
    'run': RUN, 'commit': COMMIT, 'run_status_at_fetch': run['status'],
    'run_conclusion_at_fetch': run['conclusion'], 'all_job_count': len(jobs),
    'successful_selected_jobs': [{k: j[k] for k in ['id', 'name', 'conclusion']} for j in selected_jobs],
    'archives': records,
    'scope': 'Original retrieval and identities only. Actual raw-log and source audit remains required.',
    'reviewer_role': CTX['role']}, indent=2) + '\n').encode())
print(json.dumps({'run_status': run['status'], 'run_conclusion': run['conclusion'],
                  'downloaded_archives': records}, indent=2))
