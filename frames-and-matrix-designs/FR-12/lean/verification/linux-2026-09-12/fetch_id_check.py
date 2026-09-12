"""Retain the companion permanent-ID CI result without rerunning it."""
from pathlib import Path
import hashlib, json, subprocess

out = Path(__file__).resolve().parent
gh = '/tmp/nla-submission-tools/gh_2.100.0_macOS_arm64/bin/gh'
prefix = 'repos/sgstepaniants/OpenProblemsInNLA/'
run_id = 34718277412
commit = '3e20bae9a07b1a33db8fdfb18bdebb9e590071a9'
def api(path):
    return subprocess.check_output([gh, 'api', '--allow-escape-sequences', prefix + path])
raw = api(f'actions/runs/{run_id}')
run = json.loads(raw)
assert run['id'] == run_id and run['head_sha'] == commit
assert run['status'] == 'completed' and run['conclusion'] == 'success'
(out / 'permanent-id-run.json').write_bytes(raw)
raw = api(f'actions/runs/{run_id}/jobs?per_page=100')
jobs = json.loads(raw)['jobs']
assert jobs and all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs)
assert all(s['conclusion'] == 'success' for j in jobs for s in j['steps'])
(out / 'permanent-id-jobs.json').write_bytes(raw)
for job in jobs:
    data = api(f"actions/jobs/{job['id']}/logs")
    assert commit.encode() in data and b'##[error]' not in data
    (out / f"permanent-id-job-{job['id']}.log").write_bytes(data)
print(json.dumps({'result': 'PASS', 'commit': commit, 'run': run_id,
                  'jobs': [{k: j[k] for k in ['id', 'name', 'conclusion']} for j in jobs]}))
