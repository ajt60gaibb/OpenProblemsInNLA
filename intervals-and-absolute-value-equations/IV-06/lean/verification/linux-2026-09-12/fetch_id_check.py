"""Retain the companion permanent-ID result at the exact supplied revision."""
from pathlib import Path
import json, subprocess

out = Path(__file__).resolve().parent
config = json.loads((out/'run-config.json').read_text())
gh = '/tmp/nla-submission-tools/gh_2.100.0_macOS_arm64/bin/gh'
prefix = 'repos/sgstepaniants/OpenProblemsInNLA/'
run_id, commit = config['permanent_id_run'], config['commit']
def api(path):
    return subprocess.check_output([gh, 'api', '--allow-escape-sequences', prefix+path])
raw = api(f'actions/runs/{run_id}')
run = json.loads(raw)
assert run['id'] == run_id and run['head_sha'] == commit
assert run['status'] == 'completed' and run['conclusion'] == 'success'
(out/'permanent-id-run.json').write_bytes(raw)
raw = api(f'actions/runs/{run_id}/jobs?per_page=100')
record = json.loads(raw)
jobs = record['jobs']
assert len(jobs) == record['total_count'] and jobs
assert all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs)
assert all(s['conclusion'] == 'success' for j in jobs for s in j['steps'])
(out/'permanent-id-jobs.json').write_bytes(raw)
for job in jobs:
    raw = api(f"actions/jobs/{job['id']}/logs")
    assert commit.encode() in raw and b'##[error]' not in raw
    (out/f"permanent-id-job-{job['id']}.log").write_bytes(raw)
print(json.dumps({'result': 'PASS', 'commit': commit, 'run': run_id,
                  'jobs': [{k:j[k] for k in ['id','name','conclusion']} for j in jobs]}))
