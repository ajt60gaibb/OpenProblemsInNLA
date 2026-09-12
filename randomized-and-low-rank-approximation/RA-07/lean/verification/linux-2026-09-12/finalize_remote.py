"""Read final run metadata after the completed relevant artifacts were retained.
Keep the first in-progress metadata separately and do not redownload passed ZIPs.
"""
from pathlib import Path
import json
import subprocess

OUT = Path(__file__).resolve().parent
GH = '/tmp/nla-submission-tools/gh_2.100.0_macOS_arm64/bin/gh'
API = 'repos/sgstepaniants/OpenProblemsInNLA/'
RUN = 34715563781
COMMIT = 'bf144a8ea84992d64f79f4425b18352843376286'

def api(path):
    return subprocess.check_output([GH, 'api', '--allow-escape-sequences', API + path])

run_raw = api(f'actions/runs/{RUN}')
run = json.loads(run_raw)
assert run['id'] == RUN and run['head_sha'] == COMMIT
assert run['status'] == 'completed' and run['conclusion'] == 'success'
jobs_raw = api(f'actions/runs/{RUN}/jobs?per_page=100')
jobs = json.loads(jobs_raw)['jobs']
assert len(jobs) == 7
assert all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs)
assert all(s['status'] == 'completed' and s['conclusion'] == 'success' for j in jobs for s in j['steps'])
metadata = api(f'actions/runs/{RUN}/artifacts?per_page=100')
first = {a['id']: a for a in json.loads((OUT / 'artifact-metadata.json').read_bytes())['artifacts']}
for a in json.loads(metadata)['artifacts']:
    if a['name'] in ['lean-RA-07', 'lean-checker-controls']:
        assert a['id'] in first and a['digest'] == first[a['id']]['digest']
(OUT / 'run-metadata.json').write_bytes(run_raw)
(OUT / 'jobs.json').write_bytes(jobs_raw)
(OUT / 'artifact-metadata-final.json').write_bytes(metadata)
print('PASS: final whole-run status SUCCESS; all seven jobs and their steps succeeded.')
