#!/usr/bin/env python3
"""Read-only GitHub Actions receipt collection; never runs Lean or Comparator."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import datetime
import gzip
import hashlib
import json
from pathlib import Path
import subprocess

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--repository', default='ajt60gaibb/OpenProblemsInNLA')
p.add_argument('--run', type=int, required=True)
p.add_argument('--pr', type=int, default=369)
p.add_argument('--head', required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
root = a.output.resolve() / ('run-' + str(a.run))
snapshot = root / 'snapshots' / stamp
snapshot.mkdir(parents=True, exist_ok=False)
api = 'repos/' + a.repository

def get(endpoint):
    return subprocess.check_output(['gh', 'api', '--allow-escape-sequences', api + endpoint])

endpoints = {'run.json': f'/actions/runs/{a.run}',
             'jobs.json': f'/actions/runs/{a.run}/jobs?per_page=100',
             'artifacts.json': f'/actions/runs/{a.run}/artifacts?per_page=100',
             'pr.json': f'/pulls/{a.pr}'}
with ThreadPoolExecutor(max_workers=4) as pool:
    data = dict(zip(endpoints, pool.map(get, endpoints.values())))
for name, body in data.items():
    (snapshot / name).write_bytes(body)
objects = {name: json.loads(body) for name, body in data.items()}
run, jobs, listing = (objects[n] for n in ['run.json', 'jobs.json', 'artifacts.json'])
assert run['id'] == a.run and run['head_sha'] == a.head
assert jobs['total_count'] <= 100 and listing['total_count'] <= 100
summary = {'collected_at_utc': stamp, 'repository': a.repository, 'run': a.run,
           'expected_head': a.head, 'event': run['event'], 'status': run['status'],
           'conclusion': run['conclusion'], 'snapshot': str(snapshot),
           'jobs': [{k: j.get(k) for k in ['id', 'name', 'status', 'conclusion']}
                    for j in jobs['jobs']], 'artifacts': listing['artifacts'],
           'scope': 'Independent non-author retrieval of actual GitHub Linux CI original bytes; no local Linux replay.'}
project_jobs = [j for j in jobs['jobs'] if j['name'] == 'verify (TR-26, tensor-computations/TR-26/lean)']
terminal = root / 'terminal'
if run['status'] == 'completed':
    terminal.mkdir(exist_ok=True)
    for name, body in data.items():
        dest = terminal / name
        if not dest.exists():
            dest.write_bytes(body)
    for job in project_jobs:
        dest = terminal / f'job-{job["id"]}.log'
        if not dest.exists():
            dest.write_bytes(get(f'/actions/jobs/{job["id"]}/logs'))
        raw = dest.read_bytes()
        (terminal / (dest.name + '.gz')).write_bytes(gzip.compress(raw, mtime=0))
        summary['project_job'] = job['id']
        summary['raw_log_sha256'] = hashlib.sha256(raw).hexdigest()
        summary['raw_log_bytes'] = len(raw)
    for artifact in listing['artifacts']:
        if artifact['name'] != 'lean-TR-26':
            continue
        dest = terminal / 'original-artifact.zip'
        if not dest.exists():
            dest.write_bytes(get(f'/actions/artifacts/{artifact["id"]}/zip'))
        body = dest.read_bytes()
        digest = hashlib.sha256(body).hexdigest()
        assert artifact['digest'] == 'sha256:' + digest
        assert artifact['size_in_bytes'] == len(body)
        (terminal / 'artifact-metadata.json').write_text(json.dumps(artifact, indent=2) + '\n')
        summary['artifact_id'] = artifact['id']
        summary['artifact_sha256'] = digest
        summary['artifact_bytes'] = len(body)
(snapshot / 'COLLECTION.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
