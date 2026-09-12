#!/usr/bin/env python3
"""Retain an actual GitHub verification artifact and check its source identity."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import zipfile

GH = '/tmp/nla-submission-tools/gh_2.100.0_macOS_arm64/bin/gh'
REPO = 'sgstepaniants/OpenProblemsInNLA'

def api(path):
    return subprocess.check_output([GH, 'api', f'repos/{REPO}/{path}'])

def digest(data):
    return hashlib.sha256(data).hexdigest()

def main():
    p = argparse.ArgumentParser()
    p.add_argument('run'); p.add_argument('problem'); p.add_argument('commit')
    p.add_argument('worktree', type=Path); p.add_argument('out', type=Path)
    a = p.parse_args(); a.out.mkdir(parents=True, exist_ok=True)
    run_raw = api(f'actions/runs/{a.run}'); run = json.loads(run_raw)
    assert run['head_sha'] == a.commit and run['conclusion'] == 'success'
    (a.out/'run-metadata.json').write_bytes(run_raw)
    jobs_raw = api(f'actions/runs/{a.run}/jobs'); jobs = json.loads(jobs_raw)
    (a.out/'jobs.json').write_bytes(jobs_raw)
    selected = [j for j in jobs['jobs'] if j['name'].startswith(f'verify ({a.problem},')]
    assert len(selected) == 1 and selected[0]['conclusion'] == 'success'
    metadata_raw = api(f'actions/runs/{a.run}/artifacts'); metadata = json.loads(metadata_raw)
    (a.out/'artifact-metadata.json').write_bytes(metadata_raw)
    artifacts = [x for x in metadata['artifacts'] if x['name'] == f'lean-{a.problem}']
    assert len(artifacts) == 1
    artifact = artifacts[0]; archive = api(f"actions/artifacts/{artifact['id']}/zip")
    assert artifact['digest'] == 'sha256:' + digest(archive)
    zpath = a.out/f'lean-{a.problem}.zip'; zpath.write_bytes(archive)
    extracted = a.out/'artifacts'/f'lean-{a.problem}'
    with zipfile.ZipFile(zpath) as z:
        for item in z.infolist():
            path = PurePosixPath(item.filename)
            assert not path.is_absolute() and '..' not in path.parts
            if item.is_dir(): continue
            target = extracted/path
            target.parent.mkdir(parents=True, exist_ok=True)
            data = z.read(item)
            if target.exists(): assert target.read_bytes() == data
            else: target.write_bytes(data)
    results = list(extracted.glob('verify-*/result.json')); assert len(results) == 1
    result = json.loads(results[0].read_text())
    assert result['result'] == 'comparator-accepted'
    assert result['repository_commit'] == a.commit
    checked = {}
    for path, expected in result['input_sha256'].items():
        source = subprocess.check_output(['git', 'show', f"{a.commit}:{result['project']}/{path}"], cwd=a.worktree)
        assert digest(source) == expected
        checked[path] = expected
    log = subprocess.check_output([GH,'run','view',a.run,'--repo',REPO,'--log'])
    (a.out/'run.log').write_bytes(log)
    inventory = {str(f.relative_to(a.out)):digest(f.read_bytes()) for f in sorted(a.out.rglob('*')) if f.is_file() and f.name != 'FETCH-IDENTITY.json'}
    record = {'run':int(a.run),'commit':a.commit,'artifact_id':artifact['id'],
              'github_archive_sha256_verified':digest(archive),'successful_job_id':selected[0]['id'],
              'input_hashes_matched_committed_blobs':checked,'retained_file_sha256':inventory,
              'scope':'Download provenance and source identity only; actual logs still require review.'}
    (a.out/'FETCH-IDENTITY.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'run':a.run,'problem':a.problem,'source_files':len(checked),'retained_files':len(inventory),'archive_digest_verified':True}))

if __name__ == '__main__': main()
