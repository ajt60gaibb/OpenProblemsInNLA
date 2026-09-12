"""Retain the original checker-controls artifact ZIP and verify GitHub's digest."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import subprocess
import zipfile

GH = '/tmp/nla-submission-tools/gh_2.100.0_macOS_arm64/bin/gh'
REPOSITORY = 'sgstepaniants/OpenProblemsInNLA'
RUN = '34709291624'
OUT = Path(__file__).resolve().parent

def api(path):
    return subprocess.check_output([GH, 'api', f'repos/{REPOSITORY}/{path}'])

def put(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        assert path.read_bytes() == data, str(path)
    else:
        path.write_bytes(data)

raw = api(f'actions/runs/{RUN}/artifacts')
metadata = json.loads(raw)
artifacts = [a for a in metadata['artifacts'] if a['name'] == 'lean-checker-controls']
assert len(artifacts) == 1
artifact = artifacts[0]
assert not artifact['expired']
archive = api(f"actions/artifacts/{artifact['id']}/zip")
digest = hashlib.sha256(archive).hexdigest()
assert artifact['digest'] == 'sha256:' + digest
put(OUT / 'checker-control-artifact-metadata.json', raw)
path = OUT / 'lean-checker-controls.zip'
put(path, archive)
with zipfile.ZipFile(path) as zipped:
    for member in zipped.infolist():
        name = PurePosixPath(member.filename)
        assert not name.is_absolute() and '..' not in name.parts
        if not member.is_dir():
            put(OUT / 'artifacts/lean-checker-controls' / name, zipped.read(member))
record = {'run': int(RUN), 'artifact_id': artifact['id'], 'name': artifact['name'],
          'sha256': digest, 'github_digest_verified': True,
          'scope': 'Original artifact provenance only; operational logs require separate review.'}
put(OUT / 'CHECKER-CONTROL-FETCH.json', (json.dumps(record, indent=2) + '\n').encode())
print(json.dumps(record))
