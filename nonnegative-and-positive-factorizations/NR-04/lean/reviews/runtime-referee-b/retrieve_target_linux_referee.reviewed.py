"""Retrieve official read-only GitHub evidence and safely extract authenticated zips.

No compiler, proof, publication, or remote write operations are performed.
"""
from pathlib import Path, PurePosixPath
import datetime
import hashlib
import json
import re
import stat
import subprocess
import sys
import zipfile

spec_path = Path(sys.argv[1]).resolve()
spec = json.loads(spec_path.read_text())
D = Path(__file__).resolve().parents[1]
E = Path(spec['evidence']).resolve()
assert E.is_relative_to(D)
E.mkdir(parents=True, exist_ok=True)
gh = D / 'tools/gh-2.101.0/gh_2.101.0_macOS_arm64/bin/gh'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
command_file = E / 'RETRIEVAL-COMMANDS.json'
commands = json.loads(command_file.read_text()) if command_file.exists() else []


def get(endpoint, output, raw_log=False):
    assert endpoint.startswith('repos/') and not endpoint.startswith('/')
    output.parent.mkdir(parents=True, exist_ok=True)
    argv = [str(gh), 'api', endpoint] + (['--allow-escape-sequences'] if raw_log else [])
    prior = [c for c in commands if c['argv'] == argv and c['exit_code'] == 0 and c['output'] == str(output)]
    if prior:
        assert output.is_file() and sha(output) == prior[-1]['output_sha256']
        return output.read_bytes()
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    result = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output.write_bytes(result.stdout)
    error = output.with_name(output.name + '.stderr')
    error.write_bytes(result.stderr)
    commands.append({'argv': argv, 'cwd': str(Path.cwd()), 'start': start,
                     'end': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                     'exit_code': result.returncode, 'output': str(output),
                     'output_sha256': sha(output), 'stderr': str(error),
                     'stderr_sha256': sha(error)})
    (E / 'RETRIEVAL-COMMANDS.json').write_text(json.dumps(commands, indent=2) + '\n')
    if result.returncode:
        raise RuntimeError(f'GitHub read failed: {endpoint}; retained stderr at {error}')
    return result.stdout


for entry in spec['runs']:
    kind, repository, run_id = entry['kind'], entry['repository'], entry['run_id']
    assert re.fullmatch(r'[a-z]+', kind)
    assert re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repository)
    assert isinstance(run_id, int)
    root = E / kind
    run = json.loads(get(f'repos/{repository}/actions/runs/{run_id}', root / 'official-run.json'))
    jobs = json.loads(get(f'repos/{repository}/actions/runs/{run_id}/jobs?per_page=100', root / 'official-jobs.json'))
    artifacts = json.loads(get(f'repos/{repository}/actions/runs/{run_id}/artifacts?per_page=100', root / 'official-artifacts.json'))
    assert len(jobs['jobs']) == jobs['total_count']
    assert len(artifacts['artifacts']) == artifacts['total_count']
    matches = [a for a in artifacts['artifacts'] if a['name'] == f"lean-{spec['problem']}"]
    assert len(matches) == 1 and not matches[0]['expired']
    artifact = matches[0]
    archive = root / f"lean-{spec['problem']}.zip"
    get(f"repos/{repository}/actions/artifacts/{artifact['id']}/zip", archive)
    assert artifact['digest'] == 'sha256:' + sha(archive)
    assert artifact['size_in_bytes'] == archive.stat().st_size
    target = root / 'artifact'
    target.mkdir(exist_ok=True)
    seen = set()
    inventory = []
    with zipfile.ZipFile(archive) as z:
        assert sum(i.file_size for i in z.infolist()) < 200_000_000
        for info in z.infolist():
            p = PurePosixPath(info.filename)
            assert not p.is_absolute() and '..' not in p.parts and '\\' not in info.filename
            assert p.parts and p.parts[0] not in {'', '.'}
            mode = info.external_attr >> 16
            assert stat.S_IFMT(mode) in {0, stat.S_IFREG, stat.S_IFDIR}
            dest = target.joinpath(*p.parts)
            assert dest.resolve().is_relative_to(target.resolve())
            assert str(p) not in seen
            seen.add(str(p))
            if info.is_dir():
                dest.mkdir(parents=True, exist_ok=True)
            else:
                dest.parent.mkdir(parents=True, exist_ok=True)
                data = z.read(info)
                if dest.exists():
                    assert dest.read_bytes() == data
                else:
                    dest.write_bytes(data)
                inventory.append({'path': str(p), 'bytes': dest.stat().st_size, 'sha256': sha(dest)})
    (root / 'ARTIFACT-FILES.json').write_text(json.dumps(inventory, indent=2) + '\n')
    receipt_files = list(target.rglob('result.json'))
    assert len(receipt_files) == 1
    receipt = json.loads(receipt_files[0].read_text())
    checked_sha = receipt['repository_commit']
    assert re.fullmatch(r'[a-f0-9]{40}', checked_sha)
    checked = json.loads(get(f'repos/{repository}/git/commits/{checked_sha}', root / 'official-checked-commit.json'))
    for job in jobs['jobs']:
        if job['name'] == 'select' or job['name'].startswith('verify ('):
            get(f"repos/{repository}/actions/jobs/{job['id']}/logs", root / f"official-job-{job['id']}.raw.log", raw_log=True)
    provenance = {'repository': repository, 'run': run, 'jobs': jobs,
                  'artifacts': artifacts, 'checked_commit': checked,
                  'retrieved_by': spec['reviewer'],
                  'retrieval_scope': 'Official GitHub REST responses; see raw saved outputs and command hashes'}
    (root / 'GITHUB-PROVENANCE.json').write_text(json.dumps(provenance, indent=2) + '\n')
    print(json.dumps({'kind': kind, 'run': run_id, 'artifact': artifact['id'],
                      'archive_sha256': sha(archive), 'checked_commit': checked_sha,
                      'artifact_files': len(inventory)}), flush=True)

(E / 'RETRIEVAL-SUMMARY.json').write_text(json.dumps({
    'scope': 'Independent nonauthor retrieval; no Lean, Comparator, proof edit, publication or promotion',
    'reviewer': spec['reviewer'], 'script_sha256': sha(Path(__file__)),
    'spec_sha256': sha(spec_path), 'gh_binary_sha256': sha(gh),
    'commands_sha256': sha(E / 'RETRIEVAL-COMMANDS.json'), 'runs': spec['runs'],
}, indent=2) + '\n')
