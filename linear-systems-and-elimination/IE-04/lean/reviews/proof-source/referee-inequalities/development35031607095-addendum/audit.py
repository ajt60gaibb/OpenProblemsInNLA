#!/usr/bin/env python3
"""Read-only Git/log/receipt audit of two complete development builds.

No Lean/Lake execution and no claim of canonical Comparator acceptance.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import zipfile

HERE = Path(__file__).resolve().parent
BASE = Path('/tmp/nla-lean-next-20260915')
RUN = BASE / 'development-runs/35031607095'
ARTIFACT = RUN / 'artifacts/lean-development-statements'
REPO = Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
COMMIT = '4bd2d76ec6e37696ff0c2d5feacf21e342371f27'


def sha(b):
    return hashlib.sha256(b).hexdigest()


def git(rel):
    return subprocess.run(['git', 'show', f'{COMMIT}:{rel}'], cwd=REPO,
                          check=True, capture_output=True).stdout


def save(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + '.tmp')
    with temp.open('w') as f:
        json.dump(obj, f, indent=2, ensure_ascii=False)
        f.write('\n')
        f.flush()
        os.fsync(f.fileno())
    os.replace(temp, path)


receipt = json.loads((ARTIFACT / 'receipt.json').read_text())
metadata = json.loads((RUN / 'run.json').read_text())
jobs = json.loads((RUN / 'jobs.json').read_text())['jobs']
archive_metadata = json.loads((RUN / 'artifacts.json').read_text())['artifacts']
fetch = json.loads((RUN / 'FETCH-IDENTITY.json').read_text())
assert metadata['id'] == 35031607095
assert metadata['head_sha'] == receipt['repository_commit'] == fetch['commit'] == COMMIT
assert metadata['conclusion'] == 'failure' and receipt['status'] == 'failed'
assert receipt['run_id'] == '35031607095' and receipt['run_attempt'] == '1'
assert receipt['platform'].startswith('Linux') and receipt['uid'] == 1001
assert not receipt['comparator_run'] and not receipt['mathematical_verification']
assert len(jobs) == 1 and jobs[0]['id'] == 104591152756
assert jobs[0]['head_sha'] == COMMIT and jobs[0]['labels'] == ['ubuntu-24.04']
assert len(archive_metadata) == 1
archive = archive_metadata[0]
assert archive['id'] == 10421054240 and archive['workflow_run']['id'] == 35031607095
assert archive['workflow_run']['head_sha'] == COMMIT
zip_path = RUN / 'lean-development-statements.zip'
zip_sha = sha(zip_path.read_bytes())
assert archive['digest'] == 'sha256:' + zip_sha
assert zip_sha == fetch['archives'][0]['sha256']
assert zip_path.stat().st_size == archive['size_in_bytes']
zip_members = {}
with zipfile.ZipFile(zip_path) as z:
    for member in z.namelist():
        if member.endswith('/'):
            continue
        content = z.read(member)
        assert content == (ARTIFACT / member).read_bytes(), member
        zip_members[member] = sha(content)

source_hashes = receipt['source_sha256']
assert len(source_hashes) == 115
for rel, expected in source_hashes.items():
    assert sha(git('.lean-development/' + rel)) == expected, rel
for cmd in receipt['commands']:
    assert cmd['source_sha256_after'] == source_hashes, cmd['argv']
    assert sha((ARTIFACT / cmd['log']).read_bytes()) == cmd['sha256'], cmd['log']
assert len(receipt['commands']) == 9
failures = [c for c in receipt['commands'] if c['exit_code']]
assert len(failures) == 1 and failures[0]['log'] == 'MF-12-modules.log'
assert 'NLA.MF12.' in receipt['error']

manifest = json.loads(git('.lean-development/lake-manifest.json'))
pins = {p['name']: p['rev'] for p in manifest['packages']}
assert pins == receipt['dependency_commits'] and len(pins) == 10
assert git('.lean-development/lean-toolchain') == b'leanprover/lean4:v4.33.1\n'
assert (ARTIFACT / 'lean-version.log').read_text().startswith('Lean (version 4.33.1, x86_64-unknown-linux-gnu,')

raw_job = (RUN / 'job-104591152756.log').read_text()
job = re.sub(r'(?m)^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+Z ?', '', raw_job)
assert COMMIT in job
assert f'Artifact ID {archive["id"]}' in job
assert f'SHA256 digest of uploaded artifact zip is {zip_sha}' in job
for cmd in receipt['commands']:
    assert 'RUN ' + repr(cmd['argv']) in job
    assert (ARTIFACT / cmd['log']).read_text() in job, ('raw job correspondence', cmd['log'])

projects = {
    'IE04': {'id': 'IE-04', 'review': BASE / 'reviews/IE04-inequalities-full-source-referee',
             'key': 'source_files', 'author': BASE / 'elimination/IE-04', 'targets': 21},
    'MF24': {'id': 'MF-24', 'review': BASE / 'reviews/MF24-inequalities-source-referee/final-byte-addendum-20260915',
             'key': 'files', 'author': BASE / 'matrix-functions/MF-24', 'targets': 22},
}
results = {}
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for short, data in projects.items():
    reviewed = json.loads((data['review'] / 'INPUTS.json').read_text())[data['key']]
    compiled = {}
    for rel, expected in reviewed.items():
        assert sha((data['author'] / rel).read_bytes()) == expected, ('changed author bytes', short, rel)
        if rel.endswith('.lean'):
            remote = f'Challenges/{short}.lean' if rel == 'Challenge.lean' else \
                     f'NLA/{short}/Solution.lean' if rel == 'Solution.lean' else rel
        elif rel == 'NUMERICAL_TARGETS.md':
            remote = f'notes/{short}-NUMERICAL_TARGETS.md'
        else:
            continue
        assert source_hashes[remote] == expected, ('approved vs compiled bytes', short, rel)
        compiled[rel] = {'development_path': remote, 'sha256': expected}
    expected_local = {rel for rel in source_hashes if rel.startswith(f'NLA/{short}/')}
    assert expected_local == {v['development_path'] for v in compiled.values()
                              if v['development_path'].startswith('NLA/')}
    log_name = data['id'] + '-modules.log'
    log = (ARTIFACT / log_name).read_text()
    command = next(c for c in receipt['commands'] if c['log'] == log_name)
    assert command['argv'] == ['lake', 'build', f'NLA.{short}.Solution'] and command['exit_code'] == 0
    assert 'Build completed successfully' in log and f'Built NLA.{short}.Solution' in log
    assert not re.search(r'(?m)^error:|sorryAx|depends on sorry|unrecognized axioms|declaration uses `sorry`', log)
    for path in expected_local:
        module = path.removesuffix('.lean').replace('/', '.')
        assert 'Built ' + module + ' ' in log, ('module missing acceptance', module)
    targets = json.loads((data['author'] / 'comparator.json').read_text())['theorem_names']
    assert len(targets) == data['targets']
    audited = {}
    for name in targets:
        pattern = r"(?m)^info: NLA/" + short + r"/Solution\.lean:\d+:0: '" + re.escape(name) + \
                  r"' depends on axioms: \[([^\]]*)\]$"
        matches = re.findall(pattern, log)
        assert len(matches) == 1, ('target axiom line missing/duplicate', name)
        axioms = set(matches[0].split(', ')) if matches[0] else set()
        assert axioms <= allowed
        solution = (data['author'] / 'Solution.lean').read_text()
        short_name = name.removeprefix('NLA.' + short + '.')
        assert re.search(r'(?m)^#assert_trust kernel (?:NLA\.' + short + r'\.)?' +
                         re.escape(short_name) + r'\s*$', solution)
        audited[name] = sorted(axioms)
    challenge_name = data['id'] + '-challenge.log'
    challenge_command = next(c for c in receipt['commands'] if c['log'] == challenge_name)
    challenge_log = (ARTIFACT / challenge_name).read_text()
    assert challenge_command['exit_code'] == 0
    assert challenge_log.count('warning: declaration uses `sorry`') == data['targets']
    assert 'error:' not in challenge_log
    project_pins = {p['name']:p['rev'] for p in json.loads((data['author']/'lake-manifest.json').read_text())['packages']}
    assert project_pins == pins
    results[short] = {'problem': data['id'], 'review_sha256': sha((data['review']/'REVIEW.md').read_bytes()),
                      'review_inputs_sha256': sha((data['review']/'INPUTS.json').read_bytes()),
                      'all_reviewed_author_files_unchanged': len(reviewed), 'compiled_source_mapping': compiled,
                      'complete_implementation_modules': len(expected_local), 'all_target_axioms': audited,
                      'commands': [{k:v for k,v in c.items() if k != 'source_sha256_after'}
                                   for c in [command,challenge_command]],
                      'complete_development_graph_accepted': True,
                      'canonical_comparator_accepted': False, 'whole_problem_verified': False}

common = {'reviewer': '/root/next_inequalities', 'run_id': 35031607095, 'commit': COMMIT,
          'job_id': 104591152756, 'archive_id': archive['id'], 'archive_sha256': zip_sha,
          'receipt_sha256': sha((ARTIFACT/'receipt.json').read_bytes()),
          'raw_job_sha256': sha((RUN/'job-104591152756.log').read_bytes()),
          'source_inputs_independently_matched_to_Git': len(source_hashes),
          'all_command_post_source_hashes_equal_before': True, 'all_nine_raw_logs_matched_to_job': True,
          'Linux_uid': receipt['uid'], 'dependency_commits': pins, 'archive_members': zip_members,
          'overall_workflow_conclusion': 'failure in MF12 only; both reviewed complete projects accepted',
          'canonical_comparator_run': False, 'independent_default_kernel_replay': False,
          'negative_controls_run': False, 'projects': results}
save(HERE/'AUDIT.json', common)
for short,data in projects.items():
    dest = data['review'] / 'development35031607095-addendum'
    dest.mkdir(exist_ok=True)
    shutil.copyfile(HERE/'AUDIT.json', dest/'AUDIT.json')
    evidence = dest/'evidence'
    evidence.mkdir(exist_ok=True)
    files = [RUN/'FETCH-IDENTITY.json', RUN/'run.json', RUN/'jobs.json', RUN/'artifacts.json',
             RUN/'job-104591152756.log', zip_path, ARTIFACT/'receipt.json',
             ARTIFACT/(data['id']+'-modules.log'), ARTIFACT/(data['id']+'-challenge.log'),
             ARTIFACT/'lean-version.log']
    file_hashes = {}
    for src in files:
        shutil.copyfile(src,evidence/src.name)
        file_hashes['evidence/'+src.name] = sha(src.read_bytes())
    for rel in ['.lean-development/check.py','.lean-development/projects.json',
                '.lean-development/lakefile.toml','.lean-development/lake-manifest.json',
                '.github/workflows/lean-development.yml']:
        target = dest/'runtime-source'/rel
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(git(rel))
        file_hashes[str(target.relative_to(dest))] = sha(target.read_bytes())
    shutil.copyfile(HERE/'audit.py',dest/'audit.py')
    file_hashes['audit.py'] = sha((HERE/'audit.py').read_bytes())
    file_hashes['AUDIT.json'] = sha((dest/'AUDIT.json').read_bytes())
    save(dest/'INPUTS.json',{'phase':'source/development acceptance, canonical gates pending',
                            'files':file_hashes,'project':results[short]})
print(json.dumps({'audit_sha256':sha((HERE/'AUDIT.json').read_bytes()),
                  'projects':{k:{'modules':v['complete_implementation_modules'],
                                 'targets':len(v['all_target_axioms']),
                                 'source_matched':len(v['compiled_source_mapping'])}
                              for k,v in results.items()}},indent=2))
