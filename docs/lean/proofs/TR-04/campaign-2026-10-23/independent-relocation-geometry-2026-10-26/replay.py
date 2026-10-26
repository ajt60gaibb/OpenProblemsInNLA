#!/usr/bin/env python3
"""Independent full fresh replay of frozen root relocation/composition support."""
import argparse, datetime, hashlib, json, os, pathlib, re, subprocess, sys
HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parents[5]
LIVE = REPO / 'lean-statements'
AUTHOR = REPO / 'docs/lean/proofs/TR-04/campaign-2026-10-25/program-relocation-author'
TOOLING = REPO.parent / 'tooling'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=pathlib.Path, default=HERE / 'run')
OUT = parser.parse_args().output.resolve()
SNAP, OBJECTS = OUT / 'sources', OUT / 'objects'
assert not OBJECTS.exists(), 'Use a new output directory: no project objects may be reused.'
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
lockpath = AUTHOR / 'source-lock.json'
assert digest(lockpath) == '2e27bf8e95ac860b716770f9dba42d583e62ad36a6cc31f848353a58bd5a3af5'
lock = json.loads(lockpath.read_text())
assert len(lock['project_closure']) == 16 and len(lock['authored_declarations']) == 36
started = datetime.datetime.now(datetime.timezone.utc).isoformat()

def check_inputs():
    assert digest(lockpath) == '2e27bf8e95ac860b716770f9dba42d583e62ad36a6cc31f848353a58bd5a3af5'
    for rec in lock['project_closure'] + lock['reviewed_original_inputs']:
        assert digest(REPO / rec['path']) == rec['sha256'], rec['path']
    assert len(lock['reviewed_original_inputs']) == 25

check_inputs()
for rec in lock['project_closure']:
    rel = pathlib.Path(rec['path']).relative_to('lean-statements')
    src = SNAP / rel
    src.parent.mkdir(parents=True, exist_ok=True)
    src.write_bytes((LIVE / rel).read_bytes())
(SNAP / '.lake').mkdir(exist_ok=True)
(SNAP / '.lake/packages').symlink_to((LIVE / '.lake/packages').resolve(), target_is_directory=True)
env = dict(os.environ, NLA_CAMPAIGN_SOURCE_ROOT=str(SNAP), NLA_CAMPAIGN_OBJECT_ROOT=str(OBJECTS))
source_cmd = [sys.executable, str(TOOLING / 'tr06-build-closure.py')] + lock['targets']
with (OUT / 'source-build.log').open('w') as log:
    proc = subprocess.run(source_cmd, cwd=REPO, env=env, stdout=log, stderr=subprocess.STDOUT)
assert proc.returncode == 0, OUT / 'source-build.log'
consumer = SNAP / 'RelocationConsumer.lean'
text = (HERE / 'RelocationConsumer.lean').read_text()
for name in lock['authored_declarations']:
    text += '#assert_trust kernel ' + name + '\n#print axioms ' + name + '\n'
consumer.write_text(text)
binary = TOOLING / 'lean-4.33.1-darwin_aarch64/bin/lean'
paths = [OBJECTS] + [p / '.lake/build/lib/lean' for p in sorted((SNAP / '.lake/packages').iterdir())
                     if (p / '.lake/build/lib/lean').is_dir()]
cenv = dict(env, PATH=str(binary.parent) + os.pathsep + os.environ['PATH'],
            LEAN_PATH=os.pathsep.join(map(str, paths)))
consumer_cmd = [str(binary), '-o', str(OBJECTS / 'RelocationConsumer.olean'), str(consumer)]
with (OUT / 'consumer-build.log').open('w') as log:
    cp = subprocess.run(consumer_cmd, cwd=SNAP, env=cenv, stdout=log, stderr=subprocess.STDOUT)
assert cp.returncode == 0, OUT / 'consumer-build.log'
check_inputs()
for rec in lock['project_closure']:
    assert digest(SNAP / pathlib.Path(rec['path']).relative_to('lean-statements')) == rec['sha256']
metas = list(OBJECTS.rglob('*.source-sha256.json'))
assert len(metas) == 16
logs = (OUT / 'source-build.log').read_text() + (OUT / 'consumer-build.log').read_text()
assert 'sorryAx' not in logs
axioms = re.findall(r'depends on axioms: \[([^]]*)\]', logs)
assert axioms and all(set(x.strip() for x in a.split(',') if x.strip()) <=
                     {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms)
result = {'reviewer': '/root/recover_geometry', 'passed': True,
 'execution_started_utc': started,
 'execution_completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'scope': 'Independent four-body source/math review and full fresh16-source plus concrete copy/SVD caller consumer; supporting machine components, not complete TR04 Target/program',
 'source_lock_sha256': digest(lockpath), 'driver_sha256': digest(pathlib.Path(__file__)),
 'fresh_project_source_count': 16, 'fresh_kernel_command_count': 17,
 'authored_declarations_asserted': 36, 'project_objects_reused': False,
 'external_pinned_package_objects_reused': True,
 'explicit_nontrivial_copy_frame_and_label_permutation': True,
 'concrete_caller_continuation_before_local_halt': True,
 'concrete_SVD_frame_and_nonempty_constant_pool_map': True,
 'arbitrary_caller_times_traces_and_rectangular_SVD_replies_checked': True,
 'all16_sources_and_25_original_review_inputs_unchanged': True,
 'source_exit_code': proc.returncode, 'consumer_exit_code': cp.returncode,
 'printed_axiom_lists': axioms,
 'compiler': subprocess.check_output([str(binary), '--version'], text=True).strip(),
 'source_command': source_cmd, 'consumer_command': consumer_cmd,
 'evidence': [{'path': str(p.relative_to(OUT)), 'sha256': digest(p)}
              for p in [consumer, OUT / 'source-build.log', OUT / 'consumer-build.log']]}
(OUT / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
