"""Read-only reconciliation of actual MF12 GitHub evidence; never runs Lean/Lake."""
from pathlib import Path, PurePosixPath
import hashlib, io, json, re, subprocess, tarfile, zipfile
import yaml

out = Path(__file__).resolve().parent
run = out / 'runtime-evidence'
repo = Path('/private/tmp/nla-lean-next-mf12-worktree')
commit = '3d06c49635bbdde109c491510641204285eaf05c'
project = 'matrix-functions-and-stability/MF-12/lean'

def sha(b): return hashlib.sha256(b).hexdigest()
def read(p): return json.loads(p.read_text())
def git(*args): return subprocess.check_output(['git', *args], cwd=repo)

meta, jobs, artifacts = [read(run / f) for f in ['run.json', 'jobs.json', 'artifacts.json']]
assert meta['id'] == 35037011332 and meta['run_attempt'] == 1
assert meta['head_sha'] == commit and meta['event'] == 'push'
assert meta['repository']['full_name'] == 'sgstepaniants/OpenProblemsInNLA'
assert meta['status'] == 'completed' and meta['conclusion'] == 'success'
job = next(j for j in jobs['jobs'] if j['name'] == f'verify (MF-12, {project})')
assert job['id'] == 104608341268 and job['conclusion'] == 'success'
assert all(s['conclusion'] in ['success', 'skipped'] for s in job['steps'])
assert next(s for s in job['steps'] if s['name'] == 'Fresh sandboxed statement, axiom and kernel verification')['conclusion'] == 'success'
assert next(s for s in job['steps'] if s['name'] == 'Validate formalization manifest')['conclusion'] == 'success'
artifact = next(a for a in artifacts['artifacts'] if a['name'] == 'lean-MF-12')
assert artifact['id'] == 10423298472 and not artifact['expired']
assert artifact['workflow_run']['id'] == meta['id'] and artifact['workflow_run']['head_sha'] == commit
archive = run / 'lean-MF-12.zip'
assert artifact['digest'] == 'sha256:' + sha(archive.read_bytes())
members = {}
with zipfile.ZipFile(archive) as z:
    for m in z.infolist():
        p = PurePosixPath(m.filename)
        assert not p.is_absolute() and '..' not in p.parts
        assert ((m.external_attr >> 16) & 0o170000) != 0o120000
        if m.is_dir(): continue
        content = z.read(m)
        assert content == (run / 'artifacts/lean-MF-12' / p).read_bytes(), str(p)
        members[str(p)] = sha(content)

receipts = list((run / 'artifacts/lean-MF-12').glob('verify-*/result.json'))
assert len(receipts) == 1
folder = receipts[0].parent
result = read(receipts[0])
assert result['repository_commit'] == commit and result['project'] == project
assert result['result'] == 'comparator-accepted'
assert result['semantic_review'] == 'not-performed-by-this-command'
with tarfile.open(fileobj=io.BytesIO(git('archive', '--format=tar', commit, '--', project))) as t:
    contents = {m.name.removeprefix(project + '/'):t.extractfile(m).read() for m in t.getmembers() if m.isfile()}
hashes = {p:sha(b) for p,b in contents.items()}
assert result['input_sha256'] == hashes == read(out / 'IMMUTABLE-INPUTS.json')['input_sha256']
assert len(hashes) == 322
config = json.loads(contents['comparator.json'])
assert result['config'] == config
names = config['theorem_names']
assert len(names) == len(set(names)) == 28 and config['definition_names'] == []
assert config['permitted_axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
manifest = yaml.safe_load(contents['formalization.yaml'])
assert [v['declaration'] for v in manifest['status']['main_results']] == names
assert manifest['status']['sorry_count'] == manifest['status']['sorry_in_definitions'] == 0

logs = {p.name:p.read_text() for p in folder.glob('*.log')}
for name in ['comparator.log', 'kernel-controls.log', 'comparator-controls.log', 'sandbox.log', 'user-service.log', 'dependencies.log', 'mathlib-cache.log']:
    assert logs[name].rstrip().endswith('EXIT_STATUS=0'), name
comp = logs['comparator.log']
assert 'nla-fresh-proof-' in comp.splitlines()[0]
assert 'COMPARATOR_LANDRUN=/home/runner/work/_temp/nla-lean-tools/scripts/strict_landrun.py' in comp.splitlines()[0]
assert 'RestrictAddressFamilies=~AF_UNIX' in comp.splitlines()[0]
assert comp.index('Building Challenge') < comp.index('Building Solution') < comp.index('Running Lean default kernel on solution.')
assert comp.count('declaration uses `sorry`') == 28
solution_log = comp[comp.index('Building Solution'):]
assert all(x not in solution_log for x in ['declaration uses `sorry`', 'sorryAx', 'Illegal axiom', 'error:'])
assert 'Lean default kernel accepts the solution' in solution_log
assert comp.count('Your solution is okay!') == 1
for module in ['Challenge', 'Solution']:
    lines = [s for s in comp.splitlines() if s.startswith('Exporting #[') and s.endswith(' from ' + module)]
    assert len(lines) == 1
    assert re.findall(r'\bNLA\.MF12\.[A-Za-z0-9_]+', lines[0]) == names
axioms = {}
for name in names:
    reports = re.findall(r"info: Solution\.lean:(\d+):0: '" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", comp)
    assert len(reports) == 1, name
    line, observed = reports[0]
    values = observed.split(', ')
    expected = ['propext', 'Quot.sound'] if name.endswith('.gap_decomposition') else config['permitted_axioms']
    assert values == expected, (name, values)
    metadata = next(m for m in manifest['status']['main_results'] if m['declaration'] == name)
    assert set(metadata['axioms']) == set(values)
    for match in re.findall(re.escape("'" + name + "' depends on axioms: ") + r'\[([^\]]*)\]', comp):
        assert set(match.split(', ')) == set(values)
    axioms[name] = {'observed_axioms':values, 'final_Solution_print_line':int(line), 'LeanCert_kernel_assertion_checked':True}

kernel_markers = ['RETURN honest_with_inductives_and_quotients: accepted',
    'RETURN invalid_raw_proof: rejected:', 'RETURN quotient_postcheck_mismatch: rejected:',
    'PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']
for marker in kernel_markers: assert marker in logs['kernel-controls.log'], marker
regressions = ['simple_match', 'simple_mismatch', 'simple_axiom_issue', 'simple_kind_mismatch', 'type_mismatch']
for case in regressions: assert 'PASS ' + case + ':' in logs['comparator-controls.log'], case
assert 'PASS: all five Comparator regressions' in logs['comparator-controls.log']
assert "Challenge and solution theorem statement do not match: 'checked'" in logs['comparator-controls.log']
for f,marker in [('negative-sorry.log',"Illegal axiom detected: 'sorryAx'"),('negative-native.log',"Illegal axiom detected: 'checked._native.native_decide.ax_1_1'")]:
    assert marker in logs[f] and logs[f].rstrip().endswith('EXIT_STATUS=1'), f
sandbox = logs['sandbox.log']
assert re.findall(r'Sandbox UID: (\d+)', sandbox) == ['1001','1001']
for mode in ['build','export']: assert 'MODE ' + mode + ': exit=0' in sandbox
for marker in ['outside .lake write-open: denied', 'outside .lake truncate: denied',
    'outside .lake read-only truncate-open: denied', 'symlink from .lake to outside write: denied',
    'outside .lake creation: denied', 'user namespace: private', 'pid namespace: private',
    'mnt namespace: private', 'net namespace: private', 'ipc namespace: private',
    'uts namespace: private', 'host parent: absent from private /proc',
    'host parent signal lookup: denied', 'host loopback listener: unreachable',
    'AF_UNIX socket creation: denied', 'effective capabilities: none',
    'no_new_privs: set', 'nested namespace write attempt: rejected exit=1']:
    assert sandbox.count('PASS ' + marker) == 2, marker
assert 'PASS build .lake write: allowed' in sandbox
assert 'PASS export .lake write-open: denied' in sandbox and 'PASS export .lake truncate: denied' in sandbox
for case in ['unknown option', 'unexpected --rw', 'unexpected --rwx', 'relative --rwx']:
    assert 'NEGATIVE ' + case + ': exit=2' in sandbox
assert 'Outer and export fixture contents unchanged; only designated build fixture written.' in sandbox

lock_bytes = git('show', commit + ':tools/lean/source-lock.json')
lock = json.loads(lock_bytes)
tool = result['tool_receipt']
assert result['source_lock_sha256'] == tool['source_lock_sha256'] == sha(lock_bytes)
assert tool['lean_toolchain'] == 'leanprover/lean4:v4.33.1'
assert tool['forsythe_commit'] == lock['commit'] == '8d1b0c0545a77b40245e84705aa7d273e6c81e62'
assert tool['platform'].startswith('Linux-') and 'x86_64-unknown-linux-gnu' in tool['lean_version']
assert tool['go_version'] == 'go version go1.27.1 linux/amd64'
assert set(tool['executables']) == {'.tools/comparator/.lake/build/bin/comparator','.tools/lean4export/.lake/build/bin/lean4export','.tools/bin/landrun'}
for p in ['tools/lean','.github/workflows/lean-verification.yml']:
    assert git('diff','ff6abf718126ceb23f933cf4f627f95104461fe8',commit,'--',p) == b''
deps = json.loads(contents['lake-manifest.json'])['packages']
for dep in deps:
    assert f"info: {dep['name']}: checking out revision '{dep['rev']}'" in logs['dependencies.log'], dep['name']
rawfile = run / f"job-{job['id']}.log"
raw = rawfile.read_text()
assert re.search(r'git log -1 --format=%H\n[^\n]*' + commit + r'\n',raw)
for marker in ['Manifest schema and comparator coverage: PASS (28 declarations)',
    'PASS: fresh Comparator run and all controls.',
    'Lean default kernel accepts the solution', 'Your solution is okay!']:
    assert marker in raw, marker
for line in comp.splitlines():
    if line.startswith('info: Solution.lean:') and 'depends on axioms' in line: assert line in raw
for marker in kernel_markers: assert marker in raw
assert 'PASS: all five Comparator regressions' in raw
assert "Illegal axiom detected: 'sorryAx'" in raw
assert "Illegal axiom detected: 'checked._native.native_decide.ax_1_1'" in raw
assert git('rev-parse','HEAD').decode().strip() == commit and not git('status','--porcelain').strip()
report = {
 'reviewer':'OpenAI Codex agent /root/next_elimination',
 'verdict':'ACCEPT actual source-bound canonical runtime; full mathematical approval is retained in the linked source review chain',
 'run_id':meta['id'],'run_attempt':meta['run_attempt'],'event':meta['event'],'job_id':job['id'],
 'literal_checkout_commit':commit,'project':project,'all322_actual_input_hashes_match_Git':True,
 'actual_export_count':28,'all_export_lists_match_frozen_comparator_order':True,
 'default_kernel_and_Comparator':'accepted','all28_LeanCert_kernel_assertions':'accepted',
 'all28_actual_axiom_sets_match_manifest':True,'actual_axioms':axioms,
 'raw_kernel_controls':kernel_markers,'comparator_regressions':regressions,
 'sorry_and_native_rejections':'expected exit1 and forbidden axiom detected',
 'build_export_sandbox_modes':'pass; both uid1001; writes/namespaces/capabilities/network/escape probes checked',
 'unexpected_sandbox_options':'all four rejected exit2',
 'standalone_checker_controls_job':'skipped because tools unchanged; all controls actually executed within the successful verify job',
 'artifact_id':artifact['id'],'artifact_archive_sha256':sha(archive.read_bytes()),
 'every_archive_member_matches_inspected_extraction':True,'archive_member_sha256':members,
 'result_receipt_sha256':sha(receipts[0].read_bytes()),'raw_verify_job_sha256':sha(rawfile.read_bytes()),
 'runtime_log_sha256':{p.name:sha(p.read_bytes()) for p in sorted(folder.glob('*.log'))},
 'tool_receipt':tool,'all10_dependency_revisions_observed':{p['name']:p['rev'] for p in deps},
 'source_checks_sha256':sha((out/'SOURCE-CHECKS.json').read_bytes()),
 'immutable_inputs_sha256':sha((out/'IMMUTABLE-INPUTS.json').read_bytes()),
 'auditor_sha256':sha(Path(__file__).read_bytes()),'local_Lean_Lake_cache_execution':False,
 'source_config_git_mutations':False,
 'limitations':'Independent AI-agent source/evidence review of one observed GitHub execution. No independent human review, formal verification of checker software, claim of a second run performed by this reviewer, or later publication/merge execution acceptance.'}
(out/'AXIOMS.json').write_text(json.dumps(axioms,indent=2)+'\n')
(out/'RUNTIME-CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'run':meta['id'],'job':job['id'],'inputs':len(hashes),'exports':len(names),'verdict':'accept','runtime_checks_sha256':sha((out/'RUNTIME-CHECKS.json').read_bytes()),'axioms_sha256':sha((out/'AXIOMS.json').read_bytes())},indent=2))
