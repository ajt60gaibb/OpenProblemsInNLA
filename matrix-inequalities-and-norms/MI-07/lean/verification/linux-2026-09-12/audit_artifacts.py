"""Independent checks of retained MI-07 Linux receipts, logs, and input identity."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import zipfile

OUT = Path(__file__).resolve().parent
PROJECT = OUT.parents[1]
REPO = PROJECT.parents[2]
COMMIT = 'f55777156432043de4201747a3759e0c6485e568'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(name):
    return json.loads((OUT/name).read_text())

def blob(path):
    return subprocess.check_output(['git','show',COMMIT+':'+path],cwd=REPO)

run = read('run-metadata.json')
assert run['id'] == 34709291624 and run['head_sha'] == COMMIT
assert run['status'] == 'completed' and run['conclusion'] == 'success'
jobs = read('jobs.json')['jobs']
selected = next(j for j in jobs if j['id'] == 103594995726)
assert selected['name'] == 'verify (MI-07, matrix-inequalities-and-norms/MI-07/lean)'
assert selected['conclusion'] == 'success'
assert all(s['conclusion'] == 'success' for s in selected['steps'])
assert all(j['conclusion'] == 'success' for j in jobs)

artifact_records = []
for name in ['lean-MI-07','lean-checker-controls']:
    item = next(a for a in read('artifact-metadata.json')['artifacts'] if a['name'] == name)
    zip_path = OUT/(name+'.zip')
    assert item['digest'] == 'sha256:'+sha(zip_path)
    assert item['size_in_bytes'] == zip_path.stat().st_size and not item['expired']
    members = {}
    with zipfile.ZipFile(zip_path) as archive:
        assert archive.testzip() is None
        for info in archive.infolist():
            if info.is_dir():
                continue
            data = archive.read(info)
            assert (OUT/'artifacts'/name/info.filename).read_bytes() == data
            members[info.filename] = hashlib.sha256(data).hexdigest()
    artifact_records.append({'name':name,'id':item['id'],'sha256':sha(zip_path),
                             'original_zip_digest_verified':True,'members':members})

logs = next((OUT/'artifacts/lean-MI-07').glob('verify-*'))
result = json.loads((logs/'result.json').read_text())
assert result['repository_commit'] == COMMIT and result['result'] == 'comparator-accepted'
config = json.loads(blob(result['project']+'/comparator.json'))
assert result['config'] == config
assert len(config['theorem_names']) == 7 and config['definition_names'] == []
assert set(config['permitted_axioms']) == STANDARD
for name, expected in result['input_sha256'].items():
    assert hashlib.sha256(blob(result['project']+'/'+name)).hexdigest() == expected, name
    assert sha(PROJECT/name) == expected, name
precheck = read('SOURCE-IDENTITY-PRECHECK.json')
for name, expected in precheck['frozen_files_at_commit'].items():
    assert result['input_sha256'][name] == expected['sha256']
for name, expected in precheck['final_review_sha256'].items():
    assert result['input_sha256'][name] == expected

receipt = result['tool_receipt']
lock_hash = sha(OUT/'source/tools/lean/source-lock.json')
assert result['source_lock_sha256'] == receipt['source_lock_sha256'] == lock_hash
assert receipt['forsythe_commit'] == precheck['locked_forsythe_commit']
assert receipt['ci_sandbox_probe_sha256'] == precheck['reconstructed_ci_probe_sha256']
assert receipt['lean_toolchain'] == 'leanprover/lean4:v4.33.1'
assert 'x86_64-unknown-linux-gnu' in receipt['lean_version']
assert '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in receipt['lean_version']
control_result = json.loads(next((OUT/'artifacts/lean-checker-controls').glob('selftest-*/result.json')).read_text())
assert control_result['tool_receipt'] == receipt

control_checks = {}
for scope, folder in [('MI07-own-controls', logs),
                      ('separate-checker-job',next((OUT/'artifacts/lean-checker-controls').glob('selftest-*')))]:
    sandbox = (folder/'sandbox.log').read_text()
    required = ['MODE build: exit=0','MODE export: exit=0',
                'PASS build .lake write: allowed','PASS export .lake write-open: denied',
                'PASS export .lake truncate: denied',
                'Outer and export fixture contents unchanged; only designated build fixture written.']
    assert all(s in sandbox for s in required)
    for marker in ['outside .lake write-open','outside .lake truncate',
                   'outside .lake read-only truncate-open','symlink from .lake to outside write',
                   'outside .lake creation','host parent signal lookup','AF_UNIX socket creation']:
        assert sandbox.count('PASS '+marker+': denied') == 2, marker
    for namespace in ['user','pid','mnt','net','ipc','uts']:
        assert sandbox.count('PASS '+namespace+' namespace: private') == 2
    for marker in ['PASS host parent: absent from private /proc',
                   'PASS host loopback listener: unreachable',
                   'PASS effective capabilities: none','PASS no_new_privs: set',
                   'PASS nested namespace write attempt: rejected exit=1','Sandbox UID: 1001']:
        assert sandbox.count(marker) == 2
    for label in ['unknown option','unexpected --rw','unexpected --rwx','relative --rwx']:
        assert 'NEGATIVE '+label+': exit=2' in sandbox
    assert '\nFAIL ' not in sandbox and sandbox.rstrip().endswith('EXIT_STATUS=0')
    kernel = (folder/'kernel-controls.log').read_text()
    assert 'RETURN honest_with_inductives_and_quotients: accepted' in kernel
    assert 'RETURN invalid_raw_proof: rejected:' in kernel and 'declaration type mismatch' in kernel
    assert 'RETURN quotient_postcheck_mismatch: rejected: Quotient constant mismatch on: Quot.lift' in kernel
    assert 'PASS: all three actual Comparator.runBuiltinKernel cases behaved as required' in kernel
    regressions = (folder/'comparator-controls.log').read_text()
    for label,status in [('simple_match',0),('simple_mismatch',1),('simple_axiom_issue',1),
                         ('simple_kind_mismatch',1),('type_mismatch',1)]:
        assert f'PASS {label}: exit {status}, expected {status};' in regressions
    assert 'PASS: all five Comparator regressions' in regressions
    for name,marker in [('negative-sorry.log',"Illegal axiom detected: 'sorryAx'"),
                        ('negative-native.log',"Illegal axiom detected: 'checked._native.native_decide.ax_1_1'")]:
        text=(folder/name).read_text()
        assert 'Building Challenge' in text and 'Building Solution' in text
        assert marker in text and text.rstrip().endswith('EXIT_STATUS=1')
    assert (folder/'user-service.log').read_text().rstrip().endswith('EXIT_STATUS=0')
    control_checks[scope] = {'sandbox_build_and_export':True,'four_invalid_options_rejected':True,
                            'three_actual_kernel_controls':True,'five_comparator_controls':True,
                            'sorry_and_native_axioms_rejected':True}

comparison=(logs/'comparator.log').read_text()
assert comparison.index('Building Challenge') < comparison.index('Building Solution')
for phase in ['Challenge','Solution']:
    exports=re.findall(r'Exporting #\[([^\n]+)\] from '+phase,comparison)
    assert len(exports)==1
    actual=[name for name in exports[0].split(', ') if name.startswith('NLA.MI07.')]
    assert actual == config['theorem_names']
assert comparison.count('warning: Challenge.lean:') == 7
assert not re.search(r'warning: (Solution|NLA/MI07/)',comparison)
axioms=re.findall(r"'(NLA\.MI07\.[^']+)' depends on axioms: \[([^\]]+)\]",comparison)
assert len(axioms)==23 and len(set(name for name,_ in axioms))==23
assert all(set(values.split(', '))==STANDARD for _,values in axioms)
assert comparison.count('Running Lean default kernel on solution.') == 1
assert comparison.count('Lean default kernel accepts the solution') == 1
assert comparison.count('Your solution is okay!') == 1
assert comparison.rstrip().endswith('EXIT_STATUS=0')
assert 'strict_landrun.py' in comparison and 'RestrictAddressFamilies=~AF_UNIX' in comparison

manifest=json.loads(blob(result['project']+'/lake-manifest.json'))
dependencies=(logs/'dependencies.log').read_text()
for package in manifest['packages']:
    assert f"info: {package['name']}: cloning {package['url']}" in dependencies
    assert f"info: {package['name']}: checking out revision '{package['rev']}'" in dependencies
assert len(manifest['packages']) == 10
cache=(logs/'mathlib-cache.log').read_text()
assert '$ lake exe cache get' in cache and 'Decompressed 8690 file(s)' in cache
assert cache.rstrip().endswith('EXIT_STATUS=0')

audit={'verdict':'PASS: independently audited actual Linux execution and source identity',
       'run':run['id'],'commit':COMMIT,'job':selected['id'],'artifacts':artifact_records,
       'input_files_matched_to_git_and_local_bytes':len(result['input_sha256']),
       'author_frozen_files_matched':len(precheck['frozen_files_at_commit']),
       'final_review_sha256':precheck['final_review_sha256'],'source_lock_sha256':lock_hash,
       'locked_checker_sources':len(precheck['all_locked_sources']),
       'tool_receipt':receipt,'controls':control_checks,'seven_compared_exports':config['theorem_names'],
       'axiom_audits':dict(axioms),'default_kernel_replay_accepted':True,
       'fresh_pinned_dependency_clones':10,'mathlib_cache_files_decompressed':8690,
       'cache_disclosure':'Pinned Mathlib binary cache was downloaded. Project Definitions, FunctionalCalculus, Proof and Solution built freshly. Exported declaration closure was replayed by the default Lean kernel. Not a source rebuild of every dependency.',
       'scope':'Remote Linux run audited locally from original ZIPs, metadata, receipts and logs. No local Linux rerun or independent second kernel. English-to-Lean correspondence relies on the two separately retained source-bound final reviews.'}
(OUT/'AUDIT-CHECKS.json').write_text(json.dumps(audit,indent=2)+'\n')
print(json.dumps({'verdict':'PASS','run':run['id'],'inputs':len(result['input_sha256']),
                  'exports':len(config['theorem_names']),'axiom_audits':len(axioms),
                  'fresh_dependency_clones':10,'both_original_zips_verified':True}))
