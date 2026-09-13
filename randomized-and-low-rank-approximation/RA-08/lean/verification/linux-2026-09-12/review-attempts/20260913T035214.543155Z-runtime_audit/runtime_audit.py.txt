"""Independent RA-08 actual Ubuntu runtime audit by /root/mf16_final_referee.
Common raw-control logic adapted from /root/leancert_examples IS03 audit, which
retains earlier campaign/standards attribution. No additional math referee,
local Linux assertion, Lean run, cache operation, or candidate mutation.
"""
from pathlib import Path,PurePosixPath
import hashlib,json,re,zipfile
OUT=Path(__file__).resolve().parent
CTX=json.loads((OUT/'context.json').read_text())
B=json.loads((OUT/'source-binding.json').read_text())
WT=Path(CTX['worktree']).resolve();P=WT/CTX['project']
COMMIT=CTX['commit'];RUN=CTX['run']
vs=list((OUT/'artifacts/lean-RA-08').glob('verify-*'))
ss=list((OUT/'artifacts/lean-checker-controls').glob('selftest-*'))
assert len(vs)==len(ss)==1
V,S=vs[0],ss[0]
def sha(data):return hashlib.sha256(data).hexdigest()
def save(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
receipt=json.loads((V/'result.json').read_text())
assert receipt['repository_commit']==COMMIT and receipt['project']==CTX['project']
assert receipt['result']=='comparator-accepted' and receipt['semantic_review']=='not-performed-by-this-command'
assert receipt['input_sha256']=={n:r['sha256'] for n,r in B['candidate_inputs'].items()}
assert len(receipt['input_sha256'])==613
for n,h in receipt['input_sha256'].items():assert sha((P/n).read_bytes())==h,n
assert receipt['config']==B['config']
config=receipt['config'];names=config['theorem_names']
assert len(names)==14
assert receipt['source_lock_sha256']==receipt['tool_receipt']['source_lock_sha256']==B['source_lock_sha256']
assert receipt['tool_receipt']['forsythe_commit']=='8d1b0c0545a77b40245e84705aa7d273e6c81e62'
assert receipt['tool_receipt']['ci_sandbox_probe_sha256']==B['derived_ci_probe_sha256']
assert '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in receipt['tool_receipt']['lean_version']
assert receipt['tool_receipt']['platform']=='Linux-6.17.0-1022-azure-x86_64-with-glibc2.39'
assert receipt['tool_receipt']['go_version']=='go version go1.27.1 linux/amd64'
assert len(receipt['tool_receipt']['executables'])==3
locked_source_count=B['locked_checker_sources']

assert receipt['tool_receipt']['lean_toolchain'] == 'leanprover/lean4:v4.33.1'
assert 'x86_64-unknown-linux-gnu' in receipt['tool_receipt']['lean_version']
assert receipt['tool_receipt']['platform'].startswith('Linux-')
assert locked_source_count == 58

controls = {}
for label, directory in [('checker-controls', S), ('RA-08 controls', V)]:
    sandbox = (directory / 'sandbox.log').read_text()
    for mode in ['build', 'export']:
        assert f'MODE {mode}: exit=0' in sandbox
    for kind in ['user', 'pid', 'mnt', 'net', 'ipc', 'uts']:
        assert sandbox.count(f'PASS {kind} namespace: private') == 2
    for marker in ['PASS outside .lake write-open: denied errno=30',
                   'PASS outside .lake truncate: denied errno=30',
                   'PASS outside .lake read-only truncate-open: denied errno=30',
                   'PASS symlink from .lake to outside write: denied errno=30',
                   'PASS outside .lake creation: denied errno=30',
                   'PASS host parent: absent from private /proc',
                   'PASS host parent signal lookup: denied errno=3',
                   'PASS host loopback listener: unreachable errno=13',
                   'PASS AF_UNIX socket creation: denied errno=97',
                   'PASS effective capabilities: none', 'PASS no_new_privs: set', 'bwrap: setting up uid map: Permission denied']:
        assert sandbox.count(marker) == 2, (label, marker)
    uids = [int(x) for x in re.findall(r'Sandbox UID: (\d+)', sandbox)]
    assert len(uids) == 2 and all(x > 0 for x in uids)
    for marker in ['PASS build .lake write: allowed', 'PASS export .lake write-open: denied errno=30',
                   'PASS export .lake truncate: denied errno=30',
                   'Outer and export fixture contents unchanged; only designated build fixture written.']:
        assert marker in sandbox
    for case in ['unknown option', 'unexpected --rw', 'unexpected --rwx', 'relative --rwx']:
        assert f'NEGATIVE {case}: exit=2' in sandbox
    kernel = (directory / 'kernel-controls.log').read_text()
    for marker in ['RETURN honest_with_inductives_and_quotients: accepted',
                   'RETURN invalid_raw_proof: rejected:', 'Quotient post-check rejects the solution',
                   'RETURN quotient_postcheck_mismatch: rejected: Quotient constant mismatch on: Quot.lift',
                   'PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']:
        assert marker in kernel
    comparator = (directory / 'comparator-controls.log').read_text()
    for case, code in [('simple_match', 0), ('simple_mismatch', 1), ('simple_axiom_issue', 1),
                       ('simple_kind_mismatch', 1), ('type_mismatch', 1)]:
        assert f'PASS {case}: exit {code}, expected {code}' in comparator
    phases = {
        'simple_match': 'Your solution is okay!',
        'simple_mismatch': "Challenge and solution constant kind don't match: 'comm'",
        'simple_axiom_issue': "Illegal axiom detected: 'helper'",
        'simple_kind_mismatch': "Illegal axiom detected: 'helper'",
        'type_mismatch': "Challenge and solution theorem statement do not match: 'checked'"}
    for case, phase in phases.items():
        block = comparator.split('\nCASE ' + case + '\n', 1)[1].split('\nCASE ', 1)[0]
        assert phase in block and ('required phase: ' + phase) in block
        assert block.count('Building Challenge') == block.count('Building Solution') == 1
        assert block.count('Exporting #[') == 2
    match_block = comparator.split('\nCASE simple_match\n', 1)[1].split('\nCASE ', 1)[0]
    assert 'Running Lean default kernel on solution.' in match_block
    assert 'Lean default kernel accepts the solution' in match_block
    assert comparator.count('Building Challenge') == comparator.count('Building Solution') == 5
    assert comparator.count('Exporting #[') == 10
    for log, axiom in [('negative-sorry.log', 'sorryAx'),
                       ('negative-native.log', 'checked._native.native_decide.ax_1_1')]:
        text = (directory / log).read_text()
        assert 'Building Challenge' in text and 'Building Solution' in text
        assert text.count('Exporting #[') == 2
        assert f"Illegal axiom detected: '{axiom}'" in text
        assert text.rstrip().endswith('EXIT_STATUS=1')
    for log in ['sandbox.log', 'kernel-controls.log', 'comparator-controls.log', 'user-service.log']:
        assert (directory / log).read_text().rstrip().endswith('EXIT_STATUS=0')
    controls[label] = {'actual_sandbox_modes': 2, 'sandbox_option_rejections': 4,
        'actual_raw_kernel_cases': 3, 'actual_comparator_fixtures': 5, 'actual_axiom_rejections': 2,
        'nested_bwrap_scope': 'Executable ran; UID-map creation was denied before the inner write.'}

main = (V / 'comparator.log').read_text()
main_command = main.splitlines()[0]
assert main_command.startswith('$ systemd-run --user ')
for marker in ['--wait --pipe --collect', 'RestrictAddressFamilies=~AF_UNIX', '/usr/bin/env -i ',
               'COMPARATOR_LANDRUN=', '/scripts/strict_landrun.py', 'COMPARATOR_LEAN4EXPORT=',
               'GIT_CONFIG_GLOBAL=/dev/null', ' comparator.json']:
    assert marker in main_command, marker
assert '--skip-kernel' not in main_command
fresh_project = re.search(r'--working-directory (\S+)', main_command).group(1)
assert '/.verification-tmp/nla-fresh-proof-' in fresh_project and fresh_project.endswith('/project')
assert main.count('Exporting #[') == 2
assert main.count('Building Challenge') == main.count('Building Solution') == 1
for module in ['Definitions','Basis','Certificate','Fourth','Functional','Location','Numerical','OrderedExistence','Polynomial','ProjectionNorm','Proof','Scalar','Spectral','SpectralCFC','Tails','Witness']:
    assert 'Built NLA.RA08.' + module in main
build_jobs = [int(value) for value in re.findall(r'Build completed successfully \((\d+) jobs\)\.', main)]
assert len(build_jobs) == 2 and all(n > 0 for n in build_jobs)
assert main.split('Building Solution', 1)[0].count('declaration uses `sorry`') == len(names)
assert 'warning:' not in main.split('Building Solution', 1)[1]
for name in config['theorem_names']:
    assert main.count(name) >= 3
axiom_records = re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]", main)
assert len(axiom_records) == main.count('depends on axioms:') == 59
assert len({name for name, _ in axiom_records}) == len(axiom_records)
assert all([value.strip() for value in axioms.split(',')] == config['permitted_axioms']
           for _, axioms in axiom_records)
for marker in ['Running Lean default kernel on solution.', 'Lean default kernel accepts the solution',
               'Your solution is okay!']:
    assert marker in main
assert main.rstrip().endswith('EXIT_STATUS=0')
save('axiom-verification.json', {'result': 'PASS', 'count': len(axiom_records),
    'declarations': {name: [value.strip() for value in axioms.split(',')] for name, axioms in axiom_records}})

manifest = json.loads((P / 'lake-manifest.json').read_text())
deps = (V / 'dependencies.log').read_text()
assert {p['name'] for p in manifest['packages']} >= {'leancert', 'mathlib'}
for package in manifest['packages']:
    assert f"{package['name']}: cloning " in deps
    assert f"{package['name']}: checking out revision '{package['rev']}'" in deps
assert deps.rstrip().endswith('EXIT_STATUS=0')
cache = (V / 'mathlib-cache.log').read_text()
cache_counts = re.findall(r'^Decompressed (\d+) file\(s\)', cache, re.M)
assert len(cache_counts) == 1 and int(cache_counts[0]) > 0 and cache.rstrip().endswith('EXIT_STATUS=0')
cache_count = int(cache_counts[0])
standalone = json.loads((S / 'result.json').read_text())
assert standalone['result'] == 'checker-selftest-passed'
assert standalone['mathematical_verification'] == 'none; checker fixtures only'
assert standalone['tool_receipt'] == receipt['tool_receipt']
for label in ['lean-RA-08', 'lean-checker-controls']:
    bootstrap = OUT / 'artifacts' / label / 'bootstrap'
    for log in ['comparator-build.log', 'elan.log', 'landrun-build.log']:
        assert (bootstrap / log).read_text().rstrip().endswith('EXIT_STATUS=0')
    for marker in ['Built comparator:exe', 'Built lean4export:exe']:
        assert marker in (bootstrap / 'comparator-build.log').read_text()



assert build_jobs==[2710,3161]
assert len(manifest['packages'])==10 and cache_count==8690
export_lists=re.findall(r'Exporting #\[(.*?)\] from (Challenge|Solution)',main)
assert len(export_lists)==2 and [m for _,m in export_lists]==['Challenge','Solution']
for text,module in export_lists:
    assert [v.strip() for v in text.split(',') if v.strip().startswith('NLA.RA08.')]==names
source_assertions=[n for r in B['source_trust_scan'].values() for n in r['kernel_assertions']]
assert len(source_assertions)==59
for name in source_assertions:assert sum(n.endswith('NLA.RA08.'+name) for n,_ in axiom_records)==1,name
for d in [V,S]:
    assert re.findall(r'Sandbox UID: (\d+)',(d/'sandbox.log').read_text())==['1001','1001']
    k=(d/'kernel-controls.log').read_text()
    assert '(kernel) declaration type mismatch' in k and '  True' in k and '  False' in k
    assert k.count('Running Lean default kernel on solution.')==3
    assert k.count('Lean default kernel accepts the solution')==2
def normalized(s):
    s=re.sub(r'\b[0-9a-f]{32}\b','INVOCATION',s)
    s=re.sub(r'\([0-9.]+[m]?s\)','(TIME)',s)
    s=re.sub(r'((?:Service runtime|CPU time consumed|Memory peak|Memory swap peak): ).*',r'\1RESOURCE',s)
    return re.sub(r'nla-axiom-[a-z0-9_]+','nla-axiom-FRESH',s)
correspondence={}
for n in ['sandbox.log','kernel-controls.log','comparator-controls.log','negative-native.log','negative-sorry.log','user-service.log']:
    a,b=(V/n).read_text(),(S/n).read_text()
    assert normalized(a)==normalized(b),n
    correspondence[n]={'project_sha256':sha((V/n).read_bytes()),'standalone_sha256':sha((S/n).read_bytes()),'complete_normalized_sha256':sha(normalized(a).encode())}
selected=OUT/'retrieval/selected'
run=json.loads((selected/'run.json').read_text())
J=json.loads((selected/'jobs.json').read_text());jobs=J['jobs']
assert run['head_sha']==COMMIT and run['status']=='completed' and run['conclusion']=='success'
assert len(jobs)==J['total_count']==17
assert all(j['status']=='completed' and j['conclusion']=='success' for j in jobs)
assert all(s['status']=='completed' and s['conclusion']=='success' for j in jobs for s in j['steps'])
pages={}
for label,key in [('jobs','jobs'),('artifacts','artifacts'),('permanent-id-jobs','jobs')]:
    combined=json.loads((selected/(label+'.json')).read_text());values=[]
    for i in range(1,combined['source_pages']+1):
        page=json.loads((selected/f'{label}-page-{i}.json').read_text());values+=page[key]
    assert combined[key]==values and len(values)==combined['total_count']==page['total_count']
    assert len({v['id'] for v in values})==len(values)
    pages[label]={'pages':combined['source_pages'],'count':len(values),'complete_original_page_identity':True}
chosen=[j for j in jobs if j['name'] in ['select','checker-controls'] or j['name'].startswith('verify (RA-08,')]
assert len(chosen)==3
workflow={}
for j in chosen:
    f=OUT/f"job-{j['id']}.log";raw=f.read_text()
    assert COMMIT in raw and '##[error]' not in raw
    assert 'Ubuntu2404-Readme.md' in raw and 'Version: 20260907.300.1' in raw
    assert '--skip-kernel' not in raw
    if j['name']!='select':
        for marker in ['sudo apt-get update','bubblewrap','uid','ulimit -n 65536','tools/lean/bootstrap.sh','$RUNNER_TEMP/nla-lean-tools']:
            assert marker in raw,(j['name'],marker)
    workflow[str(j['id'])]={'name':j['name'],'raw_log_sha256':sha(f.read_bytes()),'steps':j['steps'],
      'phase_lines':[s for s in raw.splitlines() if any(t in s for t in ['##[group]Run ','Ubuntu2404-Readme.md','SHA256 digest of uploaded','Artifact ID','Manifest schema and comparator coverage:'])]}
pj=next(j for j in chosen if j['name'].startswith('verify (RA-08,'))
assert 'Manifest schema and comparator coverage: PASS (14 declarations)' in (OUT/f"job-{pj['id']}.log").read_text()
archive_checks=[]
for item in json.loads((selected/'artifacts.json').read_text())['artifacts']:
    if item['name'] not in ['lean-RA-08','lean-checker-controls']:continue
    f=OUT/(item['name']+'.zip');data=f.read_bytes()
    assert item['digest']=='sha256:'+sha(data)
    assert not item['expired'] and item['workflow_run']['head_sha']==COMMIT
    target=OUT/'artifacts'/item['name'];members={}
    with zipfile.ZipFile(f) as z:
        assert z.testzip() is None and len(z.namelist())==len(set(z.namelist()))
        for info in z.infolist():
            n=PurePosixPath(info.filename)
            assert not n.is_absolute() and '..' not in n.parts
            assert (info.external_attr>>16)&0o170000!=0o120000
            if info.is_dir():continue
            assert z.read(info)==(target/n).read_bytes()
            members[info.filename]={'sha256':sha(z.read(info)),'bytes':info.file_size}
    assert set(members)=={str(f.relative_to(target)) for f in target.rglob('*') if f.is_file()}
    j=pj if item['name']=='lean-RA-08' else next(j for j in chosen if j['name']=='checker-controls')
    raw=(OUT/f"job-{j['id']}.log").read_text()
    assert 'SHA256 digest of uploaded artifact zip is '+sha(data) in raw and f"Artifact ID {item['id']}" in raw
    archive_checks.append({'name':item['name'],'id':item['id'],'zip_sha256':sha(data),'zip_bytes':len(data),'file_count':len(members),
      'GitHub_metadata_actual_upload_job_and_original_bytes_agree':True,'complete_extracted_files':members})
assert len(archive_checks)==2
ids=json.loads((selected/'permanent-id-run.json').read_text())
idjobs=json.loads((selected/'permanent-id-jobs.json').read_text())['jobs']
assert ids['head_sha']==COMMIT and ids['status']=='completed' and ids['conclusion']=='success'
assert len(idjobs)==1
for j in idjobs:
    assert j['conclusion']=='success' and all(s['conclusion']=='success' for s in j['steps'])
    raw=(OUT/f"permanent-id-job-{j['id']}.log").read_text()
    assert COMMIT in raw and '##[error]' not in raw
    assert 'Validated 217 permanent problem IDs' in raw and 'Ran 17 tests' in raw and 'OK' in raw
whole=json.loads((OUT/'whole-run-verification.json').read_text())
assert whole['whole_job_count']==17 and whole['archive_file_count']==217
assert whole['archive_sha256']==sha((OUT/'run-logs.zip').read_bytes())
save('runtime-verification.json',{'result':'PASS independent actual Ubuntu operational checks',
 'candidate':COMMIT,'run':RUN,'whole_workflow_jobs':17,'whole_workflow_all_steps_successful':True,
 'candidate_source_inputs_matched_to_actual_receipt':613,'actual_exports':names,
 'default_kernel_replay':'accepted','statement_comparator':'accepted','actual_standard_three_axiom_reports':59,
 'actual_main_command':main_command,'fresh_project':fresh_project,'challenge_graph_jobs':build_jobs[0],'solution_graph_jobs':build_jobs[1],
 'actual_tool_receipt':receipt['tool_receipt'],'all_58_checker_sources_and_exact_derived_probe_bound':True,
 'artifact_identity_checks':archive_checks,'complete_metadata_page_checks':pages,
 'actual_control_checks':controls,'actual_UIDs':[1001,1001],'complete_control_text_correspondence':correspondence,
 'normalization_scope':'Only invocation IDs, fresh axiom directory names, elapsed times and resource measurements; commands, phases, errors, fixture labels and outcomes remain.',
 'workflow_checks':workflow,'fresh_dependency_pins':manifest['packages'],'official_matching_Mathlib_cache_files':cache_count,
 'dependency_scope':'Fresh project proof compilation with official matching dependency objects; not a from-source rebuild of all Mathlib.',
 'permanent_ID_run':CTX['permanent_id_run'],'permanent_ID_tests':17,'all_217_ID_paths_validated':True,
 'whole_run_original_log_files':217,'other_project_semantic_audits_claimed':False,'coordinator_acceptance_and_publication':'pending'})
print(json.dumps({'result':'PASS actual Ubuntu runtime audit','all_jobs':17,'candidate_inputs':613,'exports':14,
 'actual_standard_three_reports':59,'kernel_replay':'accepted','Comparator':'accepted','actual_control_runs':2}))
