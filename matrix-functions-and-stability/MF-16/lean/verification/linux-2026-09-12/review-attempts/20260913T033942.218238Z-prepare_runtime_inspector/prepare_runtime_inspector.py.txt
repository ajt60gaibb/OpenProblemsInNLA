"""Adapt the already inspected common IS03 raw-control checks for MF-16.
The complete exact template and this adaptation are retained. Candidate source
and mathematical binding are handled separately by source_audit.py.
"""
from pathlib import Path
import hashlib,json
O=Path(__file__).resolve().parent
T=Path('/tmp/nla-lean-is03-worktree/eigenvalues-and-inverse-problems/IS-03/lean/verification/linux-2026-09-12/audit_checks.py')
old=T.read_text()
(O/'source/IS03-runtime-template.py.txt').write_text(old)
(O/'ENOSPC-write-failure.json').write_text(json.dumps({
 'operation':'Initial apply_patch creation of runtime_audit.py',
 'raw_tool_result':'Script error: Exit code: 1; Failed to write file /tmp/nla-lean-mf16-worktree/matrix-functions-and-stability/MF-16/lean/verification/linux-2026-09-12/runtime_audit.py',
 'file_state_after_failure':'Absent; no partial script',
 'cause':'ENOSPC independently reported by coordinator; later free space 479284 KiB after coordinator cleanup',
 'candidate_or_raw_evidence_change':False,
 'recovery':'Write small operational inspector after headroom recovered; no Lean, dependency or artifact rerun'},indent=2)+'\n')
prefix=r'''"""Independent MF-16 actual Ubuntu runtime audit by /root/mf16_final_referee.
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
vs=list((OUT/'artifacts/lean-MF-16').glob('verify-*'))
ss=list((OUT/'artifacts/lean-checker-controls').glob('selftest-*'))
assert len(vs)==len(ss)==1
V,S=vs[0],ss[0]
def sha(data):return hashlib.sha256(data).hexdigest()
def save(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
receipt=json.loads((V/'result.json').read_text())
assert receipt['repository_commit']==COMMIT and receipt['project']==CTX['project']
assert receipt['result']=='comparator-accepted' and receipt['semantic_review']=='not-performed-by-this-command'
assert receipt['input_sha256']=={n:r['sha256'] for n,r in B['candidate_inputs'].items()}
assert len(receipt['input_sha256'])==294
for n,h in receipt['input_sha256'].items():assert sha((P/n).read_bytes())==h,n
assert receipt['config']==B['config']
config=receipt['config'];names=config['theorem_names']
assert len(names)==9
assert receipt['source_lock_sha256']==receipt['tool_receipt']['source_lock_sha256']==B['source_lock_sha256']
assert receipt['tool_receipt']['forsythe_commit']=='8d1b0c0545a77b40245e84705aa7d273e6c81e62'
assert receipt['tool_receipt']['ci_sandbox_probe_sha256']==B['derived_ci_probe_sha256']
assert '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in receipt['tool_receipt']['lean_version']
assert receipt['tool_receipt']['platform']=='Linux-6.17.0-1022-azure-x86_64-with-glibc2.39'
assert receipt['tool_receipt']['go_version']=='go version go1.27.1 linux/amd64'
assert len(receipt['tool_receipt']['executables'])==3
locked_source_count=B['locked_checker_sources']
'''
controls=old[old.index("assert receipt['tool_receipt']['lean_toolchain']"):old.index('implementation_paths =')]
controls=controls.replace('IS-03','MF-16').replace('IS03','MF16')
controls=controls.replace("['Definitions', 'Algebra', 'Spectral', 'Witness', 'Newton', 'Numerical', 'Proof']",
                          "['Definitions', 'Algebra', 'Recovery', 'Polynomial', 'CayleyHamilton', 'Numerical', 'Proof']")
controls=controls.replace("== 18","== 22")
deps=old[old.index("manifest = json.loads((WT / PROJECT"):old.index("for rel, expected in proof_freeze['source_files'].items():")]
deps=deps.replace('WT / PROJECT','P').replace('IS-03','MF-16')
suffix=r'''
assert build_jobs==[2840,2863]
assert len(manifest['packages'])==10 and cache_count==8690
export_lists=re.findall(r'Exporting #\[(.*?)\] from (Challenge|Solution)',main)
assert len(export_lists)==2 and [m for _,m in export_lists]==['Challenge','Solution']
for text,module in export_lists:
    assert [v.strip() for v in text.split(',') if v.strip().startswith('NLA.MF16.')]==names
source_assertions=[n for r in B['source_trust_scan'].values() for n in r['kernel_assertions']]
assert len(source_assertions)==22
for name in source_assertions:assert sum(n.endswith('NLA.MF16.'+name) for n,_ in axiom_records)==1,name
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
chosen=[j for j in jobs if j['name'] in ['select','checker-controls'] or j['name'].startswith('verify (MF-16,')]
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
pj=next(j for j in chosen if j['name'].startswith('verify (MF-16,'))
assert 'Manifest schema and comparator coverage: PASS (9 declarations)' in (OUT/f"job-{pj['id']}.log").read_text()
archive_checks=[]
for item in json.loads((selected/'artifacts.json').read_text())['artifacts']:
    if item['name'] not in ['lean-MF-16','lean-checker-controls']:continue
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
    j=pj if item['name']=='lean-MF-16' else next(j for j in chosen if j['name']=='checker-controls')
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
 'candidate_source_inputs_matched_to_actual_receipt':294,'actual_exports':names,
 'default_kernel_replay':'accepted','statement_comparator':'accepted','actual_standard_three_axiom_reports':22,
 'actual_main_command':main_command,'fresh_project':fresh_project,'challenge_graph_jobs':build_jobs[0],'solution_graph_jobs':build_jobs[1],
 'actual_tool_receipt':receipt['tool_receipt'],'all_58_checker_sources_and_exact_derived_probe_bound':True,
 'artifact_identity_checks':archive_checks,'complete_metadata_page_checks':pages,
 'actual_control_checks':controls,'actual_UIDs':[1001,1001],'complete_control_text_correspondence':correspondence,
 'normalization_scope':'Only invocation IDs, fresh axiom directory names, elapsed times and resource measurements; commands, phases, errors, fixture labels and outcomes remain.',
 'workflow_checks':workflow,'fresh_dependency_pins':manifest['packages'],'official_matching_Mathlib_cache_files':cache_count,
 'dependency_scope':'Fresh project proof compilation with official matching dependency objects; not a from-source rebuild of all Mathlib.',
 'permanent_ID_run':CTX['permanent_id_run'],'permanent_ID_tests':17,'all_217_ID_paths_validated':True,
 'whole_run_original_log_files':217,'other_project_semantic_audits_claimed':False,'coordinator_acceptance_and_publication':'pending'})
print(json.dumps({'result':'PASS actual Ubuntu runtime audit','all_jobs':17,'candidate_inputs':294,'exports':9,
 'actual_standard_three_reports':22,'kernel_replay':'accepted','Comparator':'accepted','actual_control_runs':2}))
'''
result=prefix+'\n'+controls+'\n'+deps+'\n'+suffix
(O/'runtime_audit.py').write_text(result)
(O/'runtime-inspector-adaptation.json').write_text(json.dumps({
 'template':'source/IS03-runtime-template.py.txt','template_sha256':hashlib.sha256(old.encode()).hexdigest(),
 'scope':'Unchanged substantive raw sandbox/kernel/Comparator negative-control logic, adapted namespace and MF16 source module/count identities; candidate binding separately audited',
 'namespaces':['IS03 -> MF16','IS-03 -> MF-16'],'embedded_axiom_count':'18 -> 22, independently established from exact MF16 source',
 'module_list':['Definitions','Algebra','Recovery','Polynomial','CayleyHamilton','Numerical','Proof'],
 'independent_operational_reviewer':'/root/mf16_final_referee','generated_runtime_inspector_sha256':hashlib.sha256(result.encode()).hexdigest()
},indent=2)+'\n')
print('Prepared actual MF16 runtime inspector with original common-control template and exact adaptation retained')
