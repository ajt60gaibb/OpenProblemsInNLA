"""MI-06 independent operational checks by /root/leancert_examples.
Mechanical assertions adapt the prior MI-29 audit by /root/formal_review_standards;
this script supplements the independent reading of actual MI-06 raw logs.
It performs read-only source/receipt checks and writes only audit records.
"""
from pathlib import Path
import hashlib, json, re, subprocess, zipfile
OUT=Path(__file__).resolve().parent
WT=Path('/tmp/nla-lean-mi06-worktree')
COMMIT='43b3dc65116633a68c32ec582fd093f3adc95597'
PROJECT='matrix-inequalities-and-norms/MI-06/lean'
V=next((OUT/'artifacts/lean-MI-06').glob('verify-*'))
S=next((OUT/'artifacts/lean-checker-controls').glob('selftest-*'))
def sha(b): return hashlib.sha256(b).hexdigest()
def git(*args): return subprocess.check_output(['git','-C',str(WT),*args])
def save(name,data): (OUT/name).write_text(json.dumps(data,indent=2)+'\n')
r=json.loads((V/'result.json').read_text())
assert r['repository_commit']==COMMIT and r['project']==PROJECT and r['result']=='comparator-accepted'
assert git('rev-parse','HEAD').decode().strip()==COMMIT
tracked={x[len(PROJECT)+1:] for x in git('ls-tree','-r','--name-only',COMMIT,'--',PROJECT).decode().splitlines()}
assert len(tracked)==117
assert tracked==set(r['input_sha256']), (tracked-set(r['input_sha256']),set(r['input_sha256'])-tracked)
for rel,digest in r['input_sha256'].items():
 b=git('show',f'{COMMIT}:{PROJECT}/{rel}')
 assert sha(b)==digest and (WT/PROJECT/rel).read_bytes()==b, rel
frozen=['NLA/MI06/Definitions.lean','Challenge.lean','NUMERICAL_TARGETS.md','NLA/MI06/Proof.lean','Solution.lean']
for ref in ['reviews/proof-referee-1.md','reviews/proof-referee-2.md']:
 report=(WT/PROJECT/ref).read_text()
 for rel in frozen:
  assert r['input_sha256'][rel] in report,(ref,rel)
config=json.loads(git('show',f'{COMMIT}:{PROJECT}/comparator.json'))
assert config==r['config']
assert config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
assert config['definition_names']==[] and len(config['theorem_names'])==6
lock=git('show',f'{COMMIT}:tools/lean/source-lock.json')
assert sha(lock)==r['source_lock_sha256']==r['tool_receipt']['source_lock_sha256']
assert not git('diff','--name-only','8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc',COMMIT,'--','tools/lean','.github/workflows/lean-verification.yml','docs/lean/ci-toolchain')
for f in ['tools/lean/harness.py','tools/lean/source-lock.json','tools/lean/bootstrap.sh','tools/lean/selftest.sh','tools/lean/verify.sh']:
 assert git('show',f'214c142d6bfe0f0c338808f188062acbbad0fb19:{f}')==git('show',f'{COMMIT}:{f}')
run=json.loads((OUT/'run-metadata.json').read_text())
assert run['head_sha']==COMMIT and run['status']=='completed' and run['conclusion']=='success' and run['id']==34711237623
jobs=json.loads((OUT/'jobs.json').read_text())['jobs']
assert len(jobs)==7 and all(j['status']=='completed' and j['conclusion']=='success' for j in jobs)
assert all(s['conclusion']=='success' for j in jobs for s in j['steps'])
archives=[]
for a in json.loads((OUT/'artifact-metadata.json').read_text())['artifacts']:
 if a['name'] not in {'lean-MI-06','lean-checker-controls'}: continue
 z=OUT/(a['name']+'.zip')
 assert sha(z.read_bytes())==a['digest'].removeprefix('sha256:')
 assert a['workflow_run']['head_sha']==COMMIT
 with zipfile.ZipFile(z) as arc:
  names={f.filename for f in arc.infolist() if not f.is_dir()}
  extracted=OUT/'artifacts'/a['name']
  assert names=={str(p.relative_to(extracted)) for p in extracted.rglob('*') if p.is_file()}
  for n in names: assert arc.read(n)==(extracted/n).read_bytes()
 archives.append({'name':a['name'],'id':a['id'],'sha256':sha(z.read_bytes()),'file_count':len(names)})
controls={}
for label,d in [('checker-controls',S),('MI-06 controls',V)]:
 sandbox=(d/'sandbox.log').read_text()
 for mode in ['build','export']: assert f'MODE {mode}: exit=0' in sandbox
 for ns in ['user','pid','mnt','net','ipc','uts']: assert sandbox.count(f'PASS {ns} namespace: private')==2
 for marker in ['PASS outside .lake write-open: denied errno=30','PASS outside .lake truncate: denied errno=30','PASS outside .lake read-only truncate-open: denied errno=30','PASS host parent: absent from private /proc','PASS host parent signal lookup: denied errno=3','PASS symlink from .lake to outside write: denied errno=30','PASS outside .lake creation: denied errno=30','PASS host loopback listener: unreachable errno=13','PASS AF_UNIX socket creation: denied errno=97','PASS effective capabilities: none','PASS no_new_privs: set','Sandbox UID: 1001','bwrap: setting up uid map: Permission denied']: assert sandbox.count(marker)==2,marker
 for marker in ['PASS build .lake write: allowed','PASS export .lake write-open: denied errno=30','PASS export .lake truncate: denied errno=30','Outer and export fixture contents unchanged; only designated build fixture written.']: assert marker in sandbox
 for case in ['unknown option','unexpected --rw','unexpected --rwx','relative --rwx']: assert f'NEGATIVE {case}: exit=2' in sandbox
 kernel=(d/'kernel-controls.log').read_text()
 for marker in ['RETURN honest_with_inductives_and_quotients: accepted','RETURN invalid_raw_proof: rejected:','Quotient post-check rejects the solution','RETURN quotient_postcheck_mismatch: rejected: Quotient constant mismatch on: Quot.lift','PASS: all three actual Comparator.runBuiltinKernel cases behaved as required']: assert marker in kernel
 comps=(d/'comparator-controls.log').read_text()
 for case,code in [('simple_match',0),('simple_mismatch',1),('simple_axiom_issue',1),('simple_kind_mismatch',1),('type_mismatch',1)]: assert f'PASS {case}: exit {code}, expected {code}' in comps
 assert comps.count('Building Challenge')==5 and comps.count('Building Solution')==5 and comps.count('Exporting #[')==10
 for log,axiom in [('negative-sorry.log','sorryAx'),('negative-native.log','checked._native.native_decide.ax_1_1')]:
  t=(d/log).read_text()
  assert 'Building Challenge' in t and 'Building Solution' in t and t.count('Exporting #[')==2
  assert f"Illegal axiom detected: '{axiom}'" in t and t.rstrip().endswith('EXIT_STATUS=1')
 for log in ['sandbox.log','kernel-controls.log','comparator-controls.log','user-service.log']: assert (d/log).read_text().rstrip().endswith('EXIT_STATUS=0')
 controls[label]={'sandbox_modes':2,'sandbox_negative_options':4,'kernel_replay_cases':3,'comparator_cases':5,'axiom_negative_controls':2,'all_actual_required_phases_observed':True,'nested_bwrap_scope':'Executable ran; UID-map creation denied before inner write.'}
main=(V/'comparator.log').read_text()
assert main.count('Exporting #[')==2 and 'Built NLA.MI06.Definitions' in main and 'Built NLA.MI06.Proof' in main
build_jobs=[int(n) for n in re.findall(r'Build completed successfully \((\d+) jobs\)\.',main)]
assert len(build_jobs)==2 and all(n>1000 for n in build_jobs)
assert main.split('Building Solution',1)[0].count('declaration uses `sorry`')==6
for name in config['theorem_names']: assert main.count(name)>=3
# Lean wraps long private declaration names across physical log lines.
# Parse each complete bracketed axiom list, preserving exact names and order.
axiom_records=re.findall(r"'([^'\n]+)' depends on axioms: \[([^\]]*)\]",main)
assert len(axiom_records)==52 and main.count('depends on axioms:')==52
assert len({name for name,_ in axiom_records})==52
assert all([x.strip() for x in names.split(',')]==['propext','Classical.choice','Quot.sound'] for _,names in axiom_records)
save('axiom-verification.json',{'declarations':{name:[x.strip() for x in names.split(',')] for name,names in axiom_records},'count':52,'verdict':'PASS'})
for marker in ['Running Lean default kernel on solution.','Lean default kernel accepts the solution','Your solution is okay!']: assert marker in main
assert main.rstrip().endswith('EXIT_STATUS=0')
assert 'warning:' not in main.split('Building Solution',1)[1]
manifest=json.loads((WT/PROJECT/'lake-manifest.json').read_text())
deps=(V/'dependencies.log').read_text()
for pkg in manifest['packages']: assert pkg['rev'] in deps,pkg['name']
assert len(manifest['packages'])==10 and deps.rstrip().endswith('EXIT_STATUS=0')
cache=(V/'mathlib-cache.log').read_text()
assert 'Decompressed 8690 file(s)' in cache and cache.rstrip().endswith('EXIT_STATUS=0')
standalone_receipt=json.loads((S/'result.json').read_text())
assert standalone_receipt['result']=='checker-selftest-passed'
assert standalone_receipt['mathematical_verification']=='none; checker fixtures only'
assert standalone_receipt['tool_receipt']==r['tool_receipt']
for label in ['lean-MI-06','lean-checker-controls']:
 bootstrap=OUT/'artifacts'/label/'bootstrap'
 for log in ['comparator-build.log','elan.log','landrun-build.log']:
  assert (bootstrap/log).read_text().rstrip().endswith('EXIT_STATUS=0')
 assert 'Built lean4export:exe' in (bootstrap/'comparator-build.log').read_text()
 assert 'Built comparator:exe' in (bootstrap/'comparator-build.log').read_text()
for jobid,artifactid,digest in [(103600321907,10303710574,'28dbe65ba6c0f4f727a8b5bf631d380fa4f9ff930831a0949b56e5db14152d0d'),(103600321902,10303422365,'51559d0cf43a7ae30c71b44711e6264aa180f8bc870a3bbbb6d4447ebadabc2e')]:
 raw=(OUT/f'job-{jobid}.log').read_text()
 assert COMMIT in raw and f'SHA256 digest of uploaded artifact zip is {digest}' in raw
 assert f'Artifact ID {artifactid}' in raw and '##[error]' not in raw
assert 'Manifest schema and comparator coverage: PASS (6 declarations)' in (OUT/'job-103600321907.log').read_text()
assert (WT/PROJECT/'NLA/MI06/Proof.lean').read_text().count('#assert_trust kernel ')==46
assert (WT/PROJECT/'Solution.lean').read_text().count('#assert_trust kernel ')==6
for rel in ['.github/workflows/lean-verification.yml','tools/lean/harness.py','tools/lean/source-lock.json',PROJECT+'/comparator.json',PROJECT+'/lake-manifest.json',PROJECT+'/lakefile.toml',PROJECT+'/lean-toolchain',PROJECT+'/formalization.yaml',PROJECT+'/README.md']+[PROJECT+'/'+p for p in frozen]+[PROJECT+'/reviews/proof-referee-1.md',PROJECT+'/reviews/proof-referee-2.md']:
 dest=OUT/'source'/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(git('show',f'{COMMIT}:{rel}'))
save('identity-verification.json',{'verdict':'PASS','commit':COMMIT,'run':run['id'],'project':PROJECT,'input_files':r['input_sha256'],'exact_complete_git_tracked_input_set':True,'all_input_bytes_match_worktree_and_commit':True,'five_core_mathematical_hashes_match_both_referees':True,'actual_harness_and_source_lock_unchanged_since_audited_linux_commit':'214c142d6bfe0f0c338808f188062acbbad0fb19','complete_tools_and_workflow_match_recorded_upstream_base':'8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc','archives':archives,'all_jobs_and_steps_succeeded':True})
save('control-verification.json',{'verdict':'PASS','control_runs':controls,'theorem_names':config['theorem_names'],'permitted_axioms':config['permitted_axioms'],'axiom_print_count':52,'fresh_challenge_graph_jobs':build_jobs[0],'fresh_solution_graph_jobs':build_jobs[1],'fresh_dependency_clones':10,'mathlib_cache_files':8690,'default_kernel_replay':'accepted','statement_comparator':'accepted','no_solution_warnings':True})
print('PASS: complete 117-file input identity, both artifact ZIPs, both actual control sets, six exports, fresh source builds and kernel replay')
