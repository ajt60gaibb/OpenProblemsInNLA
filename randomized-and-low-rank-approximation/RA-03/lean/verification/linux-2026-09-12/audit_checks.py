from pathlib import Path
import hashlib, json, re, subprocess, zipfile
OUT=Path(__file__).resolve().parent
WT=Path('/tmp/nla-lean-ra03-worktree')
COMMIT='973f95969701601dcae7b30683b175843baa9c22'
PROJECT='randomized-and-low-rank-approximation/RA-03/lean'
V=OUT/'artifacts/lean-RA-03/verify-20260912T161438Z-4193'
S=OUT/'artifacts/lean-checker-controls/selftest-20260912T161435Z-3917'
def sha(b): return hashlib.sha256(b).hexdigest()
def git(*args): return subprocess.check_output(['git','-C',str(WT),*args])
def save(name,data): (OUT/name).write_text(json.dumps(data,indent=2)+'\n')
r=json.loads((V/'result.json').read_text())
assert r['repository_commit']==COMMIT and r['project']==PROJECT and r['result']=='comparator-accepted'
assert git('rev-parse','HEAD').decode().strip()==COMMIT
tracked={x[len(PROJECT)+1:] for x in git('ls-tree','-r','--name-only',COMMIT,'--',PROJECT).decode().splitlines()}
assert tracked==set(r['input_sha256']), (tracked-set(r['input_sha256']),set(r['input_sha256'])-tracked)
for rel,digest in r['input_sha256'].items():
 b=git('show',f'{COMMIT}:{PROJECT}/{rel}')
 assert sha(b)==digest and (WT/PROJECT/rel).read_bytes()==b, rel
frozen=['NLA/RA03/Definitions.lean','Challenge.lean','NUMERICAL_TARGETS.md','NLA/RA03/Proof.lean','Solution.lean']
for ref in ['reviews/proof-referee-1.md','reviews/proof-referee-2.md']:
 report=(WT/PROJECT/ref).read_text()
 for rel in frozen: assert r['input_sha256'][rel] in report,(ref,rel)
config=json.loads(git('show',f'{COMMIT}:{PROJECT}/comparator.json'))
assert config==r['config']
assert config['permitted_axioms']==['propext','Classical.choice','Quot.sound']
assert config['definition_names']==[] and len(config['theorem_names'])==4
lock=git('show',f'{COMMIT}:tools/lean/source-lock.json')
assert sha(lock)==r['source_lock_sha256']==r['tool_receipt']['source_lock_sha256']
assert not git('diff','--name-only','214c142d6bfe0f0c338808f188062acbbad0fb19',COMMIT,'--','tools/lean','.github/workflows/lean-verification.yml','docs/lean/ci-toolchain')
run=json.loads((OUT/'run-metadata.json').read_text())
assert run['head_sha']==COMMIT and run['conclusion']=='success' and run['id']==34704564047
jobs=json.loads((OUT/'jobs.json').read_text())['jobs']
assert len(jobs)==3 and all(j['conclusion']=='success' for j in jobs)
assert all(s['conclusion']=='success' for j in jobs for s in j['steps'])
archives=[]
for a in json.loads((OUT/'artifact-metadata.json').read_text())['artifacts']:
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
for label,d in [('checker-controls',S),('RA-03 controls',V)]:
 sandbox=(d/'sandbox.log').read_text()
 for mode in ['build','export']: assert f'MODE {mode}: exit=0' in sandbox
 for ns in ['user','pid','mnt','net','ipc','uts']: assert sandbox.count(f'PASS {ns} namespace: private')==2
 for marker in ['PASS outside .lake write-open: denied errno=30','PASS outside .lake truncate: denied errno=30','PASS symlink from .lake to outside write: denied errno=30','PASS outside .lake creation: denied errno=30','PASS host loopback listener: unreachable errno=13','PASS AF_UNIX socket creation: denied errno=97','PASS effective capabilities: none','PASS no_new_privs: set','Sandbox UID: 1001','bwrap: setting up uid map: Permission denied']: assert sandbox.count(marker)==2,marker
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
assert main.count('Exporting #[')==2 and 'Built NLA.RA03.Definitions' in main and 'Built NLA.RA03.Proof' in main
assert 'Build completed successfully (2723 jobs).' in main and 'Build completed successfully (3731 jobs).' in main
for name in config['theorem_names']: assert main.count(name)>=3
axiom_lines=[line for line in main.splitlines() if 'depends on axioms:' in line]
assert len(axiom_lines)==12
assert all(line.endswith('[propext, Classical.choice, Quot.sound]') for line in axiom_lines)
for marker in ['Running Lean default kernel on solution.','Lean default kernel accepts the solution','Your solution is okay!']: assert marker in main
assert main.rstrip().endswith('EXIT_STATUS=0')
assert 'warning:' not in main.split('Building Solution',1)[1]
manifest=json.loads((WT/PROJECT/'lake-manifest.json').read_text())
deps=(V/'dependencies.log').read_text()
for pkg in manifest['packages']: assert pkg['rev'] in deps,pkg['name']
assert len(manifest['packages'])==10 and deps.rstrip().endswith('EXIT_STATUS=0')
cache=(V/'mathlib-cache.log').read_text()
assert 'Decompressed 8690 file(s)' in cache and cache.rstrip().endswith('EXIT_STATUS=0')
assert json.loads((S/'result.json').read_text())['tool_receipt']==r['tool_receipt']
for rel in ['.github/workflows/lean-verification.yml','tools/lean/harness.py','tools/lean/source-lock.json',PROJECT+'/comparator.json',PROJECT+'/lake-manifest.json',PROJECT+'/lakefile.toml',PROJECT+'/lean-toolchain',PROJECT+'/formalization.yaml',PROJECT+'/README.md']+[PROJECT+'/'+p for p in frozen]+[PROJECT+'/reviews/proof-referee-1.md',PROJECT+'/reviews/proof-referee-2.md']:
 dest=OUT/'source'/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(git('show',f'{COMMIT}:{rel}'))
save('identity-verification.json',{'verdict':'PASS','commit':COMMIT,'run':run['id'],'project':PROJECT,'input_files':r['input_sha256'],'exact_complete_git_tracked_input_set':True,'all_input_bytes_match_worktree_and_commit':True,'frozen_mathematical_hashes_match_both_referees':True,'tool_harness_unchanged_since_independently_audited_linux_commit':'214c142d6bfe0f0c338808f188062acbbad0fb19','archives':archives,'all_jobs_and_steps_succeeded':True})
save('control-verification.json',{'verdict':'PASS','control_runs':controls,'theorem_names':config['theorem_names'],'permitted_axioms':config['permitted_axioms'],'axiom_print_count':12,'fresh_challenge_graph_jobs':2723,'fresh_solution_graph_jobs':3731,'fresh_dependency_clones':10,'mathlib_cache_files':8690,'default_kernel_replay':'accepted','statement_comparator':'accepted','no_solution_warnings':True})
print('PASS: complete 48-file input identity, both artifact ZIPs, both actual control sets, four exports, fresh source builds and kernel replay')
