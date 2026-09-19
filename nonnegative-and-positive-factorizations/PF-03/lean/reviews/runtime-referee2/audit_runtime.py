"""Independent read-only audit of completed PF03 GitHub artifacts; runs no proof tools."""
from pathlib import Path,PurePosixPath
import datetime,hashlib,json,re,subprocess,zipfile
O=Path(__file__).resolve().parent;D=O.parents[1]
W=D/'publication/PF03';E=D/'verification/PF03-linux-20260919'
FORSYTHE=Path('/Users/georgestepaniants/Research/Forsythe')
PROOF='9625a76780183040186664100e24e0e90d8fcc7d';MERGE='693e92b166d391507dd818687aea0b1ad92f1321'
PROJECT='nonnegative-and-positive-factorizations/PF-03/lean'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(repo,*args):return subprocess.check_output(['git',*args],cwd=repo)
def blob(path):return git(W,'show',PROOF+':'+path)
api=json.loads((O/'FRESH-GITHUB-OBSERVATIONS.json').read_text())
# GitHub's merge commit has the same entire tree as the actual published proof commit.
assert api['merge_commit']['sha']==MERGE
assert api['merge_commit']['parents']==['71563f17926cd826a892c2bba0e294894ee57a5c',PROOF]
assert api['merge_commit']['tree']==git(W,'rev-parse',PROOF+'^{tree}').decode().strip()
assert next(r for r in api['merge_pf03_directory'] if r['name']=='lean')['sha']==git(W,'rev-parse',PROOF+':'+PROJECT).decode().strip()
assert api['pull_request']['number']==303 and api['pull_request']['head_sha']==PROOF
paths=git(W,'ls-tree','-r','--name-only',PROOF,'--',PROJECT).decode().splitlines()
inputs={str(PurePosixPath(p).relative_to(PROJECT)):sha(blob(p)) for p in paths}
assert len(inputs)==234
# Match all active Lean inputs to this referee's independently reviewed source packet.
old=json.loads((D/'reviews/PF03-final-referee2/STATIC-AUDIT.json').read_text())
lean_inputs={p:h for p,h in inputs.items()
 if p in ['Challenge.lean','Solution.lean'] or (p.startswith('NLA/') and p.endswith('.lean'))}
assert len(lean_inputs)==61
assert all(old['all_packet_file_hashes'][p]==h for p,h in lean_inputs.items())
for p in ['comparator.json','NUMERICAL_TARGETS.md']:
 assert inputs[p]==old['all_packet_file_hashes'][p]
config=json.loads(blob(PROJECT+'/comparator.json'));names=config['theorem_names']
allowed={'propext','Classical.choice','Quot.sound'}
assert len(names)==25 and config['definition_names']==[] and set(config['permitted_axioms'])==allowed
lockbytes=blob('tools/lean/source-lock.json');lock=json.loads(lockbytes)
assert lock['commit']=='8d1b0c0545a77b40245e84705aa7d273e6c81e62'
assert lock['lean_toolchain']=='leanprover/lean4:v4.33.1'
for entry in lock['files']:
 data=git(FORSYTHE,'show',lock['commit']+':'+entry['source'])
 assert sha(data)==entry['sha256'] and len(data)==entry['bytes'],entry['source']
dependencies=json.loads(blob(PROJECT+'/lake-manifest.json'))['packages']
log_sources={};runs=[]
for k,(side,runid,jobid,artifactid,repo) in enumerate([
 ('fork',35424055075,105846873543,10578972769,'sgstepaniants/OpenProblemsInNLA'),
 ('upstream',35424087832,105846968481,10578567081,'ajt60gaibb/OpenProblemsInNLA')]):
 fresh=api['runs'][k];assert fresh['repository']==repo
 r=fresh['run'];assert r['id']==runid and r['head_sha']==PROOF and r['status']=='completed' and r['conclusion']=='success'
 jobs=fresh['jobs'];selected=[j for j in jobs if j['name'].startswith('verify (')]
 assert len(selected)==1
 job=selected[0];assert job['id']==jobid and job['status']=='completed' and job['conclusion']=='success'
 assert job['name']==f'verify (PF-03, {PROJECT})' and job['labels']==['ubuntu-24.04']
 step=next(s for s in job['steps'] if s['name']=='Fresh sandboxed statement, axiom and kernel verification')
 assert step['status']=='completed' and step['conclusion']=='success'
 a=next(x for x in fresh['artifacts'] if x['id']==artifactid)
 assert a['workflow_run']['id']==runid and a['workflow_run']['head_sha']==PROOF and not a['expired']
 assert a['name']=='lean-PF-03'
 B=E/side;zpath=B/'lean-PF-03.zip';zdata=zpath.read_bytes()
 assert 'sha256:'+sha(zdata)==a['digest'] and len(zdata)==a['size_in_bytes']
 member_hashes={}
 with zipfile.ZipFile(zpath) as z:
  assert z.testzip() is None
  members=[i for i in z.infolist() if not i.is_dir()]
  assert len(members)==len(set(i.filename for i in members))
  for i in members:
   n=PurePosixPath(i.filename);assert not n.is_absolute() and '..' not in n.parts
   raw=z.read(i);assert raw==(B/'artifact'/n).read_bytes()
   member_hashes[str(n)]=sha(raw)
 assert set(member_hashes)=={str(p.relative_to(B/'artifact')) for p in (B/'artifact').rglob('*') if p.is_file()}
 vs=list((B/'artifact').glob('verify*/result.json'));assert len(vs)==1
 R=vs[0];V=R.parent;result=json.loads(R.read_text())
 assert result['repository_commit']==(PROOF if side=='fork' else MERGE)
 assert result['project']==PROJECT and result['config']==config and result['input_sha256']==inputs
 assert result['result']=='comparator-accepted' and result['semantic_review']=='not-performed-by-this-command'
 assert result['source_lock_sha256']==sha(lockbytes)
 tr=result['tool_receipt'];assert tr['source_lock_sha256']==sha(lockbytes) and tr['forsythe_commit']==lock['commit']
 assert tr['lean_toolchain']==lock['lean_toolchain'] and 'x86_64-unknown-linux-gnu' in tr['lean_version']
 assert tr['platform'].startswith('Linux-') and tr['go_version']=='go version go1.27.1 linux/amd64'
 if runs:assert tr==runs[0]['tool_receipt']
 texts={p.name:p.read_text() for p in V.glob('*.log')}
 def need(file,code,*markers):
  t=texts[file];assert t.rstrip().endswith('EXIT_STATUS='+str(code)),file
  for marker in markers:assert marker in t,(file,marker)
 need('comparator.log',0,'Building Challenge','Building Solution','systemd-run --user','RestrictAddressFamilies=~AF_UNIX','COMPARATOR_LANDRUN=/home/runner/work/_temp/nla-lean-tools/scripts/strict_landrun.py','Running Lean default kernel on solution.','Lean default kernel accepts the solution','Your solution is okay!')
 t=texts['comparator.log'];assert t.count('[interval_decide] Dyadic certificate verified')==2
 assert len(re.findall(r'warning: Challenge\.lean:\d+:\d+: declaration uses `sorry`',t))==25
 assert not re.search(r'warning: (?!Challenge\.lean)[^\n]*declaration uses `sorry`',t)
 exported=re.findall(r'Exporting #\[(.*?)\] from (Challenge|Solution)',t)
 assert len(exported)==2
 for targets,which in exported:
  targetlist=targets.split(', ');assert [n for n in targetlist if n.startswith('NLA.PF03.')]==names
 reports={n:[] for n in names}
 for n,axtxt in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",t):
  ax=set(x.strip() for x in axtxt.split(',') if x.strip());assert ax<=allowed,(n,ax)
  if n in reports:reports[n].append(sorted(ax))
 assert all(reports.values())
 aggregate={n:ax.split(', ') for n,ax in re.findall(r"info: Solution\.lean:\d+:\d+: '([^']+)' depends on axioms: \[([^\]]*)\]",t)}
 assert set(aggregate)==set(names) and all(set(a)==allowed for a in aggregate.values())
 built=set(re.findall(r'Built (NLA\.PF03\.\w+) \(',t))
 assert len(built)==59
 need('kernel-controls.log',0,'RETURN honest_with_inductives_and_quotients: accepted','RETURN invalid_raw_proof: rejected','(kernel) declaration type mismatch','RETURN quotient_postcheck_mismatch: rejected','Quotient constant mismatch on: Quot.lift','PASS: all three actual Comparator.runBuiltinKernel cases behaved as required')
 need('comparator-controls.log',0,'PASS simple_match: exit 0, expected 0','PASS simple_mismatch: exit 1, expected 1','PASS simple_axiom_issue: exit 1, expected 1','PASS simple_kind_mismatch: exit 1, expected 1','PASS type_mismatch: exit 1, expected 1','PASS: all five Comparator regressions')
 need('negative-sorry.log',1,"Illegal axiom detected: 'sorryAx'")
 need('negative-native.log',1,"Illegal axiom detected: 'checked._native.native_decide.ax_1_1'")
 need('sandbox.log',0,'MODE build: exit=0','MODE export: exit=0','Outer and export fixture contents unchanged; only designated build fixture written.')
 sandbox=texts['sandbox.log'];assert re.findall(r'Sandbox UID: (\d+)',sandbox)==['1001','1001']
 for marker in ['outside .lake write-open: denied','outside .lake truncate: denied','outside .lake read-only truncate-open: denied','symlink from .lake to outside write: denied','outside .lake creation: denied','user namespace: private','pid namespace: private','mnt namespace: private','net namespace: private','ipc namespace: private','uts namespace: private','host parent: absent from private /proc','host parent signal lookup: denied','host loopback listener: unreachable','AF_UNIX socket creation: denied','effective capabilities: none','no_new_privs: set','nested namespace write attempt: rejected exit=1']:
  assert sandbox.count('PASS '+marker)==2,marker
 for marker in ['PASS build .lake write: allowed','PASS export .lake write-open: denied','PASS export .lake truncate: denied']:
  assert marker in sandbox
 for case in ['unknown option','unexpected --rw','unexpected --rwx','relative --rwx']:
  assert f'NEGATIVE {case}: exit=2' in sandbox
 need('user-service.log',0,'systemd-run','--user')
 need('dependencies.log',0)
 for dep in dependencies:assert "checking out revision '"+dep['rev']+"'" in texts['dependencies.log']
 for f in ['elan.log','landrun-build.log','comparator-build.log']:
  s=(B/'artifact/bootstrap'/f).read_text();assert s.rstrip().endswith('EXIT_STATUS=0')
 runs.append({'repository':repo,'run_id':runid,'job_id':jobid,'artifact_id':artifactid,'artifact_digest':a['digest'],'artifact_size':len(zdata),'checked_commit':result['repository_commit'],'official_head_commit':PROOF,'official_verify_step':'success','only_selected_problem':'PF-03','project_input_files':len(inputs),'active_Lean_files':len(lean_inputs),'actual_built_PF03_modules':len(built),'contract_count':len(names),'actual_aggregate_axioms':aggregate,'all_target_report_occurrences':reports,'tool_receipt':tr,'artifact_member_sha256':member_hashes,'result_sha256':sha(R.read_bytes()),'shared_checker_controls_job':next(j['conclusion'] for j in jobs if j['name']=='checker-controls'),'controls_within_actual_project_job':'All required controls passed; separate checker-controls job was correctly skipped because infrastructure did not change'})
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewer':'/root/pf03_final_referee2','verdict':'PASS','kind':'Independent operational and archived-artifact audit with fresh public GitHub observations; no compiler or Comparator run by this reviewer','proof_commit':PROOF,'upstream_merge_commit':MERGE,'both_entire_git_trees':api['merge_commit']['tree'],'project_git_tree':next(r['sha'] for r in api['merge_pf03_directory'] if r['name']=='lean'),'published_project_source_sha256':inputs,'all_active_Lean_files_match_previous_independent_review':True,'source_lock_sha256':sha(lockbytes),'source_lock_entries_checked_against_pinned_Forsythe_git_objects':len(lock['files']),'runs':runs,'reviewed_harness_hashes':{f:sha(blob(f)) for f in ['.github/workflows/lean-verification.yml','tools/lean/verify.sh','tools/lean/harness.py','tools/lean/source-lock.json']},'count_change_by_reviewer':0,'limits':['Evidence applies to the exact published proof commit and the tree-identical synthetic PR merge, not an uninspected future revision.','No new Lean or Comparator process was run by this reviewer.','This is not a full independent audit of the Lean kernel, operating system, GitHub, exporter or checker implementation.','Machine acceptance does not establish informal statement fidelity; that is covered by the separate hash-bound mathematical reviews.']}
(O/'AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'verdict':'PASS','runs':len(runs),'input_files_per_run':len(inputs),'active_Lean_files':len(lean_inputs),'contracts_per_run':len(names),'tool_source_pins':len(lock['files']),'merge_tree_equal_to_proof_tree':True,'audit_sha256':sha((O/'AUDIT.json').read_bytes())},indent=2))
