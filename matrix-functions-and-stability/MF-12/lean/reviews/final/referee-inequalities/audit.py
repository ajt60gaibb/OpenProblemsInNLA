#!/usr/bin/env python3
"""Independent read-only Git/raw-log audit; never invokes Lean or Lake."""
from pathlib import Path
import difflib
import hashlib
import json
import re
import shutil
import subprocess
import zipfile

HERE = Path(__file__).resolve().parent
BASE = Path('/tmp/nla-lean-next-20260915')
RUN = BASE / 'reviews/MF12-elimination-complete-source/canonical35037011332-addendum/runtime-evidence'
ART = RUN / 'artifacts/lean-MF-12'
LOG = ART / 'verify-20260915T234603Z-4147'
REPO = Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
WORK = HERE
REL = 'matrix-functions-and-stability/MF-12/lean'
PROJECT = HERE / 'source'
COMMIT = '3d06c49635bbdde109c491510641204285eaf05c'
PRIOR = BASE / 'reviews/MF12-inequalities-full-source-referee'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def read(path):
    return json.loads(path.read_text())

def git(path):
    return subprocess.check_output(['git','show',f'{COMMIT}:{path}'],cwd=REPO)

def save(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')

run, jobs, arts, fetch = (read(RUN/n) for n in
    ['run.json','jobs.json','artifacts.json','FETCH-IDENTITY.json'])
result = read(LOG/'result.json')
assert run['id'] == fetch['run'] == 35037011332
assert run['head_sha'] == fetch['commit'] == result['repository_commit'] == COMMIT
assert run['status'] == 'completed' and run['conclusion'] == fetch['conclusion'] == 'success'
assert run['head_branch'] == 'codex/lean-mf12-verification'
assert run['event'] == 'push' and run['path'] == '.github/workflows/lean-verification.yml'
assert result['project'] == REL and result['result'] == 'comparator-accepted'
verify = next(j for j in jobs['jobs'] if j['id']==104608341268)
assert verify['head_sha']==COMMIT and verify['conclusion']=='success'
assert verify['labels']==['ubuntu-24.04']
assert all(s['conclusion']=='success' for s in verify['steps'])
assert next(j for j in jobs['jobs'] if j['name']=='checker-controls')['conclusion']=='skipped'
artifact = arts['artifacts'][0]
assert len(arts['artifacts'])==1 and artifact['id']==10423298472
assert artifact['workflow_run']['id']==35037011332 and artifact['workflow_run']['head_sha']==COMMIT
archive = RUN/'lean-MF-12.zip'
ziphash = sha(archive.read_bytes())
assert 'sha256:'+ziphash==artifact['digest']
assert ziphash==fetch['archives'][0]['sha256']
assert archive.stat().st_size==artifact['size_in_bytes']
members={}
with zipfile.ZipFile(archive) as z:
    for n in z.namelist():
        if n.endswith('/'): continue
        b=z.read(n)
        assert b==(ART/n).read_bytes(),n
        members[n]=sha(b)

raw=(RUN/'job-104608341268.log').read_text(encoding='utf-8-sig')
job=re.sub(r'(?m)^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}\.\d+Z ?', '', raw)
assert COMMIT in job and 'Artifact ID '+str(artifact['id']) in job
assert 'SHA256 digest of uploaded artifact zip is '+ziphash in job
assert 'PASS: fresh Comparator run and all controls.' in job
loghashes={}
for f in sorted(LOG.glob('*.log')):
    t=f.read_text()
    assert t.startswith('$ ') and re.search(r'\nEXIT_STATUS=\d+\n\Z',t),f.name
    output=t.split('\n',1)[1].rsplit('\nEXIT_STATUS=',1)[0].rstrip('\n')
    assert output in job,('raw-job content mismatch',f.name)
    loghashes[f.name]=sha(f.read_bytes())

inputs=result['input_sha256']
assert len(inputs)==322
tree=subprocess.check_output(['git','ls-tree','-rz',COMMIT,'--',REL],cwd=REPO)
tree_paths=set()
for entry in tree.split(b'\0'):
    if not entry: continue
    meta,path=entry.split(b'\t',1)
    mode,kind,object_id=meta.decode().split()
    assert mode in ['100644','100755'] and kind=='blob'
    full=path.decode(); local=full[len(REL)+1:]; tree_paths.add(local)
    b=subprocess.check_output(['git','cat-file','blob',object_id],cwd=REPO)
    assert sha(b)==inputs[local],local
    assert '.lake' not in Path(local).parts and Path(local).suffix not in ['.olean','.ilean','.o','.a','.so']
    target=HERE/'source'/local; target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes(b)
assert tree_paths==set(inputs)

prior_inputs=read(PRIOR/'INPUTS.json')['source_files']
assert len(prior_inputs)==35
unchanged={}
changes={}
relocated={}
for f,h in prior_inputs.items():
    old=(PRIOR/'source'/f).read_bytes()
    assert sha(old)==h,f
    if f in inputs and inputs[f]==h:
        unchanged[f]=h
    elif f in inputs:
        before='verification/packaging/before/'+f
        assert inputs[before]==h,('historical pre-packaging bytes missing',f)
        new=(PROJECT/f).read_bytes()
        changes[f]={'before_sha256':h,'after_sha256':inputs[f],'retained_original':before}
        diff=''.join(difflib.unified_diff(old.decode().splitlines(keepends=True),new.decode().splitlines(keepends=True),fromfile='reviewed/'+f,tofile='candidate/'+f))
        path=HERE/'packaging-diffs'/(f+'.patch');path.parent.mkdir(parents=True,exist_ok=True);path.write_text(diff)
    else:
        before='verification/packaging/before/'+f
        assert inputs[before]==h,('relocated draft differs',f)
        relocated[f]={'sha256':h,'retained_path':before}
assert len(unchanged)==27 and len(changes)==4 and len(relocated)==4
assert set(changes)=={'README.md','SourceCorrespondence.md','formalization.yaml','lakefile.toml'}
math_files={f:inputs[f] for f in inputs if f.startswith('NLA/') and f.endswith('.lean')}
math_files['Solution.lean']=inputs['Solution.lean']
assert len(math_files)==19
assert all(unchanged[f]==h for f,h in math_files.items())
assert inputs['Challenge.lean']==prior_inputs['Challenge.lean']
assert inputs['NUMERICAL_TARGETS.md']==prior_inputs['NUMERICAL_TARGETS.md']
assert inputs['STATEMENT-FREEZE.json']==prior_inputs['STATEMENT-FREEZE.json']
freeze=read(PROJECT/'STATEMENT-FREEZE.json')
frozen_unchanged={}
frozen_metadata_changes={}
for f,h in freeze['frozen_files_sha256'].items():
    snapshot='statement-audit/snapshots/'+f+('.txt' if f.endswith('.lean') else '')
    assert inputs[snapshot]==h,('original frozen snapshot differs',f)
    if inputs[f]==h: frozen_unchanged[f]=h
    else:
        assert f in ['lakefile.toml','SourceCorrespondence.md']
        frozen_metadata_changes[f]={'original_sha256':h,'current_sha256':inputs[f],'immutable_snapshot':snapshot}
assert len(frozen_unchanged)==8 and len(frozen_metadata_changes)==2
for r in freeze['reviews']: assert inputs[r['retained_path']]==r['sha256'],r
old=(PRIOR/'source/lakefile.toml').read_text();new=(PROJECT/'lakefile.toml').read_text()
assert old.replace('defaultTargets = ["Challenge"]','defaultTargets = ["Solution"]')==new
transition=read(PROJECT/'verification/packaging/TRANSITION.json')
for f,h in transition['mathematical_files_unchanged'].items():assert inputs[f]==h,f
for f,v in transition['changed_top_level_files'].items():
    assert inputs[f]==v['after_sha256'] and inputs[v['before_path']]==v['before_sha256'],f
assert not transition['proof_implementation_changes']
config=read(PROJECT/'comparator.json')
assert config==result['config'] and len(config['theorem_names'])==28
assert config['definition_names']==[]
assert set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert config['challenge_module']=='Challenge' and config['solution_module']=='Solution'
comp=(LOG/'comparator.log').read_text()
assert comp.endswith('EXIT_STATUS=0\n')
assert comp.count('Running Lean default kernel on solution.')==1
assert comp.count('Lean default kernel accepts the solution')==1
assert comp.count('Your solution is okay!')==1
assert len(re.findall(r'^warning: Challenge\.lean:.*declaration uses `sorry`',comp,re.M))==28
proofpart=comp.split('Building Solution\n',1)[1]
assert not re.search(r'^error:|declaration uses `sorry`|sorryAx|Illegal axiom|native_decide|unrecognized axioms',proofpart,re.M)
target_axioms={}
solution=(PROJECT/'Solution.lean').read_text()
for name in config['theorem_names']:
    matches=re.findall(r"^info: Solution\.lean:\d+:0: '"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]$",comp,re.M)
    assert len(matches)==1,name
    assert set(matches[0].split(', '))<=set(config['permitted_axioms'])
    assert re.search(r'^#assert_trust kernel '+r'(?:NLA\.MF12\.)?'+re.escape(name.removeprefix('NLA.MF12.'))+r'\s*$',solution,re.M)
    assert len(re.findall(re.escape(name)+r'(?=,|\])',comp))==2,('export count',name)
    target_axioms[name]=matches[0].split(', ')
module_files=sorted(f for f in inputs if f.startswith('NLA/') and f.endswith('.lean'))
for f in module_files:
    assert 'Built '+f[:-5].replace('/','.')+' ' in comp,('missing build',f)
assert 'Built Solution ' in comp

controls={
 'kernel-controls.log':['RETURN honest_with_inductives_and_quotients: accepted',
   'RETURN invalid_raw_proof: rejected:','Quotient post-check rejects the solution',
   'PASS: all three actual Comparator.runBuiltinKernel cases behaved as required','EXIT_STATUS=0'],
 'comparator-controls.log':['PASS simple_match: exit 0, expected 0',
   'PASS simple_mismatch: exit 1, expected 1','PASS simple_axiom_issue: exit 1, expected 1',
   'PASS simple_kind_mismatch: exit 1, expected 1','PASS type_mismatch: exit 1, expected 1',
   "Challenge and solution theorem statement do not match: 'checked'",'PASS: all five Comparator regressions','EXIT_STATUS=0'],
 'negative-sorry.log':["Illegal axiom detected: 'sorryAx'",'EXIT_STATUS=1'],
 'negative-native.log':["Illegal axiom detected: 'checked._native.native_decide.ax_1_1'",'EXIT_STATUS=1'],
 'sandbox.log':['MODE build: exit=0','MODE export: exit=0','PASS AF_UNIX socket creation: denied errno=97',
   'PASS export .lake write-open: denied errno=30','PASS build .lake write: allowed','Sandbox UID: 1001',
   'PASS host loopback listener: unreachable errno=13','PASS nested namespace write attempt: rejected exit=1',
   'NEGATIVE unknown option: exit=2','NEGATIVE unexpected --rw: exit=2',
   'NEGATIVE unexpected --rwx: exit=2','NEGATIVE relative --rwx: exit=2',
   'Outer and export fixture contents unchanged; only designated build fixture written.','EXIT_STATUS=0'],
 'user-service.log':['RestrictAddressFamilies=~AF_UNIX','EXIT_STATUS=0']}
for file,markers in controls.items():
    text=(LOG/file).read_text()
    for marker in markers: assert marker in text,(file,marker)

manifest=read(PROJECT/'lake-manifest.json')
pins={p['name']:p['rev'] for p in manifest['packages']}
deps=dict(re.findall(r"info: ([^:]+): checking out revision '([0-9a-f]{40})'",(LOG/'dependencies.log').read_text()))
assert pins==deps and len(pins)==10
assert (LOG/'mathlib-cache.log').read_text().endswith('EXIT_STATUS=0\n')
lock=git('tools/lean/source-lock.json')
assert sha(lock)==result['source_lock_sha256']==result['tool_receipt']['source_lock_sha256']
assert json.loads(lock)['commit']==result['tool_receipt']['forsythe_commit']
assert result['tool_receipt']['lean_toolchain']=='leanprover/lean4:v4.33.1'
assert result['tool_receipt']['platform'].startswith('Linux-')
assert 'x86_64-unknown-linux-gnu' in result['tool_receipt']['lean_version']
runtime={}
for f in ['tools/lean/source-lock.json','tools/lean/harness.py','tools/lean/verify.sh',
          'tools/lean/bootstrap.sh','tools/lean/validate_manifest.py','.github/workflows/lean-verification.yml',
          'docs/lean/README.md','docs/lean/REVIEW.md']:
    b=git(f); runtime[f]=sha(b)
    p=HERE/'runtime-source'/f;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
for f in ['run.json','jobs.json','artifacts.json','FETCH-IDENTITY.json',
          'job-104608341268.log','job-104608272267.log','lean-MF-12.zip']:
    (HERE/'evidence').mkdir(exist_ok=True)
    shutil.copyfile(RUN/f,HERE/'evidence'/f)
shutil.copytree(ART,HERE/'evidence/artifact',dirs_exist_ok=True)
for f in ['REVIEW.md','INPUTS.json','CHECKS.json']:
    p=HERE/'prior-review'/f;p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(PRIOR/f,p)

canonical_files={}
for f,h in read(PRIOR/'INPUTS.json')['canonical_files'].items():
    b=git(f)
    assert sha(b)==h,('original source changed',f)
    target=HERE/'canonical'/f;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(b)
    canonical_files[f]=h
active=read(PROJECT/'ACTIVE-SOURCE-MANIFEST.json')
for f,h in active['mathematical_files_sha256'].items(): assert inputs[f]==h,f
assert active['statement_freeze_sha256']==inputs['STATEMENT-FREEZE.json']
assert active['comparator_config_sha256']==inputs['comparator.json']
validator=Path('/private/tmp/nla-lean-next-ie04-worktree/tools/lean/validate_manifest.py')
assert sha(validator.read_bytes())==runtime['tools/lean/validate_manifest.py']
cmd=['/tmp/nla-lean-formalization/venv/bin/python',str(validator),str(PROJECT)]
validation=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
assert validation.returncode==0
assert 'PASS (28 declarations)' in validation.stdout
save(HERE/'SCHEMA.json',{'argv':cmd,'returncode':validation.returncode,'stdout':validation.stdout,'stderr':validation.stderr,'validator_sha256':sha(validator.read_bytes())})
out={'reviewer':'/root/next_inequalities','run_id':35037011332,'commit':COMMIT,
     'job_id':104608341268,'artifact_id':10423298472,'archive_sha256':ziphash,
     'all_project_Git_inputs':inputs,'original_mathematical_source':canonical_files,'all_project_inputs_match_Git_receipt':True,
     'archive_members':members,'raw_job_sha256':sha((RUN/'job-104608341268.log').read_bytes()),
     'command_logs_sha256':loghashes,'all_command_outputs_occur_in_raw_job':True,
     'previous_approved_files_unchanged':unchanged,'packaging_changes':changes,'relocated_draft_records':relocated,
     'frozen_files_unchanged':frozen_unchanged,'frozen_metadata_changes':frozen_metadata_changes,
     'all19_previously_reviewed_math_files_unchanged':math_files,
     'complete_implementation_files':module_files+['Solution.lean'],
     'all_target_axioms':target_axioms,'mandatory_control_markers':controls,
     'dependency_commits':pins,'tool_receipt':result['tool_receipt'],'runtime_source':runtime,
     'candidate_full_canonical_acceptance':True,'published_final_metadata_run_accepted':False,
     'upstream_merged_main_revision_checked':False,'no_local_Lean_Lake_invocation':True}
closures=dict(re.findall(r"^info: [^\n]*: '([^']+)' depends on axioms: \[([^\]]*)\]$",comp,re.M))
assert len(closures)==28
assert all(set(v.split(', '))<=set(config['permitted_axioms']) for v in closures.values())
assert set(closures['NLA.MF12.gap_decomposition'].split(', '))=={'propext','Quot.sound'}
assert all(set(v.split(', '))==set(config['permitted_axioms']) for k,v in closures.items() if k!='NLA.MF12.gap_decomposition')
out['all_printed_axiom_closures']={k:v.split(', ') for k,v in closures.items()}
previous=read(BASE/'reviews/IE04-inequalities-canonical-35034399633/AUDIT.json')
assert runtime==previous['runtime_source']
out['shared_runtime_source_matches_prior_independent_inspection']=True
save(HERE/'AUDIT.json',out)
files={str(p.relative_to(HERE)):sha(p.read_bytes()) for p in sorted(HERE.rglob('*'))
       if p.is_file() and p not in [HERE/'INPUTS.json',HERE/'REVIEW.md']}
save(HERE/'INPUTS.json',{'scope':'Independent complete candidate canonical acceptance; publication rerun pending','files':files})
print(json.dumps({'project_inputs':len(inputs),'unchanged_prior_files':len(unchanged),
                  'targets':len(target_axioms),'modules':len(module_files)+1,
                  'AUDIT_sha256':sha((HERE/'AUDIT.json').read_bytes()),
                  'INPUTS_sha256':sha((HERE/'INPUTS.json').read_bytes())},indent=2))
