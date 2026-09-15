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
RUN = BASE / 'canonical-runs/MF24-35033148310'
ART = RUN / 'artifacts/lean-MF-24'
LOG = ART / 'verify-20260915T225458Z-4151'
REPO = Path('/Users/georgestepaniants/Research/OpenProblemsInNLA')
WORK = Path('/private/tmp/nla-lean-next-mf24-worktree')
REL = 'matrix-functions-and-stability/MF-24/lean'
PROJECT = WORK / REL
COMMIT = '208e30d80f73ef661b1f019c7de93c70254f7e48'
PRIOR = BASE / 'reviews/MF24-inequalities-source-referee/final-byte-addendum-20260915'

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
assert run['id'] == fetch['run'] == 35033148310
assert run['head_sha'] == fetch['commit'] == result['repository_commit'] == COMMIT
assert run['status'] == 'completed' and run['conclusion'] == fetch['conclusion'] == 'success'
assert run['event'] == 'push' and run['path'] == '.github/workflows/lean-verification.yml'
assert result['project'] == REL and result['result'] == 'comparator-accepted'
verify = next(j for j in jobs['jobs'] if j['id']==104596164346)
assert verify['head_sha']==COMMIT and verify['conclusion']=='success'
assert verify['labels']==['ubuntu-24.04']
assert all(s['conclusion']=='success' for s in verify['steps'])
assert next(j for j in jobs['jobs'] if j['name']=='checker-controls')['conclusion']=='skipped'
artifact = arts['artifacts'][0]
assert len(arts['artifacts'])==1 and artifact['id']==10422461856
assert artifact['workflow_run']['id']==35033148310 and artifact['workflow_run']['head_sha']==COMMIT
archive = RUN/'lean-MF-24.zip'
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

raw=(RUN/'job-104596164346.log').read_text(encoding='utf-8-sig')
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
assert len(inputs)==192
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
    assert (PROJECT/local).read_bytes()==b,('working copy differs',local)
    assert '.lake' not in Path(local).parts and Path(local).suffix not in ['.olean','.ilean','.o','.a','.so']
    target=HERE/'source'/local; target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes(b)
assert tree_paths==set(inputs)

prior=read(PRIOR/'INPUTS.json')
changes={}; unchanged={}; diffs=[]
for f,h in prior['files'].items():
    now=inputs[f]
    if h==now: unchanged[f]=h
    else:
        changes[f]={'previous':h,'current':now}
        diffs.extend(difflib.unified_diff((PRIOR/'source'/f).read_text().splitlines(True),
                     (PROJECT/f).read_text().splitlines(True),fromfile='approved/'+f,tofile='candidate/'+f))
assert set(changes)=={'formalization.yaml','lakefile.toml'}
assert len(unchanged)==31
assert (PROJECT/'lakefile.toml').read_text()==(PRIOR/'source/lakefile.toml').read_text().replace(
    'defaultTargets = ["Challenge"]','defaultTargets = ["Solution"]')
(HERE/'PACKAGING-DIFF.patch').write_text(''.join(diffs))
freeze=read(PROJECT/'STATEMENT-FREEZE.json')

config=read(PROJECT/'comparator.json')
assert config==result['config'] and len(config['theorem_names'])==22
assert config['definition_names']==[]
assert set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
assert config['challenge_module']=='Challenge' and config['solution_module']=='Solution'
comp=(LOG/'comparator.log').read_text()
assert comp.endswith('EXIT_STATUS=0\n')
assert comp.count('Running Lean default kernel on solution.')==1
assert comp.count('Lean default kernel accepts the solution')==1
assert comp.count('Your solution is okay!')==1
assert len(re.findall(r'^warning: Challenge\.lean:.*declaration uses `sorry`',comp,re.M))==22
proofpart=comp.split('Building Solution\n',1)[1]
assert not re.search(r'^error:|declaration uses `sorry`|sorryAx|Illegal axiom|native_decide|unrecognized axioms',proofpart,re.M)
target_axioms={}
solution=(PROJECT/'Solution.lean').read_text()
for name in config['theorem_names']:
    matches=re.findall(r"^info: Solution\.lean:\d+:0: '"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]$",comp,re.M)
    assert len(matches)==1,name
    assert set(matches[0].split(', '))<=set(config['permitted_axioms'])
    assert re.search(r'^#assert_trust kernel '+re.escape(name)+r'\s*$',solution,re.M)
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
          'job-104596164346.log','job-104596070240.log','lean-MF-24.zip']:
    (HERE/'evidence').mkdir(exist_ok=True)
    shutil.copyfile(RUN/f,HERE/'evidence'/f)
shutil.copytree(ART,HERE/'evidence/artifact',dirs_exist_ok=True)
for f in ['REVIEW.md','INPUTS.json','development35031607095-addendum/REVIEW.md']:
    p=HERE/'prior-review'/f;p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(PRIOR/f,p)

out={'reviewer':'/root/next_inequalities','run_id':35033148310,'commit':COMMIT,
     'job_id':104596164346,'artifact_id':10422461856,'archive_sha256':ziphash,
     'all_project_Git_inputs':inputs,'all_project_inputs_match_worktree':True,
     'archive_members':members,'raw_job_sha256':sha((RUN/'job-104596164346.log').read_bytes()),
     'command_logs_sha256':loghashes,'all_command_outputs_occur_in_raw_job':True,
     'previous_approved_files_unchanged':unchanged,'packaging_changes':changes,
     'complete_implementation_files':module_files+['Solution.lean'],
     'all_target_axioms':target_axioms,'mandatory_control_markers':controls,
     'dependency_commits':pins,'tool_receipt':result['tool_receipt'],'runtime_source':runtime,
     'candidate_full_canonical_acceptance':True,'published_final_metadata_run_accepted':False,
     'upstream_PR_or_merge_asserted':False,'no_local_Lean_Lake_invocation':True}
save(HERE/'AUDIT.json',out)
files={str(p.relative_to(HERE)):sha(p.read_bytes()) for p in sorted(HERE.rglob('*'))
       if p.is_file() and p not in [HERE/'INPUTS.json',HERE/'REVIEW.md']}
save(HERE/'INPUTS.json',{'scope':'Independent complete candidate canonical acceptance; publication rerun pending','files':files})
print(json.dumps({'project_inputs':len(inputs),'unchanged_prior_files':len(unchanged),
                  'targets':len(target_axioms),'modules':len(module_files)+1,
                  'AUDIT_sha256':sha((HERE/'AUDIT.json').read_bytes()),
                  'INPUTS_sha256':sha((HERE/'INPUTS.json').read_bytes())},indent=2))
