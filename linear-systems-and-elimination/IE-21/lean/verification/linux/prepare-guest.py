from pathlib import Path, PurePosixPath
import datetime, hashlib, json, os, re, subprocess, sys, tarfile

base=Path(__file__).resolve().parent
receipt=json.loads((base/'input-receipt.json').read_text())
archive=base/'input.tar'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert os.getuid()==1000
assert archive.stat().st_size==receipt['archive_bytes']
assert sha(archive)==receipt['archive_sha256']
assert receipt['project_path']=='linear-systems-and-elimination/IE-21/lean'
repo=base/'repo';repo.mkdir()
prefix=PurePosixPath(receipt['project_path']);members={}
with tarfile.open(archive) as t:
 for m in t.getmembers():
  path=PurePosixPath(m.name)
  assert not path.is_absolute() and '..' not in path.parts
  assert m.isdir() or m.isfile(),m.name
  if m.isfile():
   rel=str(path.relative_to(prefix));assert rel not in members
   members[rel]=hashlib.sha256(t.extractfile(m).read()).hexdigest()
 assert members==receipt['input_sha256']
 t.extractall(repo,filter='data')
project=repo/receipt['project_path']
actual={str(p.relative_to(project)):sha(p) for p in project.rglob('*') if p.is_file()}
assert actual==receipt['input_sha256']
assert not (project/'.lake').exists()
assert not any(p.suffix in {'.olean','.ilean','.o','.so','.a'} for p in project.rglob('*') if p.is_file())
config=json.loads((project/'comparator.json').read_text())
names=config['theorem_names']
assert names==receipt['theorem_names'] and len(names)==len(set(names))==23
assert set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
challenge_names=['NLA.IE21.'+n for n in re.findall(r'^theorem ([A-Za-z_][A-Za-z_0-9]*)',(project/'Challenge.lean').read_text(),re.M)]
assert challenge_names==names
solution=(project/'Solution.lean').read_text()
assert 'import LeanCert.Tactic.Verification' in solution and 'set_option leancert.trust "kernel"' in solution
assert re.findall(r'^#assert_trust kernel (\S+)$',solution,re.M)==names
assert re.findall(r'^#print axioms (\S+)$',solution,re.M)==names
assert not re.search(r'^import Challenge\b',solution,re.M)
manifest=json.loads((project/'lake-manifest.json').read_text())
pins={p['name']:p['rev'] for p in manifest['packages']}
assert pins['mathlib']=='0df444a360eaa60ab8c11dca51a86af692955474'
assert pins['leancert']=='621a43d7cf21f87872392a01e874f2f1dbddc926'
def git(*args):
 return subprocess.check_output(['git',*args],cwd=repo,text=True,stderr=subprocess.STDOUT).strip()
git('init','-q','-b','verification-ie21')
git('add','--',receipt['project_path'])
git('-c','user.name=George Stepaniants','-c','user.email=','commit','-q','-m','Freeze unchanged reviewed IE-21 input from publication '+receipt['publication_commit'])
commit=git('rev-parse','HEAD');assert git('status','--porcelain')==''
assert set(git('ls-files').splitlines())=={receipt['project_path']+'/'+n for n in actual}
sys.path.insert(0,'/home/admin/mf21-harness/tools/lean');import harness
assert harness.validate_project(project)==config
record={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'uid':os.getuid(),'publication_repository':receipt['publication_repository'],'publication_commit':receipt['publication_commit'],'publication_base':receipt['publication_base'],'guest_repository_commit':commit,'commit_relation':'Fresh local verification-only git commit containing exactly the publication project files with unchanged bytes; intentionally distinct from publication commit.','project':receipt['project_path'],'archive_sha256':receipt['archive_sha256'],'receipt_sha256':sha(base/'input-receipt.json'),'input_sha256':actual,'tracked_input_count':len(actual),'theorem_names':names,'selected_theorem_count':len(names),'all_selected_kernel_assertions_and_axiom_prints_present':True,'prior_project_build_artifacts':False,'git_status':git('status','--porcelain'),'project_validation':'PASS','verification_started':False}
(base/'preparation.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
