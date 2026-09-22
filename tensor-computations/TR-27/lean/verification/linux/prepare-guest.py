from pathlib import Path,PurePosixPath
import datetime,hashlib,json,os,re,subprocess,sys,tarfile
base=Path('/home/admin/nla-tr27-full-20260922');receipt=json.loads((base/'input-receipt.json').read_text());archive=base/'input.tar'
assert archive.stat().st_size==receipt['archive_bytes']
assert hashlib.sha256(archive.read_bytes()).hexdigest()==receipt['archive_sha256']
repo=base/'repo';repo.mkdir()
prefix=PurePosixPath(receipt['project_path']);members={}
with tarfile.open(archive) as t:
 for m in t.getmembers():
  path=PurePosixPath(m.name);assert not path.is_absolute() and '..' not in path.parts
  assert m.isdir() or m.isfile(),m.name
  if m.isfile():
   rel=str(path.relative_to(prefix));assert rel not in members
   members[rel]=hashlib.sha256(t.extractfile(m).read()).hexdigest()
 assert members==receipt['input_sha256'] and len(members)==116
 t.extractall(repo,filter='data')
project=repo/receipt['project_path']
actual={str(p.relative_to(project)):hashlib.sha256(p.read_bytes()).hexdigest() for p in project.rglob('*') if p.is_file()}
assert actual==receipt['input_sha256']
assert not (project/'.lake').exists()
assert not any(p.suffix in {'.olean','.ilean','.o','.so','.a'} for p in project.rglob('*') if p.is_file())
config=json.loads((project/'comparator.json').read_text());assert config['theorem_names']==receipt['theorem_names'] and len(config['theorem_names'])==25
assert set(config['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
solution=(project/'Solution.lean').read_text();assert 'import LeanCert.Tactic.Verification' in solution and 'set_option leancert.trust "kernel"' in solution
assert re.findall(r'^#assert_trust kernel (\S+)$',solution,re.M)==config['theorem_names']
assert re.findall(r'^#print axioms (\S+)$',solution,re.M)==config['theorem_names']
def git(*args):
 return subprocess.check_output(['git',*args],cwd=repo,text=True,stderr=subprocess.STDOUT).strip()
git('init','-q','-b','verification-tr27')
git('add','--',receipt['project_path'])
git('-c','user.name=George Stepaniants','-c','user.email=','commit','-q','-m','Freeze unchanged reviewed TR-27 input from publication 775e8b169119c4045b07db7666eda8c001ae3bd1')
commit=git('rev-parse','HEAD');assert git('status','--porcelain')==''
assert set(git('ls-files').splitlines())=={receipt['project_path']+'/'+n for n in actual}
sys.path.insert(0,'/home/admin/mf21-harness/tools/lean');import harness
assert harness.validate_project(project)==config
record={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'uid':os.getuid(),'publication_repository':receipt['publication_repository'],'publication_commit':receipt['publication_commit'],'publication_base':receipt['publication_base'],'guest_repository_commit':commit,'commit_relation':'Fresh local verification-only git commit containing exactly the publication project files with unchanged bytes; intentionally distinct from publication commit.','project':receipt['project_path'],'archive_sha256':receipt['archive_sha256'],'receipt_sha256':hashlib.sha256((base/'input-receipt.json').read_bytes()).hexdigest(),'input_sha256':actual,'tracked_input_count':len(actual),'theorem_names':config['theorem_names'],'all25_kernel_assertions_and_axiom_prints_present':True,'prior_project_build_artifacts':False,'git_status':git('status','--porcelain'),'project_validation':'PASS','verification_started':False}
(base/'preparation.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
