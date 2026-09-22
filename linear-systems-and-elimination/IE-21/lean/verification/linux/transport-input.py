from pathlib import Path,PurePosixPath
import argparse,base64,datetime,hashlib,json,os,shutil,subprocess,tarfile
p=argparse.ArgumentParser()
p.add_argument('--publication-repository',required=True,type=Path)
p.add_argument('--publication-commit',required=True)
p.add_argument('--archive',required=True,type=Path)
p.add_argument('--receipt',required=True,type=Path)
p.add_argument('--guest-directory',default='/home/admin/nla-ie21-full-20260922')
a=p.parse_args();base=Path(__file__).resolve().parent
TART='/private/tmp/mf21-tart-2.37.0/tart.app/Contents/MacOS/tart'
env=os.environ.copy();env['TART_HOME']='/private/tmp/mf21-tart-vms'
sha=lambda b:hashlib.sha256(b).hexdigest()
r=json.loads(a.receipt.read_text());archive=a.archive.read_bytes()
assert len(archive)==r['archive_bytes'] and sha(archive)==r['archive_sha256']
assert r['publication_commit']==a.publication_commit
assert r['project_path']=='linear-systems-and-elimination/IE-21/lean'
assert subprocess.check_output(['git','rev-parse',a.publication_commit+'^{commit}'],cwd=a.publication_repository,text=True).strip()==a.publication_commit
prefix=PurePosixPath(r['project_path'])
files=subprocess.check_output(['git','ls-tree','-r','--name-only',a.publication_commit,'--',r['project_path']],cwd=a.publication_repository,text=True).splitlines()
assert set(files)=={r['project_path']+'/'+name for name in r['input_sha256']}
for name,digest in r['input_sha256'].items():
 blob=subprocess.check_output(['git','show',a.publication_commit+':'+r['project_path']+'/'+name],cwd=a.publication_repository)
 assert sha(blob)==digest,name
with tarfile.open(a.archive) as t:
 content={}
 for item in t.getmembers():
  path=PurePosixPath(item.name)
  assert item.isdir() or item.isfile()
  assert not path.is_absolute() and '..' not in path.parts
  if item.isfile():
   name=str(path.relative_to(prefix));assert name not in content
   content[name]=sha(t.extractfile(item).read())
 assert content==r['input_sha256']
assert len(r['theorem_names'])==len(set(r['theorem_names']))==23
record={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'publication_repository':str(a.publication_repository),'publication_commit':a.publication_commit,'archive_sha256':sha(archive),'receipt_sha256':sha(a.receipt.read_bytes()),'all_committed_project_files_match_archive':True,'input_count':len(content),'selected_target_count':len(r['theorem_names']),'source_sha256':content,'guest_directory':a.guest_directory,'verification_started':False}
(base/'input-authentication.json').write_text(json.dumps(record,indent=2)+'\n')
assert a.guest_directory.startswith('/home/admin/nla-ie21-full-') and '..' not in PurePosixPath(a.guest_directory).parts
def guest(code):
 return subprocess.run([TART,'exec','mf21-verification','/usr/bin/python3','-c',code],env=env,check=True,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT).stdout
# The new directory check is intentionally non-resumable: failed attempts retain their bytes.
guest('from pathlib import Path; p=Path('+repr(a.guest_directory)+'); assert not p.exists(); p.mkdir()')
transfers={}
for path,name in [(a.archive,'input.tar'),(a.receipt,'input-receipt.json')]+[(base/name,name) for name in ['prepare-guest.py','run-verifier.py','capture-dependency-receipt.py']]:
 blob=path.read_bytes();target=a.guest_directory+'/'+name
 for i in range(0,len(blob),49152):
  chunk=base64.b64encode(blob[i:i+49152]).decode()
  guest('from pathlib import Path; import base64; p=Path('+repr(target)+'); f=p.open('+repr('xb' if i==0 else 'ab')+'); f.write(base64.b64decode('+repr(chunk)+')); f.close()')
 output=guest('from pathlib import Path; import hashlib; p=Path('+repr(target)+'); print(hashlib.sha256(p.read_bytes()).hexdigest())').strip()
 assert output==sha(blob),name
 transfers[name]={'bytes':len(blob),'sha256':output}
 if path.resolve()!=(base/name).resolve():
  assert not (base/name).exists();shutil.copyfile(path,base/name)
(base/'transport-receipt.json').write_text(json.dumps({'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':transfers,'guest_directory':a.guest_directory,'verification_started':False},indent=2)+'\n')
print('PASS: all committed archive source bytes independently matched; transferred '+str(len(transfers))+' files with exact hashes; no verifier started.')
