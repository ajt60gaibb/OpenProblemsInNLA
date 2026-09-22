from pathlib import Path
import datetime,hashlib,json,subprocess
base=Path(__file__).resolve().parent
repo=Path('/private/tmp/nla-ie22-publication-20260922')
commit='c45f9ccef20a2fa5cc4b988e93d4173dab853362'
prefix='linear-systems-and-elimination/IE-22/lean'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=repo)
assert git('rev-parse','HEAD').decode().strip()==commit
assert git('status','--porcelain').decode()==''
files=git('ls-tree','-r','--name-only',commit,'--',prefix).decode().splitlines()
assert len(files)==394
hashes={p[len(prefix)+1:]:sha(git('show',commit+':'+p)) for p in files}
for p,digest in hashes.items():assert sha((repo/prefix/p).read_bytes())==digest,p
freeze=git('show',commit+':'+prefix+'/reviews/package-source-freeze.json')
assert sha(freeze)=='2a07dedc9ca3774cd9fc5a760f421dd47f105cc257c770f401ae73513dea1226'
freeze_record=json.loads(freeze)
assert len(freeze_record['source_sha256'])==57
for p,digest in freeze_record['source_sha256'].items():assert hashes[p]==digest,p
config=json.loads(git('show',commit+':'+prefix+'/comparator.json'))
assert len(config['theorem_names'])==len(set(config['theorem_names']))==20
archive=git('archive','--format=tar',commit,'--',prefix)
archive_path=base/'publication-input.tar';receipt_path=base/'publication-input-receipt.json'
assert not archive_path.exists() and not receipt_path.exists()
archive_path.write_bytes(archive)
r={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'publication_repository':'https://github.com/ajt60gaibb/OpenProblemsInNLA','publication_commit':commit,'publication_base':'daf313133bfe730c32a266ea85cd9ca0fbe2d5ed','publication_parent':'19d9f19bd2b779caf5f3b40540e9a303a1226a5c','project_path':prefix,'archive_bytes':len(archive),'archive_sha256':sha(archive),'input_sha256':hashes,'theorem_names':config['theorem_names'],'package_source_freeze_sha256':sha(freeze),'all_frozen_source_hashes_match':True,'role':'Mechanical verification preparation; operator authored Gaussian Poincare, hinge and variance modules, and vendored IE-21 Gaussian/spherical modules and is not a final independent mathematical reviewer.'}
receipt_path.write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['publication_commit','project_path','archive_bytes','archive_sha256','package_source_freeze_sha256']},indent=2))
print('PASS: all394 committed/live project files and all57 final-reviewed frozen files match before transport')
