from pathlib import Path
import datetime,hashlib,json,subprocess
base=Path('/home/admin/nla-tr27-full-20260922');receipt=json.loads((base/'input-receipt.json').read_text())
candidates=[]
for p in Path('/home/admin/nla-lean-tools/.verification-tmp').glob('nla-fresh-proof-*/project'):
 s=p/'Solution.lean'
 if s.is_file() and hashlib.sha256(s.read_bytes()).hexdigest()==receipt['input_sha256']['Solution.lean']:
  candidates.append(p)
assert len(candidates)==1,candidates
fresh=candidates[0];manifest=json.loads((fresh/'lake-manifest.json').read_text());package_records=[]
for p in manifest['packages']:
 path=fresh/manifest['packagesDir']/p['name']
 actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=path,text=True).strip();assert actual==p['rev'],p['name']
 package_records.append({'name':p['name'],'url':p['url'],'manifest_revision':p['rev'],'actual_git_head':actual})
source=fresh/'.lake/packages/leancert/LeanCert/Tactic/Verification.lean';blob=source.read_bytes();gitblob=subprocess.check_output(['git','show','HEAD:LeanCert/Tactic/Verification.lean'],cwd=fresh/'.lake/packages/leancert');assert blob==gitblob
out=base/'dependency-evidence';out.mkdir(exist_ok=True);(out/'LeanCert-Verification.lean').write_bytes(blob)
record={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'read_only_fresh_project':str(fresh),'package_heads_all_match_manifest':True,'packages':package_records,'LeanCert_Verification_sha256':hashlib.sha256(blob).hexdigest(),'LeanCert_Verification_bytes_match_pinned_git_blob':True,'snapshot_input_sha256':{name:hashlib.sha256((fresh/name).read_bytes()).hexdigest() for name in receipt['input_sha256']}}
assert record['snapshot_input_sha256']==receipt['input_sha256']
(out/'dependency-receipt.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
