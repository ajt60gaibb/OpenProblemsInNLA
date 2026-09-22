from pathlib import Path,PurePosixPath
import base64,hashlib,json,os,re,shutil,subprocess,tarfile
base=Path(__file__).resolve().parent
TART='/private/tmp/mf21-tart-2.37.0/tart.app/Contents/MacOS/tart'
env=os.environ.copy();env['TART_HOME']='/private/tmp/mf21-tart-vms'
guest_base='/home/admin/nla-ie22-full-20260922'
def guest(code):return subprocess.check_output([TART,'exec','mf21-verification','/usr/bin/env','XDG_RUNTIME_DIR=/run/user/1000','DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus','/usr/bin/python3','-c',code],env=env,text=True)
blob=(base/'package-guest-evidence.py').read_bytes()
guest('from pathlib import Path; import base64; p=Path('+repr(guest_base+'/package-guest-evidence.py')+'); assert not p.exists(); p.write_bytes(base64.b64decode('+repr(base64.b64encode(blob).decode())+'))')
output=guest('import runpy; runpy.run_path('+repr(guest_base+'/package-guest-evidence.py')+', run_name="__main__")')
(base/'evidence-packaging.log').write_text(output);meta=json.loads(output)
(base/'evidence-export-receipt.json').write_text(json.dumps(meta,indent=2)+'\n')
blob=base64.b64decode(guest('from pathlib import Path; import base64; print(base64.b64encode(Path('+repr(guest_base+'/verification-evidence.tar.gz')+').read_bytes()).decode())'))
assert len(blob)==meta['bytes'] and hashlib.sha256(blob).hexdigest()==meta['sha256']
archive=base/'verification-evidence.tar.gz';assert not archive.exists();archive.write_bytes(blob)
dest=Path('/private/tmp/nla-ie22-publication-20260922/linear-systems-and-elimination/IE-22/lean/verification/linux')
assert not dest.exists();dest.mkdir(parents=True)
with tarfile.open(archive) as t:
 seen=set()
 for m in t.getmembers():
  path=PurePosixPath(m.name);assert not path.is_absolute() and '..' not in path.parts
  assert m.isdir() or m.isfile(),m.name
  if m.isfile():assert m.name not in seen;seen.add(m.name)
 t.extractall(dest,filter='data')
 for m in t.getmembers():
  if m.isfile():assert (dest/m.name).read_bytes()==t.extractfile(m).read(),m.name
for p in sorted(base.iterdir()):
 if p.is_file() and (p.suffix in {'.py','.json','.log'} or p.name in {'input.tar','verification-evidence.tar.gz'}):
  if p.name=='publication-input-receipt.json':continue
  target=dest/p.name
  if target.exists():assert target.read_bytes()==p.read_bytes(),p.name
  else:shutil.copyfile(p,target)
proof=(dest/'successful-verification/comparator.log').read_text()
exports=re.findall(r'^Exporting #\[(.*)\] from (Challenge|Solution)$',proof,re.M)
selected=json.loads((dest/'input-receipt.json').read_text())['theorem_names']
record={'source':'successful-verification/comparator.log','source_sha256':hashlib.sha256((dest/'successful-verification/comparator.log').read_bytes()).hexdigest(),'exports':[{'module':module,'all_logged_declarations':declarations.split(', '),'selected_declarations':[n for n in declarations.split(', ') if n.startswith('NLA.IE22.')]} for declarations,module in exports],'selected_theorem_count':len(selected),'raw_stream_scope':'Pinned Comparator removes temporary raw export streams; no retained stream hashes are claimed.'}
assert [x['module'] for x in record['exports']]==['Challenge','Solution']
assert all(x['selected_declarations']==selected for x in record['exports'])
(dest/'export-receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'destination':str(dest),'archive':meta,'export_modules':['Challenge','Solution'],'selected_theorem_count':len(selected)},indent=2))
