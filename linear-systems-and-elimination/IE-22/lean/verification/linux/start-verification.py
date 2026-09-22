from pathlib import Path
import datetime,hashlib,json,os,subprocess
base=Path(__file__).resolve().parent
TART='/private/tmp/mf21-tart-2.37.0/tart.app/Contents/MacOS/tart'
env=os.environ.copy();env['TART_HOME']='/private/tmp/mf21-tart-vms'
input_receipt=json.loads((base/'input-receipt.json').read_text())
preflight=json.loads((base/'prerequisite-inspection.json').read_text())
publication=Path('/private/tmp/nla-ie22-publication-20260922')
for name,digest in preflight['driver_sha256'].items():
 assert hashlib.sha256((publication/'tools/lean'/name).read_bytes()).hexdigest()==digest,name
cmd=[TART,'exec','mf21-verification','/usr/bin/python3','/home/admin/nla-ie22-full-20260922/prepare-guest.py']
p=subprocess.run(cmd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(base/'preparation.log').write_text(p.stdout)
assert p.returncode==0,p.stdout
prep=json.loads(p.stdout)
assert prep['input_sha256']==input_receipt['input_sha256']
assert prep['publication_commit']==input_receipt['publication_commit']
assert prep['tracked_input_count']==len(input_receipt['input_sha256'])==394
assert prep['selected_theorem_count']==20
assert prep['project_validation']=='PASS' and prep['git_status']==''
assert prep['prior_project_build_artifacts'] is False
(base/'preparation.json').write_text(json.dumps(prep,indent=2)+'\n')
cmd=[TART,'exec','mf21-verification','/usr/bin/env','XDG_RUNTIME_DIR=/run/user/1000','DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus','systemd-run','--user','--unit=nla-ie22-full-20260922-r1','-p','RuntimeMaxSec=5400','-p','LimitNOFILE=65536','--working-directory=/home/admin/nla-ie22-full-20260922','/usr/bin/python3','/home/admin/nla-ie22-full-20260922/run-verifier.py']
p=subprocess.run(cmd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
record={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'command':cmd,'exit_code':p.returncode,'output':p.stdout,'publication_commit':prep['publication_commit'],'distinct_guest_commit':prep['guest_repository_commit']}
(base/'service-start.json').write_text(json.dumps(record,indent=2)+'\n')
assert p.returncode==0,p.stdout
print(json.dumps(record,indent=2))
