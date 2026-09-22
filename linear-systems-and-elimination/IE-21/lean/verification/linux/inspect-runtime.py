from pathlib import Path
import datetime, hashlib, json, os, subprocess
base=Path(__file__).resolve().parent
TART='/private/tmp/mf21-tart-2.37.0/tart.app/Contents/MacOS/tart'
env=os.environ.copy();env['TART_HOME']='/private/tmp/mf21-tart-vms'
code=r'''
from pathlib import Path
import datetime,hashlib,json,os,subprocess,sys
os.environ.update({'PATH':'/home/admin/.elan/bin:/home/admin/mf21-tools/go/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin','XDG_RUNTIME_DIR':'/run/user/1000','DBUS_SESSION_BUS_ADDRESS':'unix:path=/run/user/1000/bus'})
commands=[['id'],['uname','-a'],['sysctl','kernel.apparmor_restrict_unprivileged_userns'],['/home/admin/.elan/bin/elan','run','leanprover/lean4:v4.33.1','lean','--version'],['/home/admin/.elan/bin/elan','run','leanprover/lean4:v4.33.1','lake','--version'],['go','version'],['bwrap','--version'],['systemctl','--user','is-system-running'],['systemctl','is-active','apt-daily-upgrade.service'],['df','-h','/home/admin']]
records=[]
for cmd in commands:
 p=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 records.append({'command':cmd,'exit_code':p.returncode,'output':p.stdout})
sys.path.insert(0,'/home/admin/mf21-harness/tools/lean');import harness
receipt,_=harness.validated_tools(Path('/home/admin/nla-lean-tools'))
record={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'commands':records,'validated_tools':'PASS','tool_receipt':receipt,'driver_sha256':{name:hashlib.sha256((Path('/home/admin/mf21-harness/tools/lean')/name).read_bytes()).hexdigest() for name in ['harness.py','verify.sh','source-lock.json']},'verification_started':False,'IE21_source_transferred':False}
assert os.getuid()==1000
print(json.dumps(record,indent=2))
'''
cmd=[TART,'exec','mf21-verification','/usr/bin/python3','-c',code]
p=subprocess.run(cmd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(base/'prerequisite-inspection.log').write_text(p.stdout)
assert p.returncode==0,p.stdout
record=json.loads(p.stdout)
for name,digest in record['driver_sha256'].items():
 local=Path('/private/tmp/nla-solved-campaign-20260922/tools/lean')/name
 assert hashlib.sha256(local.read_bytes()).hexdigest()==digest,name
(base/'prerequisite-inspection.json').write_text(json.dumps(record,indent=2)+'\n')
state=json.loads(subprocess.check_output([TART,'list','--format','json'],env=env,text=True))
vm=next(v for v in state if v['Name']=='mf21-verification');assert vm['Running']
life={'vm':'mf21-verification','started_by_this_verification_task':True,'retained_exec_session_id':43940,'boot_command':[TART,'run','--no-graphics','--no-audio','--no-clipboard','mf21-verification'],'TART_HOME':'/private/tmp/mf21-tart-vms','configuration_changed':False,'host_filesystem_shared':False,'running_observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'state':vm,'stop_required_after_evidence_export':True}
(base/'vm-lifecycle.json').write_text(json.dumps(life,indent=2)+'\n')
print(json.dumps(record,indent=2))
