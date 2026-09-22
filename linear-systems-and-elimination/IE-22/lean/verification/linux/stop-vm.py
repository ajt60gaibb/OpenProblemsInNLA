from pathlib import Path
import datetime,json,os,subprocess
base=Path(__file__).resolve().parent
TART='/private/tmp/mf21-tart-2.37.0/tart.app/Contents/MacOS/tart'
env=os.environ.copy();env['TART_HOME']='/private/tmp/mf21-tart-vms'
life=json.loads((base/'vm-lifecycle.json').read_text())
assert life['started_by_this_verification_task'] is True and life['retained_exec_session_id']==82049
state=json.loads(subprocess.check_output([TART,'list','--format','json'],env=env,text=True))
vm=next(v for v in state if v['Name']=='mf21-verification')
assert vm['Running'],vm
cmd=[TART,'stop','mf21-verification','--timeout','30']
p=subprocess.run(cmd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
state=json.loads(subprocess.check_output([TART,'list','--format','json'],env=env,text=True))
vm=next(v for v in state if v['Name']=='mf21-verification')
record={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'vm':'mf21-verification','started_by_this_task':True,'retained_exec_session_id':82049,'stop_command':cmd,'stop_exit_code':p.returncode,'stop_output':p.stdout,'final_state':vm,'disk_and_sources_preserved':True,'frozen_operational_report_unchanged':True,'frozen_evidence_manifest_unchanged':True,'boot_session_completion':'Pending separate tool wait confirmation'}
(base/'vm-cleanup.json').write_text(json.dumps(record,indent=2)+'\n')
assert p.returncode==0 and not vm['Running'],record
print(json.dumps(record,indent=2))
