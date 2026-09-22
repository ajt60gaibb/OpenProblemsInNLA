from pathlib import Path
import datetime,hashlib,json,os,subprocess
base=Path(__file__).resolve().parent
TART='/private/tmp/mf21-tart-2.37.0/tart.app/Contents/MacOS/tart'
env=os.environ.copy();env['TART_HOME']='/private/tmp/mf21-tart-vms'
policy=Path('/private/tmp/nla-ie22-publication-20260922/.github/workflows/lean-verification.yml')
assert 'sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0' in policy.read_text()
steps=[]
for cmd in [['sysctl','kernel.apparmor_restrict_unprivileged_userns'],['sudo','-n','sysctl','-w','kernel.apparmor_restrict_unprivileged_userns=0'],['sysctl','kernel.apparmor_restrict_unprivileged_userns']]:
 p=subprocess.run([TART,'exec','mf21-verification',*cmd],env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 steps.append({'guest_command':cmd,'exit_code':p.returncode,'output':p.stdout})
 assert p.returncode==0,p.stdout
assert steps[-1]['output'].strip()=='kernel.apparmor_restrict_unprivileged_userns = 0'
record={'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'operator':'Codex AI /root/infrastructure_audit, mechanical operator and author of separate IE-22 Gaussian Poincare, hinge and variance modules, and vendored IE-21 Gaussian/spherical modules; not final independent referee','reason':'VM reboot restored user namespace restriction to 1. Restore documented shared CI prerequisite without changing harness, controls or proof sources.','policy_source':'.github/workflows/lean-verification.yml','policy_sha256':hashlib.sha256(policy.read_bytes()).hexdigest(),'steps':steps,'verification_started':False,'IE22_source_transferred':False}
(base/'environment-repair.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
