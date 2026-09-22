from pathlib import Path
import json,os,subprocess
base=Path(__file__).resolve().parent
TART='/private/tmp/mf21-tart-2.37.0/tart.app/Contents/MacOS/tart'
env=os.environ.copy();env['TART_HOME']='/private/tmp/mf21-tart-vms'
code=r'''
from pathlib import Path
import json
base=Path('/home/admin/nla-ie22-full-20260922')
print((base/'runner-result-attempt-1.json').read_text())
log=base/'verification-driver-attempt-1.log'
if log.exists():print('DRIVER TAIL\n'+'\n'.join(log.read_text().splitlines()[-12:]))
logs=sorted(Path('/home/admin/nla-lean-tools/logs').glob('verify-*'))
if logs:
 latest=logs[-1];print('LATEST LOG DIRECTORY',latest)
 for f in sorted(latest.glob('*.log')):
  print(f.name,'\n'+'\n'.join(f.read_text().splitlines()[-3:]))
print('Dependency receipt captured:',(base/'dependency-evidence/dependency-receipt.json').exists())
'''
p=subprocess.run([TART,'exec','mf21-verification','/usr/bin/python3','-c',code],env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
print(p.stdout);raise SystemExit(p.returncode)
