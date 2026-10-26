#!/usr/bin/env python3
"""Rerun the corrected isolated kind control; preserve successful source builds."""
import datetime,hashlib,json,os,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
report=json.loads((HERE/'attempts/kind-control-missing-namespace/result.json').read_text())
assert [c['name'] for c in report['checks'] if not c['passed']]==['theorem-kind-guard-rejects-proof-valued-definition']
entry=next(c for c in report['commands'] if c['module']=='VerificationKindRejection')
path=Path(entry['argv'][-1]);old=(HERE/'attempts/kind-control-missing-namespace/VerificationKindRejection.lean.txt').read_bytes()
data=old.replace(b'import NLA.Statements.IE22\n',b'import NLA.Statements.IE22\nopen Lean Elab Command\n',1)
assert data!=old
path.write_bytes(data);(HERE/'consumers/VerificationKindRejection.lean.txt').write_bytes(data)
env=os.environ.copy();env['LEAN_PATH']=report['LEAN_PATH']
p=subprocess.run(entry['argv'],cwd=Path(report['private_build'])/'source',env=env,capture_output=True,text=True,timeout=120)
log=(p.stdout+p.stderr).encode();(HERE/'logs/VerificationKindRejection.log').write_bytes(log)
assert p.returncode==1 and b'review requires an actual theorem: VerificationFakeTheorem' in log
assert b'Unknown identifier' not in log and b'has not been implemented' not in log
replacement=dict(entry,exit_code=p.returncode,source_sha256=sha(data),log_sha256=sha(log))
report['commands']=[replacement if c['module']=='VerificationKindRejection' else c for c in report['commands']]
for c in report['checks']:
 if c['name']=='theorem-kind-guard-rejects-proof-valued-definition':c['passed']=True
report['kind_control_repair']=dict(UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='Only isolated reviewer kind-test namespace import repaired; all18 immutable proof/statement sources and successful exact/kernel consumer remain untouched',archived_prior_report_sha256=sha((HERE/'attempts/kind-control-missing-namespace/result.json').read_bytes()),argv=entry['argv'],exit_code=p.returncode,source_sha256=sha(data),log_sha256=sha(log),repair_script_sha256=sha(Path(__file__).read_bytes()))
report['script_sha256']=sha((HERE/'reproduce.py').read_bytes());report['passed']=all(c['passed'] for c in report['checks'])
(HERE/'result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(passed=report['passed'],checks=len(report['checks']),commands=len(report['commands']),declarations=len(report['declarations']),repair_exit=p.returncode)))
