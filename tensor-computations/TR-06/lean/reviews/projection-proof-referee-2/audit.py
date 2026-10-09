from pathlib import Path
import json,os,subprocess,hashlib
root=Path(__file__).resolve().parent
receipt=json.loads((root/'evidence/receipt.json').read_text());env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(receipt['lean_path'])
cmd=['/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.tools/lean-4.33.1-darwin_aarch64/bin/lean','ExportAudit.lean']
r=subprocess.run(cmd,cwd=root,env=env,capture_output=True,text=True);log=r.stdout+r.stderr
(root/'evidence/ExportAudit.log').write_text(log)
(root/'evidence/ExportAudit.json').write_text(json.dumps({'command':cmd,'exit_code':r.returncode,'source_sha256':hashlib.sha256((root/'ExportAudit.lean').read_bytes()).hexdigest()},indent=2)+'\n')
print(log);raise SystemExit(r.returncode)
