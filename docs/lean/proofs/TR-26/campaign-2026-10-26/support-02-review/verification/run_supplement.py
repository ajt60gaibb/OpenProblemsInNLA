#!/usr/bin/env python3
"""Exact support consumers and two infinity controls using the fresh audited closure."""
import hashlib,json,os,subprocess
from pathlib import Path
p=Path(__file__).resolve().parent
r=json.loads((p/"result.json").read_bytes());assert r["passed"]
build=Path(r["private_build"]);src=build/"source";obj=build/"out"
b=(p/"SupplementaryExactAudit.lean.txt").read_bytes();f=src/"SupplementaryExactAudit.lean";f.write_bytes(b)
env=os.environ.copy();env["LEAN_PATH"]=r["LEAN_PATH"]
argv=[r["commands"][0]["argv"][0],"-R",str(src),"-o",str(obj/"SupplementaryExactAudit.olean"),str(f)]
proc=subprocess.run(argv,cwd=src,env=env,capture_output=True,text=True,timeout=360)
log=proc.stdout+proc.stderr;(p/"logs/SupplementaryExactAudit.log").write_text(log)
sha=lambda b:hashlib.sha256(b).hexdigest()
report={"scope":"Exact fixed-degree iff/isotropic-factor/conditional-chart consumers, frozen Target identity and actual repeated-vs-simple projective infinity controls; no endpoint proved","checkpoint_commit":r["checkpoint_commit"],"passed":proc.returncode==0,"argv":argv,"exit_code":proc.returncode,"consumer_sha256":sha(b),"log_sha256":sha(log.encode()),"fresh_source_result_sha256":sha((p/"result.json").read_bytes()),"script_sha256":sha(Path(__file__).read_bytes())}
(p/"SUPPLEMENT.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report,indent=2));print(log);raise SystemExit(proc.returncode)

