from pathlib import Path
import datetime
import json
import os
import subprocess
import sys

base = Path("/home/admin/nla-tr27-full-20260922")
repo = base / "repo"
log = base / "verification-driver-attempt-1.log"
record_path = base / "runner-result-attempt-1.json"
env = os.environ.copy()
env.update({"PATH": "/home/admin/.elan/bin:/home/admin/mf21-tools/go/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
            "XDG_RUNTIME_DIR": "/run/user/1000",
            "DBUS_SESSION_BUS_ADDRESS": "unix:path=/run/user/1000/bus"})
env.pop("NLA_LEAN_SKIP_CACHE", None)
command = ["/home/admin/mf21-harness/tools/lean/verify.sh", "tensor-computations/TR-27/lean", "/home/admin/nla-lean-tools"]
record = {"scope": "complete original TR-27 target and all25 frozen required declarations",
          "operator_role": "mechanical verifier operator; authored ProjectiveGeometry; not an independent final referee",
          "command": command, "cwd": str(repo),
          "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
          "status": "running"}
record_path.write_text(json.dumps(record, indent=2) + "\n")
with log.open("w") as stream:
    result = subprocess.run(command, cwd=repo, env=env, stdout=stream, stderr=subprocess.STDOUT)
record.update({"status": "finished", "exit_code": result.returncode,
               "finished_utc": datetime.datetime.now(datetime.timezone.utc).isoformat()})
record_path.write_text(json.dumps(record, indent=2) + "\n")
sys.exit(result.returncode)
