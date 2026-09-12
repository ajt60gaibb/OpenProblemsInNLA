"""Author fresh-source elaboration; not independent review or Linux Comparator."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import tempfile

project = Path(sys.argv[1]).resolve()
problem = sys.argv[2]
referee = sys.argv[3]
modules = sys.argv[4:]
evidence = project / "verification" / "author-completion"
prefix = Path(tempfile.mkdtemp(prefix=f"nla-{problem}-root-final-{referee}-", dir="/tmp"))
evidence.mkdir(parents=True, exist_ok=True)
prefix.mkdir(parents=True, exist_ok=True)
files = [f"{m.replace('.', '/')}.lean" for m in modules]
files += ["Challenge.lean", "NUMERICAL_TARGETS.md", "lakefile.toml", "lake-manifest.json", "lean-toolchain"]
for extra in ["SOURCE_CORRESPONDENCE.md", "comparator.json", "reviews/statement-freeze.json", "reviews/statement-referee-1.md", "reviews/statement-referee-2.md", "verification/proof-start.json"]:
    if (project / extra).exists(): files.append(extra)
def manifest():
    return {f: {"sha256": hashlib.sha256((project/f).read_bytes()).hexdigest(), "bytes": (project/f).stat().st_size} for f in files}
before = manifest()
lean_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=project, text=True).strip()
lean = subprocess.check_output(["lake", "env", "which", "lean"], cwd=project, text=True).strip()
env = os.environ.copy()
paths = []
for raw in lean_path.split(":"):
    resolved = Path(raw) if Path(raw).is_absolute() else project / raw
    resolved = resolved.resolve()
    if resolved == (project / ".lake/build/lib/lean").resolve():
        continue
    paths.append(str(resolved))
assert all(str(project / ".lake/build/lib/lean") != x for x in paths)
env["LEAN_PATH"] = ":".join([str(prefix), *paths])
records = []
for module in modules:
    source = module.replace(".", "/") + ".lean"
    target = prefix / (module.replace(".", "/") + ".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    cmd = [lean, "-o", str(target), source]
    started = time.monotonic()
    result = subprocess.run(cmd, cwd=project, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    logfile = evidence / (module.replace(".", "-") + ".log")
    logfile.write_bytes(result.stdout)
    record = {"module": module, "command": cmd, "exit_code": result.returncode, "elapsed_seconds": round(time.monotonic()-started, 3), "object_sha256": hashlib.sha256(target.read_bytes()).hexdigest() if target.exists() else None, "log": str(logfile.relative_to(project)), "log_sha256": hashlib.sha256(result.stdout).hexdigest()}
    records.append(record)
    (evidence/"execution.json").write_text(json.dumps({"platform": "local macOS arm64; not Linux Comparator", "lean": lean, "LEAN_PATH": env["LEAN_PATH"], "commands": records}, indent=2)+"\n")
    print(json.dumps(record), flush=True)
    if result.returncode:
        print(result.stdout.decode(errors="replace"), flush=True)
        raise SystemExit(result.returncode)
after = manifest()
assert before == after, "Reviewed sources changed during fresh elaboration"
axioms = []
for r in records:
    content = (project/r["log"]).read_text()
    assert "warning:" not in content and "error:" not in content
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", content):
        names = sorted(x.strip() for x in raw.split(",") if x.strip())
        assert names == ["Classical.choice", "Quot.sound", "propext"], (name,names)
        axioms.append({"declaration": name, "axioms": names})
(evidence/"axioms.json").write_text(json.dumps({"status": "PASS", "count": len(axioms), "records": axioms}, indent=2)+"\n")
(evidence/"source-identity.json").write_text(json.dumps({"before_equals_after": True, "files": before}, indent=2)+"\n")
print(json.dumps({"status": "PASS", "axiom_checks":len(axioms), "evidence":str(evidence)}), flush=True)
