#!/usr/bin/env python3
"""Remote development checks only; never a complete problem-verification receipt."""
from pathlib import Path
import datetime, hashlib, json, os, platform, subprocess, sys

root = Path(__file__).resolve().parent
out = root / "evidence"
out.mkdir(exist_ok=True)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def sources():
    paths = []
    for directory, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in {".lake", "evidence", "__pycache__", ".git"}]
        paths.extend(Path(directory) / name for name in files)
    return {str(p.relative_to(root)): digest(p) for p in sorted(paths)}

receipt = {"kind": "development-elaboration-and-module-checks",
           "mathematical_verification": False, "comparator_run": False,
           "status": "running", "repository_commit": os.environ["GITHUB_SHA"],
           "run_id": os.environ["GITHUB_RUN_ID"], "run_attempt": os.environ["GITHUB_RUN_ATTEMPT"],
           "started_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
           "platform": platform.platform(), "uid": os.getuid(),
           "source_sha256": sources(), "commands": []}

def save():
    (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")

def run(argv, filename):
    print("RUN", repr(argv), flush=True)
    with (out / filename).open("w") as log:
        proc = subprocess.Popen(argv, cwd=root, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
        for line in proc.stdout:
            print(line, end="", flush=True)
            log.write(line)
        code = proc.wait()
    post_sources = sources()
    receipt["commands"].append({"argv": argv, "exit_code": code,
                                "log": filename, "sha256": digest(out / filename),
                                "source_sha256_after": post_sources})
    if post_sources != receipt["source_sha256"]:
        raise RuntimeError("development source changed during command")
    save()
    if code:
        raise RuntimeError(f"command failed ({code}): {argv}")

save()
try:
    if os.getuid() == 0 or platform.system() != "Linux":
        raise RuntimeError("Linux non-root execution required")
    projects = json.loads((root / "projects.json").read_text())
    run(["lean", "--version"], "lean-version.log")
    run(["lake", "env", "true"], "dependencies.log")
    pins = json.loads((root / "lake-manifest.json").read_text())["packages"]
    receipt["dependency_commits"] = {}
    for package in pins:
        actual = subprocess.check_output(["git", "-C", str(root / ".lake/packages" / package["name"]),
                                          "rev-parse", "HEAD"], text=True).strip()
        if actual != package["rev"]:
            raise RuntimeError(f"dependency revision mismatch: {package['name']}")
        receipt["dependency_commits"][package["name"]] = actual
    run(["lake", "exe", "cache", "get"], "mathlib-cache.log")
    failures = []
    for project in projects:
        checks = [(["lake", "build", *project["modules"]], f"{project['id']}-modules.log"),
                  (["lake", "env", "lean", project["challenge"]], f"{project['id']}-challenge.log")]
        for argv, filename in checks:
            try:
                run(argv, filename)
            except RuntimeError as exc:
                failures.append(str(exc))
    if failures:
        raise RuntimeError("Development checks failed: " + "; ".join(failures))
    if sources() != receipt["source_sha256"]:
        raise RuntimeError("development source changed during elaboration")
    receipt["status"] = "development-checks-passed-no-complete-problem-verification"
except Exception as exc:
    receipt["status"] = "failed"
    receipt["error"] = str(exc)
    raise
finally:
    receipt["finished_at"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    save()
