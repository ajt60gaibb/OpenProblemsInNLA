"""Author-only statement validation. This is not independent review or Linux CI."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

project = Path(__file__).resolve().parents[1]
root = project.parents[2]
base = "8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc"
reviews = project / "reviews"
assert not (project / "Solution.lean").exists()
assert not (project / "NLA/FR12/Proof.lean").exists()
prefix = project / ".verification/statement-author"
prefix.mkdir(parents=True, exist_ok=True)
lean = subprocess.check_output(["lake", "env", "which", "lean"], cwd=project, text=True).strip()
path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=project, text=True).strip()
env = os.environ.copy()
env["LEAN_PATH"] = str(prefix) + ":" + path
records = []
for name, source, expected in [("definitions", "NLA/FR12/Definitions.lean", 0),
                               ("challenge", "Challenge.lean", 7),
                               ("inspection", "reviews/InspectStatements.lean", 0)]:
    command = [lean]
    if name != "inspection":
        target = prefix / Path(source).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        command += ["-o", str(target)]
    command.append(source)
    start = time.monotonic()
    result = subprocess.run(command, cwd=project, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    output = reviews / f"statement-{name}.log"
    output.write_bytes(result.stdout)
    record = {"command": command, "exit_code": result.returncode,
              "seconds": round(time.monotonic()-start, 3),
              "log": output.name, "sha256": hashlib.sha256(result.stdout).hexdigest()}
    records.append(record)
    print(json.dumps(record), flush=True)
    assert result.returncode == 0, result.stdout.decode(errors="replace")
    assert result.stdout.count(b"declaration uses `sorry`") == expected
    assert result.stdout.count(b"warning:") == expected

reconstruction = subprocess.run(["python3", "reviews/reconstruct.py"], cwd=project,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(reviews / "reconstruction.json").write_bytes(reconstruction.stdout)
assert reconstruction.returncode == 0, reconstruction.stdout.decode(errors="replace")
dependencies = []
for package in json.loads((project / "lake-manifest.json").read_text())["packages"]:
    package_path = project / ".lake/packages" / package["name"]
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=package_path, text=True).strip()
    dirty = subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"],
                                    cwd=package_path, text=True)
    assert actual == package["rev"] and not dirty
    dependencies.append({"name": package["name"], "rev": actual, "tracked_sources_clean": True})
(reviews / "statement-checks.json").write_text(json.dumps({
    "platform": "macOS arm64, author statement check, not independent review or Linux Comparator",
    "date_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "LEAN_PATH": env["LEAN_PATH"], "commands": records,
    "dependencies": dependencies, "reconstruction_exit_code": reconstruction.returncode,
    "proof_implementation_absent": True
}, indent=2) + "\n")

source_paths = ["frames-and-matrix-designs/FR-12/README.md",
                "frames-and-matrix-designs/FR-12/solution.md",
                "frames-and-matrix-designs/FR-12/solution.tex",
                "references/stepaniants-fr12-2026-09-12/REVIEW.md"]
sources = {}
for source in source_paths:
    actual = (root / source).read_bytes()
    canonical = subprocess.check_output(["git", "show", f"{base}:{source}"], cwd=root)
    assert actual == canonical
    sources[source] = hashlib.sha256(actual).hexdigest()
files = {}
for path in sorted(project.rglob("*")):
    rel = path.relative_to(project)
    if not path.is_file() or any(part in (".lake", ".verification") for part in rel.parts):
        continue
    if rel.as_posix() == "reviews/statement-freeze.json":
        continue
    files[rel.as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
freeze = {"stage": "Statements only; two independent approvals required before proof",
          "base_commit": base, "branch": "codex/lean-fr12-hadamard-enumeration",
          "files": files, "source_files": sources, "proof_files_present": False,
          "fresh_statement_modules_passed": 3, "intentional_challenge_holes": 7,
          "clean_dependency_pins": len(dependencies)}
(reviews / "statement-freeze.json").write_text(json.dumps(freeze, indent=2) + "\n")
print(json.dumps({"status": "PASS: author statement checks; not proof verification",
                  "frozen_files": len(files), "source_files": len(sources),
                  "freeze_sha256": hashlib.sha256((reviews / "statement-freeze.json").read_bytes()).hexdigest()}), flush=True)
