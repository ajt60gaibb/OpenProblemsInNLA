#!/usr/bin/env python3
"""Check pinned source/dependency correspondence; this is not a proof checker."""
import hashlib
import json
from pathlib import Path
import subprocess


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


project = Path(__file__).resolve().parents[1]
repository = project.parents[2]
lock = json.loads((project / "verification/source-lock.json").read_text())
require((project / "lean-toolchain").read_text().strip() == lock["lean_toolchain"],
        "Lean toolchain changed")
for local, source in lock["statement_sources"].items():
    require(digest(project / local) == source["sha256"], f"Changed reviewed copy: {local}")
    original = repository / source["repository_path"]
    if original.exists():
        require(digest(original) == source["sha256"], f"Changed repository statement: {original}")
for local, source in lock.get("shared_sources", {}).items():
    original = repository / source
    if original.exists():
        require((project / local).read_bytes() == original.read_bytes(),
                f"Shared bridge differs: {local}")

manifest = json.loads((project / "lake-manifest.json").read_text())
pins = {p["name"]: p["rev"] for p in manifest["packages"]}
require(pins == lock["dependency_revisions"], "Dependency manifest differs from source lock")
for name, revision in pins.items():
    package = project / ".lake/packages" / name
    actual = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=package, text=True).strip()
    require(actual == revision, f"Wrong dependency revision: {name}")
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--"], cwd=package, check=True,
                   stdout=subprocess.DEVNULL)
for local, sha256 in lock["komlos_sources"].items():
    require(digest(project / ".lake/packages/Komlos" / local) == sha256,
            f"Changed external proof source: {local}")
print("PASS: reviewed statement bytes, shared bridge, toolchain and all dependency source pins")
