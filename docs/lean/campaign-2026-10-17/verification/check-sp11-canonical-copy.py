#!/usr/bin/env python3
"""Bind completed canonical SP11 proof copies to shared and frozen source bytes."""
import hashlib
import json
from pathlib import Path
import subprocess

REPO = Path(__file__).resolve().parents[4]
PROJECT = REPO / "eigenvalues-and-inverse-problems/SP-11/lean"
OUT = Path(__file__).with_name("sp11-canonical-copy-check.json")
BASE = "47006df8b3a6c724a557266c891893d03e69323a"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


lock_path = PROJECT / "proof-source-lock.json"
lock = json.loads(lock_path.read_text())
historical = json.loads(Path(__file__).with_name("sp11-package-boundary-review").joinpath(
    "source/boundary-source-lock.json.txt").read_text())
checks = []
for item in lock["copies"]:
    actual_source = digest(REPO / item["source"])
    actual_destination = digest(REPO / item["destination"])
    checks.append({"name": "proof-copy:" + item["module"],
                   "source_sha256": actual_source, "destination_sha256": actual_destination,
                   "passed": actual_source == actual_destination == item["source_sha256"] == item["destination_sha256"]})
expected = {str(Path(item["destination"]).relative_to(PROJECT.relative_to(REPO))) for item in lock["copies"]}
actual = {str(p.relative_to(PROJECT)) for p in (PROJECT / "NLA").rglob("*.lean")}
checks.append({"name": "exact-NLA-copy-file-set", "passed": actual == expected,
               "extra": sorted(actual - expected), "missing": sorted(expected - actual)})
checks.append({"name": "closure-counts", "passed": len(lock["copies"]) == 38
               and lock["topological_module_count"] == 38 and lock["proof_module_count"] == 36})
for name, expected_sha in lock["package_exports"].items():
    actual_sha = digest(PROJECT / name)
    checks.append({"name": "export-lock:" + name, "sha256": actual_sha, "passed": actual_sha == expected_sha})
for item in historical["copied_sources"]:
    actual_sha = digest(PROJECT / item["package_path"])
    checks.append({"name": "original-copy:" + item["package_path"], "sha256": actual_sha,
                   "passed": actual_sha == item["sha256"] == digest(REPO / item["shared_source"])})
for name, expected_sha in historical["package_boundary"].items():
    path = PROJECT / name
    if name == "lakefile.toml":
        path = PROJECT / "reviews/boundary-scaffold-2026-10-18/lakefile.toml"
    checks.append({"name": "historical-boundary:" + name, "sha256": digest(path),
                   "passed": digest(path) == expected_sha})
for local, published in [
    ("NLA/Statements/SP11.lean", "lean-statements/NLA/Statements/SP11.lean"),
    ("NLA/Statements/Infrastructure.lean", "lean-statements/NLA/Statements/Infrastructure.lean"),
    ("Reviewed/SP11.lean", "lean-statements/Reviewed/SP11.lean"),
    ("ORIGINAL.md", "eigenvalues-and-inverse-problems/SP-11/README.md"),
]:
    original = subprocess.check_output(["git", "show", f"{BASE}:{published}"], cwd=REPO)
    checks.append({"name": "published-base:" + local,
                   "passed": (PROJECT / local).read_bytes() == original})
comparator = json.loads((PROJECT / "comparator.json").read_text())
checks.append({"name": "selected-exact-target-only", "passed": comparator["theorem_names"] == ["NLA.SP11.target"]
               and comparator["definition_names"] == [] and comparator["solution_module"] == "Solution"
               and comparator["challenge_module"] == "Challenge"
               and comparator["permitted_axioms"] == ["propext", "Classical.choice", "Quot.sound"]})
result = {"reviewer": "/root/lean_verification", "checked_on": "2026-10-18",
          "scope": "Exact copies and package export locks only; runtime Target proof checked separately",
          "proof_source_lock_sha256": digest(lock_path), "checks": checks,
          "passed": all(c["passed"] for c in checks), "linux_comparator": False}
OUT.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"passed": result["passed"], "checks": len(checks),
                  "failures": [c["name"] for c in checks if not c["passed"]]}, indent=2))
raise SystemExit(0 if result["passed"] else 1)
