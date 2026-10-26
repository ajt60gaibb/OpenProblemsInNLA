#!/usr/bin/env python3
"""Check that adding TR14 proofs changes no registered original page or artifact."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess

REPO = Path(__file__).resolve().parents[4]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--base-ref", default="d250bd50d602ec7fd6e55bb4fd19494c5e19b045")
parser.add_argument("--output", type=Path, default=Path(__file__).with_name("preservation-before-linux.json"))
args = parser.parse_args()
base = subprocess.check_output(["git", "rev-parse", args.base_ref], cwd=REPO, text=True).strip()
def original(name):
    return subprocess.check_output(["git", "show", base + ":" + name], cwd=REPO)
def sha(data):
    return hashlib.sha256(data).hexdigest()
registry_bytes = original("problem_ids.json")
registry = json.loads(registry_bytes)
tracked = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", "-z", base], cwd=REPO).decode().split("\0")
parents = {str(PurePosixPath(p).parent) for p in registry.values()}
names = sorted(p for p in tracked if p and str(PurePosixPath(p).parent) in parents)
records = []
for name in names:
    old = original(name)
    path = REPO / name
    new = path.read_bytes() if path.is_file() else b""
    records.append({"path": name, "base_sha256": sha(old), "current_sha256": sha(new), "unchanged": old == new})
checks = [
    {"name": "registry-bytes", "passed": (REPO / "problem_ids.json").read_bytes() == registry_bytes},
    {"name": "canonical-paths", "passed": all((REPO / p).is_file() for p in registry.values()), "count": len(registry)},
    {"name": "all-original-pages-and-immediate-artifacts", "passed": all(r["unchanged"] for r in records), "count": len(records)},
]
result = {"date": "2026-10-18", "reviewer": "/root (AI agent; reproducible byte-preservation check)", "base_ref": base,
          "scope": "Exact preservation of every registered canonical README and all immediate tracked original problem artifacts before TR14 status promotion",
          "checks": checks, "files": records, "passed": all(c["passed"] for c in checks)}
args.output.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"passed": result["passed"], "checks": len(checks), "files": len(records), "changed": [r["path"] for r in records if not r["unchanged"]]}))
raise SystemExit(0 if result["passed"] else 1)
