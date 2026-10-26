#!/usr/bin/env python3
"""Independent local source/LeanCert replay; never a Linux/CI receipt."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

parser = argparse.ArgumentParser()
parser.add_argument("--lean", required=True, type=Path)
parser.add_argument("--packages", required=True, type=Path)
args = parser.parse_args()
OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[1]
FILES = ["NLA/Statements/Infrastructure.lean", "NLA/Statements/RA05.lean",
         "NLA/Proofs/RA05/SupportMinimum.lean", "SupportAudit.lean"]
source = {p: (ROOT / p).read_bytes() for p in FILES + ["Challenge.lean", "CONTRACT.md"]}
hashes = {p: hashlib.sha256(data).hexdigest() for p, data in source.items()}
lock = json.loads((ROOT / "SOURCE_LOCK.json").read_text())
for path in FILES[:2]:
    assert hashes[path] == lock["files"][path]
    original = subprocess.check_output(["git", "show", f"{lock['published_base']}:lean-statements/{path}"])
    assert source[path] == original


def signatures(data):
    return [" ".join(s.split()) for s in re.findall(r"(?ms)^theorem (.*?) := by", data.decode())]


expected = signatures(source["Challenge.lean"])
actual = signatures(source["NLA/Proofs/RA05/SupportMinimum.lean"])
assert len(expected) == 8 and expected == actual
result = {
    "scope": "Independent local macOS source replay using shared pinned dependency caches; not a dependency rebuild, full RA05 proof, Linux replay, CI or Comparator receipt.",
    "reviewer": "/root/inventory", "published_base": lock["published_base"],
    "input_sha256": hashes, "eight_signatures_equal_challenge": True,
    "published_definition_copies_equal": True,
    "lean_version": subprocess.check_output([str(args.lean), "--version"], text=True).strip(),
    "files": [],
}
with tempfile.TemporaryDirectory(prefix="nla-ra05-minimum-inventory-review-") as temporary:
    temp = Path(temporary)
    source_root = temp / "source"
    build_root = temp / "build"
    env = os.environ.copy()
    paths = [str(build_root)] + [str(p / ".lake/build/lib/lean") for p in sorted(args.packages.iterdir())
                                  if (p / ".lake/build/lib/lean").is_dir()]
    env["LEAN_PATH"] = ":".join(paths + [str(args.lean.parent.parent / "lib/lean")])
    result["shared_dependency_cache_paths"] = paths[1:]
    for relative in FILES:
        source_file = source_root / relative
        source_file.parent.mkdir(parents=True, exist_ok=True)
        source_file.write_bytes(source[relative])
        target = build_root / Path(relative).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        argv = [str(args.lean), "-R", str(source_root), "-o", str(target), str(source_file)]
        process = subprocess.run(argv, cwd=source_root, env=env, capture_output=True, text=True, timeout=180)
        log = relative.replace("/", "-") + ".log"
        (OUT / log).write_text(process.stdout + process.stderr)
        snapshot = OUT / "source" / (relative + ".txt")
        snapshot.parent.mkdir(parents=True, exist_ok=True)
        snapshot.write_bytes(source[relative])
        result["files"].append({"source": relative, "sha256": hashes[relative],
                                "argv": argv, "exit_code": process.returncode,
                                "log": log, "stdout": process.stdout, "stderr": process.stderr})
        print(relative, process.returncode, flush=True)
        if process.returncode:
            break
result["inputs_unchanged_after_replay"] = all((ROOT / p).read_bytes() == b for p, b in source.items())
result["passed"] = len(result["files"]) == len(FILES) and all(f["exit_code"] == 0 for f in result["files"]) and result["inputs_unchanged_after_replay"]
(OUT / "result.json").write_text(json.dumps(result, indent=2) + "\n")
raise SystemExit(0 if result["passed"] else 1)
