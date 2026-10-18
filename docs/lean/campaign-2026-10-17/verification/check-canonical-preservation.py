#!/usr/bin/env python3
"""Record permanent-ID, canonical page/status, and original artifact identity."""
import argparse
from datetime import date
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[4])
parser.add_argument("--base-ref", default="47006df8b3a6c724a557266c891893d03e69323a")
parser.add_argument("--output", type=Path, default=Path(__file__).with_name("canonical-preservation.json"))
parser.add_argument("--checked-on", default=date.today().isoformat())
args = parser.parse_args()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def blob(path):
    return subprocess.check_output(["git", "show", f"{args.base_ref}:{path}"], cwd=args.repo)


def status(data):
    match = re.search(r"^\*\*Status:\*\*\s*(.*?)\s*$", data.decode(), re.M)
    return match.group(1).strip() if match else None


registry_base = blob("problem_ids.json")
registry_current = (args.repo / "problem_ids.json").read_bytes()
registry = json.loads(registry_base)
all_paths = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", "-z", args.base_ref], cwd=args.repo).decode().split("\0")
pages, artifacts = [], []
for problem_id, canonical in sorted(registry.items()):
    base = blob(canonical)
    current_path = args.repo / canonical
    current = current_path.read_bytes() if current_path.is_file() else b""
    pages.append({"id": problem_id, "canonical_path": canonical,
                  "base_sha256": sha(base), "current_sha256": sha(current),
                  "base_status": status(base), "current_status": status(current),
                  "bytes_unchanged": base == current, "status_unchanged": status(base) == status(current)})
    parent = PurePosixPath(canonical).parent
    for name in all_paths:
        path = PurePosixPath(name)
        # Preserve every originally tracked immediate canonical artifact, including
        # problem and solution sources/PDFs. The new lean/ proof tree is separate.
        if name and path.parent == parent and name != canonical:
            original = blob(name)
            working = args.repo / name
            actual = working.read_bytes() if working.is_file() else b""
            artifacts.append({"id": problem_id, "path": name, "base_sha256": sha(original),
                              "current_sha256": sha(actual), "bytes_unchanged": original == actual})

source_paths = [
    "lean-statements/NLA/Statements/SP11.lean",
    "docs/lean/statements/SP-11/NUMERICAL_TARGETS.md",
    "docs/lean/statements/SP-11/ORIGINAL.md",
    "eigenvalues-and-inverse-problems/SP-11/solution.md",
    "references/stepaniants-sp11-sp12-2026-09-11/verification/SP-11-SP-12-independent-review.md",
]
sources = []
for name in source_paths:
    original, current = blob(name), (args.repo / name).read_bytes()
    sources.append({"path": name, "base_sha256": sha(original), "current_sha256": sha(current),
                    "bytes_unchanged": original == current})
report = {
    "schema_version": 1, "checked_on": args.checked_on,
    "reviewer": "/root/lean_verification (independent Codex AI agent)",
    "scope": "Byte identity of every registered canonical README/status, registry, original immediate problem artifacts, and selected SP-11 source/frozen boundary",
    "base_ref": args.base_ref,
    "registry": {"base_sha256": sha(registry_base), "current_sha256": sha(registry_current),
                 "bytes_unchanged": registry_base == registry_current,
                 "mappings_unchanged": registry == json.loads(registry_current), "published_id_count": len(registry)},
    "canonical_pages": pages, "original_artifacts": artifacts, "sp11_original_sources": sources,
    "summary": {"canonical_pages": len(pages), "original_artifacts": len(artifacts),
                "changed_canonical_pages": [p["id"] for p in pages if not p["bytes_unchanged"]],
                "changed_statuses": [p["id"] for p in pages if not p["status_unchanged"]],
                "changed_original_artifacts": [p["path"] for p in artifacts if not p["bytes_unchanged"]],
                "changed_sp11_sources": [p["path"] for p in sources if not p["bytes_unchanged"]]},
    "passed": registry_base == registry_current and all(p["bytes_unchanged"] for p in pages + artifacts + sources),
    "limitations": ["This is byte/status preservation evidence; it does not validate new Lean proofs or certify the semantics of changed future statements.",
                    "New proof and campaign review/evidence files are expected additions and are outside the unchanged-original set."]
}
args.output.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"passed": report["passed"], **report["summary"], "output": str(args.output)}, indent=2))
raise SystemExit(0 if report["passed"] else 1)
