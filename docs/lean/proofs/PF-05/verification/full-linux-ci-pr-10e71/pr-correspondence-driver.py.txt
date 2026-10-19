#!/usr/bin/env python3
"""Check actual PR-merge file correspondence without accepting a proof-head receipt.

Reads retained GitHub commit and complete small Git-tree responses. The strict
unchanged actual-artifact checker result remains independently authoritative.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

REPO = Path(__file__).resolve().parents[5]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--ref", required=True)
parser.add_argument("--evidence", type=Path, required=True)
args = parser.parse_args()
p = args.evidence
commit = json.loads((p / "merge-commit.json").read_text())
subtrees = json.loads((p / "merge-source-subtrees.json").read_text())
strict = json.loads((p / "independent-review-3.json").read_text())
result = json.loads(next((p / "artifact").rglob("result.json")).read_text())
run = json.loads((p / "run.json").read_text())
records = []
all_chains_valid = True
for subtree in subtrees:
    prefix = subtree["prefix"]
    tree_sha = commit["tree"]["sha"]
    for part in prefix.split("/"):
        raw = json.loads((p / "merge-source-trees" / (tree_sha + ".json")).read_text())
        assert not raw.get("truncated")
        assert raw["sha"] == tree_sha
        row = next(r for r in raw["tree"] if r["path"] == part)
        assert row["type"] == "tree"
        tree_sha = row["sha"]
    complete = json.loads((p / "merge-source-trees" / (tree_sha + "-recursive.json")).read_text())
    assert not complete.get("truncated")
    assert complete["sha"] == tree_sha == subtree["tree_sha"]
    assert complete["tree"] == subtree["entries"]
    merge_blobs = {prefix + "/" + row["path"]: row["sha"]
                   for row in subtree["entries"] if row["type"] == "blob"}
    reference_tree = subprocess.check_output(["git", "ls-tree", "-r", "-z",
        "--format=%(path) %(objectname)", args.ref, "--", prefix], cwd=REPO)
    reference_blobs = {row.rsplit(" ", 1)[0]: row.rsplit(" ", 1)[1]
                       for row in reference_tree.decode().split("\0") if row}
    files = []
    for name, oid in merge_blobs.items():
        data = subprocess.check_output(["git", "show", args.ref + ":" + name], cwd=REPO)
        actual_oid = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        files.append({"path": name, "merge_blob_oid": oid,
                      "proof_head_blob_oid": actual_oid,
                      "proof_head_sha256": hashlib.sha256(data).hexdigest(),
                      "identical": actual_oid == oid == reference_blobs.get(name)})
    records.append({"prefix": prefix, "merge_tree_sha": tree_sha,
                    "exact_file_set": merge_blobs.keys() == reference_blobs.keys(),
                    "files": files,
                    "identical": merge_blobs == reference_blobs and all(f["identical"] for f in files)})
project = next(r for r in records if r["prefix"] == "nonnegative-and-positive-factorizations/PF-05/lean")
prefix = "nonnegative-and-positive-factorizations/PF-05/lean/"
hashes = {f["path"][len(prefix):]: f["proof_head_sha256"] for f in project["files"]}
strict_failed = [c["name"] for c in strict["checks"] if not c["passed"]]
correspondence = (commit["sha"] == result["repository_commit"]
    and args.ref in [row["sha"] for row in commit["parents"]]
    and run["headSha"] == args.ref
    and hashes == result["input_sha256"]
    and all(r["identical"] for r in records)
    and len(strict["checks"]) == 41 and strict_failed == ["harness-source-commit"])
report = {"reviewer": "/root/lean_verification (independent Codex AI agent)",
          "scope": "Exact source correspondence of the actual accepted PR synthetic merge; not strict proof-head receipt acceptance",
          "workflow_head": args.ref, "actual_harness_merge_commit": result["repository_commit"],
          "merge_parents": [row["sha"] for row in commit["parents"]],
          "root_tree_sha": commit["tree"]["sha"], "complete_subtree_records": records,
          "actual_project_input_count": len(hashes),
          "actual_lean_input_count": sum(n.endswith(".lean") for n in hashes),
          "project_input_sha256_equals_actual_harness": hashes == result["input_sha256"],
          "source_correspondence_passed": correspondence,
          "strict_proof_head_receipt_passed": strict["passed"],
          "strict_failed_checks": strict_failed,
          "strict_audit": "independent-review-3.json",
          "promotion_approved": False,
          "limitations": ["The unchanged strict checker correctly fails the proof-head/actual-merge commit equality.",
              "This report verifies source correspondence only and does not waive that failure or authorize promotion.",
              "Only individually complete small subtrees and their complete path chains are used; no repository-wide recursive tree is relied upon.",
              "Retained GitHub commit/tree metadata has the same GitHub API trust boundary as the workflow/artifact metadata."]}
(p / "independent-pr-merge-correspondence.json").write_text(json.dumps(report, indent=2) + "\n")
(p / "pr-correspondence-driver.py.txt").write_bytes(Path(__file__).read_bytes())
print(json.dumps({"source_correspondence_passed": correspondence,
    "strict_proof_head_receipt_passed": strict["passed"], "strict_failed_checks": strict_failed,
    "files": {r["prefix"]: len(r["files"]) for r in records}}, indent=2))
raise SystemExit(0 if correspondence else 1)
