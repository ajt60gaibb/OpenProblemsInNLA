"""Independent root publication identity check; no proof rebuild or Linux claim."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[5]
project = root / "matrix-inequalities-and-norms/MI-21/lean"
record_dir = Path(__file__).resolve().parent
verified = "06ade659dee260a18b79ce638383bf0a49125ecf"
upstream = "8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc"

def git(*args):
    return subprocess.check_output(["git", *args], cwd=root)

def blob(rev, path):
    return git("show", rev + ":" + path)

def sha(data):
    return hashlib.sha256(data).hexdigest()

assert git("rev-parse", "HEAD").decode().strip() == verified
assert git("rev-parse", "MERGE_HEAD").decode().strip() == upstream
prefix = str(project.relative_to(root)) + "/"
old_files = git("ls-tree", "-r", "--name-only", verified, "--", prefix).decode().splitlines()
assert len(old_files) == 81
preserved = {}
for name in old_files:
    if name in [prefix + "README.md", prefix + "formalization.yaml"]:
        continue
    data = (root/name).read_bytes()
    assert data == blob(verified, name), name
    preserved[name] = sha(data)

registry = (root/"problem_ids.json").read_bytes()
assert registry == blob(upstream, "problem_ids.json")
ids = json.loads(registry)
assert len(ids) == 217
counts = Counter()
for code, name in ids.items():
    data = (root/name).read_bytes()
    counts[re.search(rb"\*\*Status:\*\* ([^\r\n]+)", data).group(1).decode().strip()] += 1
    if code != "MI-21":
        assert data == blob(upstream, name), code
    else:
        marker = b"## Problem statement"
        assert data.split(marker, 1)[1] == blob(upstream, name).split(marker, 1)[1]
for name in ["solution.md", "solution.tex", "solution.pdf"]:
    full = "matrix-inequalities-and-norms/MI-21/" + name
    assert (root/full).read_bytes() == blob(upstream, full), name
assert counts == {"Open": 57, "Partially resolved": 71, "Solved": 82, "Lean verified": 7}, counts

shared = git("ls-tree", "-r", "--name-only", upstream, "--", "tools/lean", "docs/lean",
             ".github/workflows/lean-verification.yml").decode().splitlines()
for name in shared:
    assert (root/name).read_bytes() == blob(upstream, name), name

linux = project/"verification/linux-2026-09-12"
manifest = json.loads((linux/"EVIDENCE-MANIFEST.json").read_text())
assert manifest["verdict"] == "PASS" and manifest["commit"] == verified
assert manifest["run"] == 34709291489 and len(manifest["files"]) == 58
for name, item in manifest["files"].items():
    assert sha((linux/name).read_bytes()) == item["sha256"], name
assert sha((linux/"OPERATIONAL-REVIEW.md").read_bytes()) == \
    "d00b70b1357257e9faf9ac8f5cc83c47bd6458783d54248c5b6ca26eb24ee1be"

commands = []
for cmd in [
    ["python3", "tools/validate_problem_ids.py", "--base-ref", "origin/main"],
    ["python3", "tools/validate_problem_ids.py", "--base-ref", upstream],
    ["/tmp/nla-lean-formalization/venv/bin/python", "tools/lean/validate_manifest.py", prefix.rstrip("/")],
]:
    result = subprocess.run(cmd, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    commands.append({"command": cmd, "exit_code": result.returncode, "output": result.stdout.decode()})
    assert result.returncode == 0, result.stdout
assert "Ran 17 tests" in (record_dir/"problem-id-tests.log").read_text()
assert (record_dir/"problem-id-tests.log").read_text().rstrip().endswith("OK")
assert "Lean verified=7" in (record_dir/"catalog-generation.log").read_text()

pub_names = ["CATALOG.md", "README.md", "RESOLVED.md", "matrix-inequalities-and-norms/README.md",
             "matrix-inequalities-and-norms/MI-21/README.md",
             "matrix-inequalities-and-norms/MI-21/problem.tex",
             "matrix-inequalities-and-norms/MI-21/problem.pdf", prefix+"README.md", prefix+"formalization.yaml"]
report = {"status": "PASS", "verified_commit": verified, "integrated_upstream": upstream,
          "preserved_original_project_inputs": preserved, "other_canonical_pages_preserved": 216,
          "permanent_IDs": 217, "counts": dict(counts), "shared_files_preserved": len(shared),
          "linux_evidence_files_preserved": 58, "commands": commands,
          "publication_sha256": {name: sha((root/name).read_bytes()) for name in pub_names},
          "independent_pdf_inspection": "Root visually inspected both rendered pages; no clipping, overlap, broken formula or missing name/affiliation found.",
          "proof_rebuild": "Not repeated: all proof and configuration bytes are unchanged from the actually verified revision."}
(record_dir/"ROOT-CHECKS.json").write_text(json.dumps(report, indent=2)+"\n")
print(json.dumps({k: v for k,v in report.items() if k not in ["preserved_original_project_inputs", "publication_sha256", "commands"]}, indent=2))
