"""Independent root publication identity check; no proof rebuild or Linux claim."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import yaml

root = Path(__file__).resolve().parents[5]
project = root / "matrix-inequalities-and-norms/MI-26/lean"
record_dir = Path(__file__).resolve().parent
verified = "81176af27e570b59ba1e1a0745e28944e7d57c03"
upstream = "8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc"

def git(*args):
    return subprocess.check_output(["git", *args], cwd=root)

def blob(rev, path):
    return git("show", rev + ":" + path)

def sha(data):
    return hashlib.sha256(data).hexdigest()

assert git("rev-parse", "HEAD").decode().strip() == verified
subprocess.run(["git", "merge-base", "--is-ancestor", upstream, verified], cwd=root, check=True)
prefix = str(project.relative_to(root)) + "/"
old_files = git("ls-tree", "-r", "--name-only", verified, "--", prefix).decode().splitlines()
assert len(old_files) == 118
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
    if code != "MI-26":
        assert data == blob(upstream, name), code
    else:
        marker = b"## Problem statement"
        assert data.split(marker, 1)[1].strip() == blob(upstream, name).split(marker, 1)[1].strip()
for name in ["solution.md", "solution.tex", "solution.pdf"]:
    full = "matrix-inequalities-and-norms/MI-26/" + name
    assert (root/full).read_bytes() == blob(upstream, full), name
assert counts == {"Open": 57, "Partially resolved": 71, "Solved": 82, "Lean verified": 7}, counts

shared = git("ls-tree", "-r", "--name-only", upstream, "--", "tools/lean", "docs/lean",
             ".github/workflows/lean-verification.yml").decode().splitlines()
for name in shared:
    assert (root/name).read_bytes() == blob(upstream, name), name

linux = project/"verification/linux-2026-09-12"
manifest = json.loads((linux/"EVIDENCE-MANIFEST.json").read_text())["files"]
assert len(manifest) == 228
run = json.loads((linux/"run-metadata.json").read_text())
assert run["conclusion"] == "success" and run["head_sha"] == verified and run["id"] == 34713045511
for name, item in manifest.items():
    assert sha((linux/name).read_bytes()) == item["sha256"], name
before = json.loads((record_dir/"before.json").read_text())["operational_evidence"]
assert len(before) == 229
for name, expected in before.items():
    assert sha((linux/name).read_bytes()) == expected, name
assert sha((linux/"OPERATIONAL-REVIEW.md").read_bytes()) == \
    "9eae3acf9521e1dff4e9f4d8344ae3c7086687ed5655d973c8d939de4b9b09e0"

old_yaml = yaml.safe_load(blob(verified, prefix + "formalization.yaml"))
new_yaml = yaml.safe_load((project/"formalization.yaml").read_text())
for key, subkey in [("status", "scope"), ("review", "status"), ("review", "notes")]:
    old_yaml[key].pop(subkey)
    new_yaml[key].pop(subkey)
assert old_yaml == new_yaml, "Unexpected semantic manifest change"
assert "George Stepaniants" in (root/"RESOLVED.md").read_text()
for f in [project/"README.md", project/"formalization.yaml", project.parent/"README.md"]:
    assert "Department of Computing and Mathematical Sciences" in f.read_text().replace("\n", " ")
    assert not re.search(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}", f.read_text())

commands = []
for cmd in [
    ["python3", "tools/validate_problem_ids.py", "--base-ref", "origin/main"],
    ["python3", "tools/validate_problem_ids.py", "--base-ref", upstream],
    ["/tmp/nla-lean-formalization/venv/bin/python", "tools/lean/validate_manifest.py", prefix.rstrip("/")],
]:
    result = subprocess.run(cmd, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    commands.append({"command": cmd, "exit_code": result.returncode, "output": result.stdout.decode()})
    assert result.returncode == 0, result.stdout
assert "Ran 17 tests" in (record_dir/"id-tests.log").read_text()
assert (record_dir/"id-tests.log").read_text().rstrip().endswith("OK")
assert "Lean verified=7" in (record_dir/"catalog.log").read_text()

pub_names = ["CATALOG.md", "README.md", "RESOLVED.md", "matrix-inequalities-and-norms/README.md",
             "matrix-inequalities-and-norms/MI-26/README.md",
             "matrix-inequalities-and-norms/MI-26/problem.tex",
             "matrix-inequalities-and-norms/MI-26/problem.pdf", prefix+"README.md", prefix+"formalization.yaml"]
report = {"status": "PASS", "verified_commit": verified, "integrated_upstream": upstream,
          "preserved_original_project_inputs": preserved, "other_canonical_pages_preserved": 216,
          "permanent_IDs": 217, "counts": dict(counts), "shared_files_preserved": len(shared),
          "linux_evidence_files_preserved": 229, "commands": commands,
          "publication_sha256": {name: sha((root/name).read_bytes()) for name in pub_names},
          "independent_pdf_inspection": "Root visually inspected both rendered pages; no clipping, overlap, broken formula or missing name/affiliation found.",
          "proof_rebuild": "Not repeated: all proof and configuration bytes are unchanged from the actually verified revision."}
(record_dir/"ROOT-CHECKS.json").write_text(json.dumps(report, indent=2)+"\n")
print(json.dumps({k: v for k,v in report.items() if k not in ["preserved_original_project_inputs", "publication_sha256", "commands"]}, indent=2))
