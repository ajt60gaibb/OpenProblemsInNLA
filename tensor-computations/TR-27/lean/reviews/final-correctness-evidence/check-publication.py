#!/usr/bin/env python3
"""Check the reviewed publication prose delta without changing historical input audits."""
from pathlib import Path
import hashlib, json, re, subprocess

package = Path(__file__).resolve().parents[2]
repo = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], cwd=package, text=True).strip())
receipt = json.loads((package / "reviews/final-correctness-publication-receipt.json").read_text())
inputs = json.loads((package / "verification/linux/successful-verification/result.json").read_text())["input_sha256"]
sha = lambda data: hashlib.sha256(data).hexdigest()
changed = {name for name, digest in inputs.items() if sha((package / name).read_bytes()) != digest}
assert changed == {"README.md", "formalization.yaml"}
for name, digest in receipt["final_current_document_sha256"].items():
    assert sha((package / name).read_bytes()) == digest, name
for name, digest in receipt["repository_document_sha256"].items():
    assert sha((repo / name).read_bytes()) == digest, name
print("PASS: exactly two approved status-document changes; other 114 verified input paths unchanged")

base = receipt["published_base"]
def original(name):
    return subprocess.check_output(["git", "show", base + ":" + name], cwd=repo)
canonical = (repo / "tensor-computations/TR-27/README.md").read_text()
old = original("tensor-computations/TR-27/README.md").decode()
assert canonical.split("## Problem statement\n", 1)[1] == old.split("## Problem statement\n", 1)[1]
def notice(text):
    return text.split("<!-- colbrook-tensor-metrics-rank -->", 1)[1].split("<!-- /colbrook-tensor-metrics-rank -->", 1)[0]
assert notice(canonical) == notice(old)
def feedback(text):
    return text.split("**Author feedback — 2026-09-17.**", 1)[1].split("\n\n", 1)[0]
assert feedback(canonical) == feedback(old)
for name in ["problem_ids.json", "references/colbrook-tensor-metrics-rank-2026-09-11/manuscripts/tr27_solution.tex"]:
    assert (repo / name).read_bytes() == original(name), name
heading = "## Lean proof and verification evidence - 2026-09-22"
inserted = heading + canonical.split(heading, 1)[1].split("## Problem statement", 1)[0]
approved = (package / "reviews/final-correctness-evidence/proposed-canonical-notice.md").read_text()
assert approved.count("```sh\n") == 1
expected = approved.replace("```sh\n", "```\n", 1)
assert expected.count('tools/lean/verify.sh tensor-computations/TR-27/lean /absolute/path/to/verification-tools') == 1
expected = expected.replace('tools/lean/verify.sh tensor-computations/TR-27/lean /absolute/path/to/verification-tools', 'tools/lean/verify.sh \\\n  tensor-computations/TR-27/lean \\\n  /absolute/path/to/verification-tools', 1)
assert inserted.strip() == expected.strip()
assert not re.search(r"[\w.+-]+@[\w.-]+\.[a-zA-Z]{2,}", canonical + (package / "README.md").read_text() + (package / "formalization.yaml").read_text())
print("PASS: original target/references, original notice, feedback, manuscript, IDs and approved new notice preserved")
print("PASS: no contact email added to current publication prose")
print("SCOPE: documentation/source preservation only; no new Lean run, catalog-generation test, or PDF visual review")
