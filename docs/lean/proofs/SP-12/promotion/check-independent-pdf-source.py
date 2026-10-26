#!/usr/bin/env python3
"""Replay independent archive/math-source checks; visual findings are human/agent review data.

The PDF was read-only rendered with the bundled pdftoppm and all three PNGs were
visually inspected by /root/lean_verification. This script records source/image
identity and checks math preservation; it does not automate visual judgment.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess

REPO = Path(__file__).resolve().parents[5]
PROOF = REPO / "docs/lean/proofs/SP-12"
ARCHIVE = PROOF / "originals-main-36767"
OUT = PROOF / "promotion"
manifest = json.loads((ARCHIVE / "manifest.json").read_text())
checks = []


def sha(data):
    return hashlib.sha256(data).hexdigest()


def check(name, passed, **evidence):
    checks.append(dict(name=name, passed=bool(passed), **evidence))


check("exact-three-original-archive-files",
      {x["archive_file"] for x in manifest["files"]} == {"README.md", "problem.tex", "problem.pdf"})
for item in manifest["files"]:
    data = (ARCHIVE / item["archive_file"]).read_bytes()
    original = subprocess.check_output(["git", "show", manifest["base_commit"] + ":" + item["original_path"]], cwd=REPO)
    check("archive-published-base:" + item["archive_file"], data == original and sha(data) == item["sha256"])
old = (ARCHIVE / "problem.tex").read_text()
new = (REPO / "eigenvalues-and-inverse-problems/SP-12/problem.tex").read_text()


def math_expressions(text):
    return [re.sub(r"\s+", "", x or y)
            for x, y in re.findall(r"\\\[(.*?)\\\]|\\\((.*?)\\\)", text, re.S)]


check("all-original-TeX-math-expressions-preserved", math_expressions(old) == math_expressions(new),
      math_expression_count=len(math_expressions(old)))
images = sorted((OUT / "independent-renderings").glob("*.png"))
check("all-three-pages-independently-rendered", len(images) == 3)
result = {
    "reviewer": "/root/lean_verification", "read_only_pdf_review": True, "checks": checks,
    "pdf_sha256": sha((REPO / "eigenvalues-and-inverse-problems/SP-12/problem.pdf").read_bytes()),
    "tex_sha256": sha(new.encode()),
    "readme_sha256": sha((REPO / "eigenvalues-and-inverse-problems/SP-12/README.md").read_bytes()),
    "rendering_sha256": {x.name: sha(x.read_bytes()) for x in images},
    "visual_findings": "All three freshly rendered pages independently inspected. Text, formulae, links, headers, footers and page numbers are legible and unclipped; no overflow, overlap, black glyphs or missing mathematical signs. Original problem statement remains complete on page two.",
    "passed": all(x["passed"] for x in checks),
}
(OUT / "independent-pdf-and-originals-review.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"passed": result["passed"], "checks": len(checks)}, indent=2))
raise SystemExit(0 if result["passed"] else 1)
