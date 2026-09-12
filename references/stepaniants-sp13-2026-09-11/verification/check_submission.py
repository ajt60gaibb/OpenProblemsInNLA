#!/usr/bin/env python3
"""Check SP-13 source preservation and packaging, not the mathematical theorem."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
CAN = ROOT / "eigenvalues-and-inverse-problems/SP-13"
FROZEN = "dc5a7118b33fa84221d1b051997642180ca9c45e1605ebcad7b15a0d0642c7dc"
CORE = "c89b2767c14af0419d403d8706bd446bad72ea4b76c28704b7290f67547d8dc0"
REVIEWS = {
    "SP-13-independent-review.md": "f6e75de15aaccb63db10c8e9b16857a3a9aad40d5111eb60de4aa9b160dd08f7",
    "SP-13-root-math-review.md": "83083dcb832083331f51324e3a954deb1ee942b4a064db3d278eddb81f832cde",
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def core(text):
    return "## 1. Exact target" + text.split("## 1. Exact target", 1)[1].split("## 6.", 1)[0]


def normalized_formula(text):
    return re.sub(r"\s+", "", text)


def markdown_math(text):
    pattern = re.compile(r"\$\$(.*?)\$\$|(?<!\\)\$(?!\$)(.*?)(?<!\\)\$", re.S)
    return [normalized_formula(m[1] if m[1] is not None else m[2]) for m in pattern.finditer(text)]


def tex_math(text):
    pattern = re.compile(r"\\\[(.*?)\\\]|\\\((.*?)\\\)", re.S)
    return [normalized_formula(m[1] if m[1] is not None else m[2]) for m in pattern.finditer(text)]


def main():
    reviewed = (HERE / "reviewed-proof.md").read_bytes()
    assert sha(reviewed) == FROZEN
    for name, expected in REVIEWS.items():
        assert sha((HERE / name).read_bytes()) == expected, name
    manuscript = (CAN / "solution.md").read_text()
    assert core(manuscript) == core(reviewed.decode())
    assert sha(core(manuscript).encode()) == CORE
    assert len(core(manuscript).encode()) == 7494
    original_scope = reviewed.decode().split("## 6. Scope, provenance, and bounded source check\n\n", 1)[1].split("\n\n", 1)[0]
    assert original_scope in manuscript
    assert manuscript.split("## References\n", 1)[1] == reviewed.decode().split("## References\n", 1)[1]
    md_math = markdown_math(manuscript)
    core_math = markdown_math(core(manuscript))
    assert len(core_math) == 121
    tx_math = tex_math((CAN / "solution.tex").read_text())
    assert md_math == tx_math, (len(md_math), len(tx_math), next(((i, x, y) for i, (x, y) in enumerate(zip(md_math, tx_math)) if x != y), None))
    original = (HERE / "original-target.md").read_text()
    canonical = (CAN / "README.md").read_text()
    assert canonical.split("## Statement\n", 1)[1] == original.split("## Statement\n", 1)[1]
    assert "**Status:** Solved" in canonical
    assert not re.search(r"^\\(?:newpage|Needspace|pagestyle)", canonical, re.M)
    assert "author: George Stepaniants" in manuscript
    assert "Department of Computing and Mathematical Sciences, California Institute of Technology" in manuscript
    assert "email:" not in manuscript
    assert "Independent Codex" in (HERE / "SP-13-independent-review.md").read_text() or "independent Codex" in (HERE / "SP-13-independent-review.md").read_text()
    scanned = []
    email = re.compile(r"[A-Za-z0-9_.+%-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}")
    for path in list(CAN.glob("*.md")) + list(CAN.glob("*.tex")) + list(HERE.parent.rglob("*.md")) + list(HERE.glob("*.json")):
        assert not email.search(path.read_text()), path
        scanned.append(path.relative_to(ROOT).as_posix())
    pages = {}
    for name in ("solution", "problem"):
        pdf = CAN / (name + ".pdf")
        text = subprocess.check_output(["pdftotext", str(pdf), "-"], text=True)
        normalized_text = re.sub(r"\s+", " ", text)
        assert "George Stepaniants" in normalized_text
        assert "Computing and Mathematical Sciences" in normalized_text
        assert "California Institute of Technology" in normalized_text
        assert not email.search(text)
        info = subprocess.check_output(["pdfinfo", str(pdf)], text=True)
        pages[name] = int(re.search(r"^Pages:\s+(\d+)", info, re.M)[1])
    manifest = HERE / "document-checks.json"
    verified_hashes = 0
    if manifest.exists():
        for name, item in json.loads(manifest.read_text()).get("artifacts", {}).items():
            data = (ROOT / name).read_bytes()
            assert sha(data) == item["sha256"], name
            assert len(data) == item["bytes"], name
            verified_hashes += 1
    result = {
        "verdict": "PASS",
        "scope": "Publication source, target, formula, metadata and artifact preservation; not independent mathematical verification",
        "frozen_source_sha256": FROZEN,
        "math_core_bytes": 7494,
        "math_core_sha256": CORE,
        "original_scope_and_references_preserved": True,
        "mathematical_core_expression_count": len(core_math),
        "whole_manuscript_ordered_math_expressions_matching_tex": len(md_math),
        "original_target_and_history_preserved": True,
        "signed_reviews_unchanged": True,
        "contact_email_found": False,
        "text_files_scanned": len(scanned),
        "pdf_page_counts": pages,
        "manifest_hashes_verified": verified_hashes,
        "visual_qa": "Separate manual all-page review is recorded in document-checks.json; text extraction is not visual inspection",
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
