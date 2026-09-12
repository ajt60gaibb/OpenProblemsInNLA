#!/usr/bin/env python3
"""Reproduce RA-19 source, target, formula, review and permanent-ID checks."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
CANONICAL = ROOT / "randomized-and-low-rank-approximation/RA-19"
BASE = "1f22006bdaa4659fcaa0bb775a887685cd3cc566"
EXPECTED_PROOF = "475e29760333fc215e80eed33e4729649383d112d585d7cca88a8b669b618c22"
EXPECTED_CORE = "9b7c3293548e04b0dc474ac6de34499b398e07d2a98500fa2c7ba892c6981cb5"
EXPECTED_REVIEW = "ddb4ecca8fe6b2844a6559dcefe13462291d165c43076d05ce25b47b94de7da4"
EXPECTED_ROOT_REVIEW = "3dcc41bab81d059b851570e8ef86d44faa7f4cdc83376929de6a1a0b17a98095"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def without_layout(text):
    return re.sub(r"(?m)^[ \t]*\\(?:Needspace\{\d+\\baselineskip\}|nopagebreak\[4\])\n\n", "", text)


def core(text, end):
    return text[text.index("## 1. Theorem and notation"):text.index(end)]


def normalized_math(text, latex=False):
    pattern = r"\\\[(.*?)\\\]|\\\((.*?)\\\)" if latex else r"\$\$(.*?)\$\$|\$([^$]+)\$"
    return [re.sub(r"\s+", "", a or b) for a, b in re.findall(pattern, text, re.S)]


def main():
    frozen = (HERE / "reviewed-proof.md").read_bytes()
    assert sha(frozen) == EXPECTED_PROOF
    assert (HERE / "RESULT.md").read_bytes() == frozen
    original = (HERE / "original-target.md").read_bytes()
    assert (HERE / "canonical-target.md").read_bytes() == original
    reviewed = (HERE / "independent-review/review.md").read_bytes()
    assert sha(reviewed) == EXPECTED_REVIEW
    assert sha((HERE / "RA-19-root-math-review.md").read_bytes()) == EXPECTED_ROOT_REVIEW
    manifest = json.loads((HERE / "independent-review/review-manifest.json").read_text())
    for name, record in manifest["artifacts"].items():
        data = (HERE / name).read_bytes()
        assert len(data) == record["bytes"] and sha(data) == record["sha256"], name

    source = (CANONICAL / "solution.md").read_text()
    original_core = core(frozen.decode(), "## 7. Primary source and bounded status check")
    published_core = without_layout(core(source, "## 7. Reference and verification scope"))
    assert original_core == published_core
    assert len(original_core.encode()) == 17059 and sha(original_core.encode()) == EXPECTED_CORE
    tex = (CANONICAL / "solution.tex").read_text()
    tex_core = tex[tex.index(r"\subsection{1. Theorem and notation}"):tex.index(r"\subsection{7. Reference and verification")]
    source_math = normalized_math(original_core)
    tex_math = normalized_math(tex_core, latex=True)
    assert source_math == tex_math, "An ordered core formula changed in conversion."

    current = (CANONICAL / "README.md").read_text()
    original_text = original.decode()
    assert current[current.index("## Statement"):] == original_text[original_text.index("## Statement"):]
    assert current.splitlines()[0] == original_text.splitlines()[0]
    for field in ("Topic", "Difficulty", "Importance", "Rating rationale"):
        pat = rf"^\*\*{field}:\*\*.*$"
        assert re.search(pat, current, re.M)[0] == re.search(pat, original_text, re.M)[0]
    assert "**Status:** Solved" in current
    base_target = subprocess.check_output(["git", "show", BASE + ":randomized-and-low-rank-approximation/RA-19/README.md"], cwd=ROOT)
    assert base_target == original
    base_registry_bytes = subprocess.check_output(["git", "show", BASE + ":problem_ids.json"], cwd=ROOT)
    base_registry = json.loads(base_registry_bytes)
    registry_bytes = (ROOT / "problem_ids.json").read_bytes()
    registry = json.loads(registry_bytes)
    assert len(base_registry) == 217
    assert all(registry.get(k) == v for k, v in base_registry.items())

    for name in ("George Stepaniants", "Department of Computing and Mathematical Sciences", "California Institute of Technology"):
        assert name in source and name in current
    local_links = 0
    for path in [CANONICAL / "README.md", CANONICAL / "solution.md", *HERE.parent.rglob("*.md")]:
        text = path.read_text()
        assert not re.search(r"[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}", text), ("Contact email", path)
        # A byte-identical relocated canonical snapshot retains links relative
        # to its original canonical location, not its archival directory.
        link_base = CANONICAL if path in (HERE / "original-target.md", HERE / "canonical-target.md") else path.parent
        for link in re.findall(r"\]\(([^)]+)\)", text):
            if re.match(r"[a-z]+:", link) or link.startswith("#"):
                continue
            target = link.split("#", 1)[0]
            if target:
                assert (link_base / target).exists(), (path, target)
                local_links += 1
    result = {
        "result": "PASS",
        "checked_utc": datetime.now(timezone.utc).isoformat(),
        "base_commit": BASE,
        "frozen_proof_sha256": EXPECTED_PROOF,
        "independent_review_sha256": EXPECTED_REVIEW,
        "coordinating_review_sha256": EXPECTED_ROOT_REVIEW,
        "independent_review_directory_manifest_preserved": True,
        "mathematical_core_sha256": EXPECTED_CORE,
        "mathematical_core_bytes": 17059,
        "core_unchanged_except_raw_layout": True,
        "ordered_core_math_expressions_identical_in_tex": len(source_math),
        "complete_original_statement_evidence_references_history_unchanged": True,
        "all_217_published_id_mappings_preserved": True,
        "current_registry_entries": len(registry),
        "registry_byte_identical_to_base": registry_bytes == base_registry_bytes,
        "author_and_full_affiliation_present": True,
        "contact_email_in_checked_text": False,
        "valid_local_links": local_links,
        "layout": {
            "needspace_directives": source.count(r"\Needspace"),
            "nopagebreak_directives": source.count(r"\nopagebreak"),
            "plain_page_style": r"\pagestyle{plain}" in source,
        },
    }
    (HERE / "source-checks.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
