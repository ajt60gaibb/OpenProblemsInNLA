#!/usr/bin/env python3
"""Portable MF-06 source-preservation and math-transcription checks.

Checks exact source fingerprints, byte-preservation of Sections 1--6, and
every ordered inline/display formula in the generated standalone LaTeX.
This checker is not a formal verification of the mathematical argument.
"""
from argparse import ArgumentParser
from hashlib import sha256
from pathlib import Path
import json
import re

ORIGINAL_SHA = "11fce1e0012b8e514890fa6a116b8d91b91f56f5b7cd0ae20199006b4a18ca94"
REVIEW_SHA = "6c15e3d3a20669ede243d7e56d1229f148e39a138e7c0d1628c5768cf6166d36"
START = "## 1. The exact target"
END = "## 7. Scope of verification and attribution"


def fingerprint(data):
    return {"bytes": len(data), "sha256": sha256(data).hexdigest()}


def md_math(text):
    pattern = r"\$\$(.*?)\$\$|(?<!\\)\$(.*?)(?<!\\)\$"
    return [re.sub(r"\s+", "", next(x for x in m.groups() if x is not None))
            for m in re.finditer(pattern, text, re.DOTALL)]


def tex_math(text):
    pattern = r"\\\[(.*?)\\\]|\\\((.*?)\\\)"
    return [re.sub(r"\s+", "", next(x for x in m.groups() if x is not None))
            for m in re.finditer(pattern, text, re.DOTALL)]


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--original", required=True, type=Path)
    parser.add_argument("--markdown", required=True, type=Path)
    parser.add_argument("--tex", required=True, type=Path)
    parser.add_argument("--review", type=Path)
    args = parser.parse_args()
    original = args.original.read_text()
    md = args.markdown.read_text()
    tex = args.tex.read_text()
    assert sha256(original.encode()).hexdigest() == ORIGINAL_SHA
    original_core = original[original.index(START):original.index(END)]
    md_core = md[md.index(START):md.index(END)]
    assert original_core == md_core
    core_formulas = md_math(original_core)
    public_formulas = md_math(md)
    rendered_formulas = tex_math(tex[tex.index(r"\maketitle"):tex.index(r"\end{document}")])
    assert public_formulas == rendered_formulas
    assert core_formulas == public_formulas
    for source in [md, tex]:
        for required in ["George Stepaniants", "Department of Computing and Mathematical Sciences",
                         "California Institute of Technology", "Pasadena, California, USA",
                         "stepaniants-mf06-2026-09-12/REVIEW.md"]:
            assert required in source
        assert not re.search(r"[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}", source)
        assert "/tmp/" not in source
    assert r"Let $n\ge1$ and $K,F\ge0$." in md_core
    result = {
        "verdict": "PASS: source preservation and full ordered formula conversion",
        "scope": "Transcription checks only; no universal proof or PDF visual check is claimed.",
        "inputs": {"reviewed-proof-clarified.md": fingerprint(original.encode()),
                   "solution.md": fingerprint(md.encode()), "solution.tex": fingerprint(tex.encode())},
        "mathematical_core": {"start_literal": START, "end_exclusive_literal": END,
                              **fingerprint(original_core.encode()), "byte_identical": True},
        "ordered_core_formulas": len(core_formulas),
        "ordered_whole_public_manuscript_formulas": len(public_formulas),
        "ordered_tex_formulas": len(rendered_formulas),
        "all_ordered_formulas_match": True,
        "formula_normalization": "Whitespace only; dollar delimiters are converted to LaTeX parentheses/brackets. All tags and mathematical tokens remain unchanged.",
        "clarified_nonnegative_parameters_preserved": True,
        "full_author_affiliation_present": True,
        "contact_email_matches_in_public_sources": 0,
        "scratch_path_matches_in_public_sources": 0,
    }
    if args.review is not None:
        review = args.review.read_bytes()
        assert sha256(review).hexdigest() == REVIEW_SHA
        result["independent_review"] = fingerprint(review)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
