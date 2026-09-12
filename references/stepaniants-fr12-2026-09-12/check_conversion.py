#!/usr/bin/env python3
"""Check the preserved FR-12 source and ordered Markdown math conversion.

This is a source-transcription check, not a mathematical proof verifier.
All input paths are explicit so the checker remains portable after archiving.
"""
from argparse import ArgumentParser
from hashlib import sha256
from pathlib import Path
import json
import re


def fingerprint(data):
    return {"bytes": len(data), "sha256": sha256(data).hexdigest()}


def normalize_math(formula):
    formula = formula.replace(r"\HH", r"\mathcal H")
    formula = re.sub(r"\\(?:label|tag)\{[^{}]*\}", "", formula)
    return re.sub(r"\s+", "", formula)


def formulas(text, kind):
    if kind == "tex":
        pattern = r"\\\[(.*?)\\\]|\\begin\{equation\}(.*?)\\end\{equation\}|(?<!\\)\$(.*?)(?<!\\)\$"
    else:
        pattern = r"\$\$(.*?)\$\$|(?<!\\)\$(.*?)(?<!\\)\$"
    return [normalize_math(next(x for x in m.groups() if x is not None))
            for m in re.finditer(pattern, text, re.DOTALL)]


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--original", required=True, type=Path)
    parser.add_argument("--tex", required=True, type=Path)
    parser.add_argument("--markdown", required=True, type=Path)
    args = parser.parse_args()
    original = args.original.read_text()
    tex = args.tex.read_text()
    md = args.markdown.read_text()
    assert sha256(original.encode()).hexdigest() == "efbcaeb82adc140be98cdffca39bf9d9a34d3b281951f42c9d7f7232279335ba"
    start = r"\section{Exact target}"
    blocks = {}
    for name, end in [("mathematical_core", r"\section{Checks, attribution, and scope}"),
                      ("whole_retained_body", r"\end{document}")]:
        a = original[original.index(start):original.index(end)]
        b = tex[tex.index(start):tex.index(end)]
        assert a == b
        blocks[name] = {**fingerprint(a.encode()), "byte_identical": True}
    tex_body = tex[tex.index(r"\begin{abstract}"):tex.index(r"\begin{thebibliography}")]
    md_body = md[:md.index("## References")]
    tex_math, md_math = formulas(tex_body, "tex"), formulas(md_body, "md")
    assert tex_math == md_math
    assert len(tex_math) == 66
    for row in [(1, 2, 8, 4, 2), (2, 8, 1536, 192, 8)]:
        assert " & ".join(map(str, row)) in tex
        assert "| " + " | ".join(map(str, row)) + " |" in md
    for source in [tex, md]:
        assert not re.search(r"[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}", source)
        assert "George Stepaniants" in source
        assert "Department of Computing and Mathematical Sciences" in source
        assert "California Institute of Technology" in source
        assert "stepaniants-fr12-2026-09-12/REVIEW.md" in source
    result = {
        "verdict": "PASS: source preservation and formula conversion",
        "scope": "Transcription, byline, and metadata checks only; independent mathematical review is separate.",
        "inputs": {"original": fingerprint(original.encode()),
                   "solution.tex": fingerprint(tex.encode()),
                   "solution.md": fingerprint(md.encode())},
        **blocks,
        "ordered_formulas_including_abstract_and_scope_excluding_bibliography": 66,
        "ordered_formulas_match_after_declared_normalization": True,
        "normalization": ["Whitespace", "Expand \\HH to \\mathcal H", "Remove equation labels or tags"],
        "finite_case_table_rows_match": 2,
        "full_author_affiliation_present": True,
        "contact_email_matches": 0,
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
