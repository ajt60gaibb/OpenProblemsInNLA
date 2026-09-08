#!/usr/bin/env python3
"""Render the canonical per-problem README.md files with Pandoc and XeLaTeX.

Usage: python3 tools/render_problems.py [IE-01 MF-02 ...]
Requires pandoc and xelatex on PATH. Generated TeX files are standalone.
"""

import concurrent.futures
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TEMPLATE = ROOT / "tools/problem-template.tex"


def render(source):
    markdown = source.read_text()
    first, body = markdown.split("\n", 1)
    identifier, title = first.removeprefix("# ").split(" — ", 1)
    category = (source.parent.parent / "README.md").read_text().splitlines()[0][2:]
    # Keep mathematical titles legible in PDF properties as well as on the page.
    pdf_title = title.replace("$", "").replace(r"\times", " × ")
    metadata = {"id": identifier, "title": title, "pdftitle": pdf_title, "category": category}
    for field, key in [("Difficulty", "difficulty"), ("Importance", "importance"), ("Last checked", "checked")]:
        match = re.search(r"^\*\*" + field + r":\*\* (.+?)\s*$", body, re.M)
        if not match:
            raise ValueError(f"{identifier}: missing {field}")
        metadata[key] = match[1]
        body = body[:match.start()] + body[match.end():]
    body = re.sub(r"<!-- navigation -->.*?<!-- /navigation -->", "", body, flags=re.S)
    # GitHub-relative links become usable links in a downloaded PDF or TeX file.
    def absolute_link(match):
        target = match[1]
        if re.match(r"[a-z]+:", target):
            return match[0]
        path, _, fragment = target.partition("#")
        relative = (source.parent / path).resolve().relative_to(ROOT)
        return "](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/" + relative.as_posix() + ("#" + fragment if fragment else "") + ")"
    body = re.sub(r"\]\(([^)]+)\)", absolute_link, body)
    with tempfile.TemporaryDirectory(prefix=f"nla-{identifier}-") as work:
        work = Path(work)
        (work / "metadata.json").write_text(json.dumps(metadata))
        result = subprocess.run(
            [os.environ.get("PANDOC", "pandoc"), "--from=markdown+tex_math_dollars+raw_tex", "--to=latex", "--standalone", "--top-level-division=section", "--template=" + str(TEMPLATE), "--metadata-file=" + str(work / "metadata.json")],
            input=body.strip(), text=True, capture_output=True, check=True,
        )
        tex = result.stdout
        # The code spans in this catalog are literal search phrases. Set them
        # in italics with ordinary spaces so long queries wrap naturally.
        tex = re.sub(r"(\\texttt\{[^{}]*)", lambda m: m[0].replace(r"\texttt", r"\textit").replace(r"\ ", " "), tex)
        tex = tex.replace("₃", r"\textsubscript{3}")
        if identifier == "NM-01":
            # Keep this longer entry's references and status together on page 2.
            # Otherwise just two lines of status evidence spill onto that page.
            tex = tex.replace(r"\subsection{References}", "\\newpage\n" + r"\subsection{References}", 1)
        (source.parent / "problem.tex").write_text(tex)
        (work / "problem.tex").write_text(tex)
        for _ in range(2):
            compiled = subprocess.run(
                [os.environ.get("XELATEX", "xelatex"), "-interaction=nonstopmode", "-halt-on-error", "problem.tex"],
                cwd=work, text=True, capture_output=True,
            )
            if compiled.returncode:
                raise RuntimeError(f"{identifier}: XeLaTeX failed\n{compiled.stdout[-5000:]}")
        log = (work / "problem.log").read_text()
        warnings = re.findall(r"(?:Overfull[^\n]+|Missing character[^\n]+)", log)
        shutil.copyfile(work / "problem.pdf", source.parent / "problem.pdf")
        return identifier, warnings


if __name__ == "__main__":
    requested = set(sys.argv[1:])
    sources = sorted(p for p in ROOT.glob("*/*/README.md") if re.match(r"[A-Z]{2}-\d{2}$", p.parent.name))
    if requested:
        sources = [p for p in sources if p.parent.name in requested]
        missing = requested - {p.parent.name for p in sources}
        if missing:
            raise SystemExit(f"Unknown IDs: {sorted(missing)}")
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        for identifier, warnings in pool.map(render, sources):
            print(identifier + (": " + "; ".join(warnings) if warnings else ": OK"), flush=True)
    print(f"Rendered {len(sources)} problem documents.")
