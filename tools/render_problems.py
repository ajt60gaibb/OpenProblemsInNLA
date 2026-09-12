#!/usr/bin/env python3
"""Render the canonical per-problem README.md files with Pandoc and XeLaTeX.

Usage: python3 tools/render_problems.py [IE-02 MF-02 ...]
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
    for field, key in [("Difficulty", "difficulty"), ("Importance", "importance"), ("Status", "status"), ("Last checked", "checked")]:
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
        # Keep references with the dated evidence in entries that otherwise
        # leave only a few lines on a second page after the status audit.
        if identifier in {
            'AA-01', 'AC-13', 'AV-01', 'AV-02', 'AV-03', 'FR-01', 'FR-02', 'FR-04',
            'FR-10', 'FR-11', 'IE-03', 'IE-04', 'IE-06', 'IE-08', 'IE-10', 'IE-11', 'IE-13',
            'IE-14', 'IE-15', 'IE-17', 'IE-18', 'IE-19', 'IE-21', 'IE-22', 'IE-23',
            'IE-24', 'IE-25', 'IS-02', 'IS-03', 'IS-05', 'IV-02', 'IV-03', 'IV-04',
            'IV-05', 'IV-06', 'KE-03', 'KE-04', 'KE-05', 'MD-06', 'MF-14', 'MF-15',
            'MF-16', 'MF-17', 'MF-21', 'MI-03', 'MI-04', 'MI-06', 'MI-07', 'MI-08',
            'MI-09', 'MI-19', 'MI-23', 'MI-29', 'NM-01', 'NM-03', 'PF-05', 'RA-02',
            'RA-04', 'RA-06', 'RA-08', 'RA-09', 'RA-10', 'RA-11', 'RA-12', 'RA-14',
            'RA-15', 'RA-17', 'RE-01', 'RE-02', 'RE-03', 'RE-06', 'SP-04', 'SP-05',
            'SP-06', 'SP-07', 'SP-09', 'SP-12', 'TR-11', 'TR-20', 'TR-21', 'TR-24',
            'TR-26', 'TR-30',
        }:
            tex = re.sub(r"\\subsection\{References?(?:\s+and\s+status\s+check)?\}",
                         lambda m: "\\newpage\n" + m[0], tex, count=1)
        if identifier == "SF-01":
            tex = tex.replace(r"\subsection{References and status}", "\\newpage\n" + r"\subsection{References and status}", 1)
        if identifier == "IE-20":
            tex = tex.replace(r"Define \(P_{\rm CG}", "\\newpage\n" + r"Define \(P_{\rm CG}", 1)
        if identifier == "RE-05":
            # The resolution notice makes the quantified question cross a page.
            tex = re.sub(r"\\(?:sub)*section\{Question\}", lambda m: "\\newpage\n" + m[0], tex, count=1)
        if identifier == "PF-05":
            # Keep the two equivalent conditions together after the new notice.
            tex = re.sub(r"\\(?:sub)*section\{Question\}", lambda m: "\\newpage\n" + m[0], tex, count=1)
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
