#!/usr/bin/env python3
"""Render per-problem solution.md manuscripts with Pandoc and XeLaTeX.

Usage: python3 tools/render_solutions.py [IS-02 KE-03 ...]
Author, affiliation, date and review metadata are maintained in solution.md.
"""

import concurrent.futures
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TEMPLATE = ROOT / "tools/solution-template.tex"


def render(source):
    identifier = source.parent.name
    markdown = source.read_text(encoding="utf-8")
    if re.search(r'^proof-source:', markdown, re.M):
        from render_latex_solutions import render as render_latex
        return render_latex(source)

    def absolute_link(match):
        target = match[1]
        if re.match(r"[a-z]+:", target) or target.startswith("#"):
            return match[0]
        path, _, fragment = target.partition("#")
        relative = (source.parent / path).resolve().relative_to(ROOT)
        return "](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/" + relative.as_posix() + ("#" + fragment if fragment else "") + ")"

    markdown = re.sub(r"\]\(([^)]+)\)", absolute_link, markdown)
    with tempfile.TemporaryDirectory(prefix=f"nla-solution-{identifier}-") as work:
        work = Path(work)
        result = subprocess.run(
            [os.environ.get("PANDOC", "pandoc"), "--from=markdown+tex_math_dollars+tex_math_single_backslash+raw_tex",
             "--to=latex", "--standalone", "--top-level-division=section",
             "--template=" + str(TEMPLATE), "--metadata=id:" + identifier],
            input=markdown, text=True, encoding="utf-8", capture_output=True, check=True,
        )
        tex = result.stdout
        (source.parent / "solution.tex").write_text(tex, encoding="utf-8")
        (work / "solution.tex").write_text(tex, encoding="utf-8")
        for _ in range(2):
            compiled = subprocess.run(
                [os.environ.get("XELATEX", "xelatex"), "-interaction=nonstopmode",
                 "-halt-on-error", "solution.tex"],
                cwd=work, text=True, encoding="utf-8", errors="replace", capture_output=True,
            )
            if compiled.returncode:
                raise RuntimeError(f"{identifier}: XeLaTeX failed\n{compiled.stdout[-5000:]}\n{compiled.stderr[-2000:]}")
        log = (work / "solution.log").read_text(encoding="utf-8", errors="replace")
        warnings = re.findall(r"(?:Overfull[^\n]+|Missing character[^\n]+)", log)
        shutil.copyfile(work / "solution.pdf", source.parent / "solution.pdf")
        return identifier, warnings


if __name__ == "__main__":
    requested = set(sys.argv[1:])
    sources = sorted(p for p in ROOT.glob("*/*/solution.md") if re.fullmatch(r"[A-Z]{2}-\d{2}", p.parent.name))
    if requested:
        sources = [p for p in sources if p.parent.name in requested]
        missing = requested - {p.parent.name for p in sources}
        if missing:
            raise SystemExit(f"Unknown solution IDs: {sorted(missing)}")
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        for identifier, warnings in pool.map(render, sources):
            print(identifier + " solution: " + ("; ".join(warnings) if warnings else "OK"), flush=True)
    print(f"Rendered {len(sources)} solution manuscripts.")
