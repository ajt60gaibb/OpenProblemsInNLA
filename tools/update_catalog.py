#!/usr/bin/env python3
"""Regenerate GitHub indexes from canonical problem titles, ratings and status."""

from collections import Counter
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
STATUSES = {
    "Open": "🔵 OPEN",
    "Partially resolved": "🟡 PARTIAL",
    "Solved": "✅ SOLVED",
    "Solution claimed": "🟠 SOLUTION CLAIMED",
    "Needs verification": "⚪ NEEDS VERIFICATION",
}
OPEN = {"Open", "Partially resolved"}
CATEGORIES = [
    "linear-systems-and-elimination", "eigenvalues-and-inverse-problems",
    "matrix-functions-and-stability", "randomized-and-low-rank-approximation",
    "tensor-computations", "nonnegative-and-positive-factorizations",
    "matrix-inequalities-and-norms", "frames-and-matrix-designs",
    "matrix-discrepancy-and-optimization", "arithmetic-and-complexity",
    "intervals-and-absolute-value-equations",
]


def field(text, name):
    match = re.search(r"^\*\*" + name + r":\*\* (.+?)\s*$", text, re.M)
    if not match:
        raise ValueError(f"Missing {name}")
    return match[1]


def read_problem(path):
    text = path.read_text()
    identifier, title = text.splitlines()[0].removeprefix("# ").split(" — ", 1)
    status = field(text, "Status")
    if status not in STATUSES:
        raise ValueError(f"{identifier}: unrecognized status {status!r}")
    return dict(id=identifier, title=title, status=status,
                difficulty=field(text, "Difficulty"), importance=field(text, "Importance"),
                checked=field(text, "Last checked"))


def table(entries, prefix=""):
    lines = ["| ID | Problem | Status | Difficulty | Impact | Read / source |",
             "| --- | --- | --- | --- | --- | --- |"]
    for e in entries:
        path = prefix + e["id"] + "/"
        lines.append(f'| [{e["id"]}]({path}README.md) | {e["title"]} | '
                     f'**{STATUSES[e["status"]]}** | {e["difficulty"]} | '
                     f'{e["importance"]} | [PDF]({path}problem.pdf) · [TeX]({path}problem.tex) |')
    return "\n".join(lines)


def main():
    categories = []
    for slug in CATEGORIES:
        folder = ROOT / slug
        title = (folder / "README.md").read_text().splitlines()[0].removeprefix("# ")
        entries = [read_problem(p) for p in sorted(folder.glob("*/README.md"))]
        categories.append((slug, title, entries))
    counts = Counter(e["status"] for _, _, entries in categories for e in entries)
    total_open = sum(counts[s] for s in OPEN)
    total = sum(counts.values())
    dates = {e["checked"] for _, _, entries in categories for e in entries}
    date_note = (f"Every listed entry was checked on **{next(iter(dates))}**." if len(dates) == 1
                 else "Each entry records its own literature-check date.")
    overview = (f'**{total_open} problems with open targets:** {counts["Open"]} open and '
                f'{counts["Partially resolved"]} partially resolved. '
                f'**{total - total_open} other retained entries**, excluded from the open count.\n\n'
                f'{date_note} Literature checks are bounded; ratings are editorial. '
                '“Impact” uses the canonical `Importance` field.\n\n')
    catalog = ["# All problems and their status\n\n" + overview +
               "[Categories](README.md) · [Status definitions](README.md#problem-status) · "
               "[Solved and claimed solutions](RESOLVED.md) · [Rating definitions](README.md#ratings)\n"]
    category_rows = []
    for slug, title, entries in categories:
        active = [e for e in entries if e["status"] in OPEN]
        other = [e for e in entries if e["status"] not in OPEN]
        summary = f"**{len(active)} problems with open targets.**"
        if other:
            summary += f" {len(other)} retained entries are excluded from the open count."
        body = (f"# {title}\n\n[← All categories](../README.md) · [Full catalog](../CATALOG.md) · "
                f"[Solved and claimed solutions](../RESOLVED.md)\n\n{summary}\n\n" + table(active) + "\n")
        full = f"## [{title}]({slug}/README.md)\n\n" + table(active, slug + "/") + "\n"
        if other:
            body += "\n## Retained entries outside the open count\n\n" + table(other) + "\n"
            full += "\nRetained entries outside the open count:\n\n" + table(other, slug + "/") + "\n"
        body += ("\nRatings are editorial; each entry explains both ratings and the scope of its status evidence. "
                 "[Definitions](../README.md#problem-status).\n")
        (ROOT / slug / "README.md").write_text(body)
        catalog.append(full)
        category_rows.append(f"| [{title}]({slug}/README.md) | {len(active)} |")
    (ROOT / "CATALOG.md").write_text("\n\n".join(catalog))
    readme_path = ROOT / "README.md"
    readme = readme_path.read_text()
    readme = re.sub(r"<!-- catalog-summary -->.*?<!-- /catalog-summary -->",
                    "<!-- catalog-summary -->\n" + overview +
                    f"**[Browse all {total_open} open targets →](CATALOG.md)** · "
                    "**[Solved and claimed solutions →](RESOLVED.md)**\n<!-- /catalog-summary -->",
                    readme, flags=re.S)
    readme = re.sub(r"\| Category \| Problems \|\n\| --- \| ---: \|\n(?:\|.*\n)+",
                    "| Category | Problems |\n| --- | ---: |\n" + "\n".join(category_rows) + "\n", readme)
    readme_path.write_text(readme)
    print(f"Indexed {total} entries: " + ", ".join(f"{k}={v}" for k, v in sorted(counts.items())))


if __name__ == "__main__":
    main()
