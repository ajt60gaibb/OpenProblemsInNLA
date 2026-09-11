#!/usr/bin/env python3
"""Render tables for the declared certificate scope; this does not certify new claims."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
claims = json.loads((ROOT / "claims.json").read_text())
orders = claims["ac11_verified_orders"]
ranges = claims["ac12_verified_orders"]
assert orders == list(range(1, max(orders) + 1))
assert ranges == list(range(1, max(ranges) + 1))
(ROOT / "results_generated.tex").write_text(
    r"\newcommand{\MaxMinOrder}{" + str(max(orders)) + "}\n"
    + r"\newcommand{\MaxRangeOrder}{" + str(max(ranges)) + "}\n"
    + r"\newcommand{\NewWitnessCount}{" + str(max(orders) - 20) + "}\n"
)
minimum = []
for n in orders:
    if n < 21:
        continue
    g = n - ((n + 1).bit_length() - 1)
    minimum.append(f"{n} & {g} & {1 << g:,} & exact full-matrix check passed " + r"\\")
range_rows = []
for n in ranges:
    values = set(map(int, (ROOT / f"data/ac12/u{n}_spectrum.txt").read_text().split()))
    method = "exhaustive representatives" if n <= 8 else "witnesses + bounded exhaustive check"
    range_rows.append(f"{n} & {len(values):,} & {2*len(values) - (0 in values):,} & {method} " + r"\\")
for stem, header, rows in [
    ("minimum", r"Order $n$ & Exponent $g(n)$ & Attained permanent & Certificate status\\", minimum),
    ("range", r"Order & Absolute values & Signed values & Completeness certificate\\", range_rows),
]:
    (ROOT / f"{stem}_table.tex").write_text("\n".join(rows) + "\n")
    (ROOT / f"{stem}_tabular.tex").write_text(
        "\\begin{tabular}{rrrl}\n\\toprule\n" + header + "\n\\midrule\n"
        + "\n".join(rows) + "\n\\bottomrule\n\\end{tabular}\n"
    )
print("Rendered declared-scope tables; run pdflatex twice to build the note.")
