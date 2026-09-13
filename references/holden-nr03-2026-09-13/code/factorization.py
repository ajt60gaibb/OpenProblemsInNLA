#!/usr/bin/env python3
"""Explicit nonnegative factorization of C_n(a,b) = (1-|a & b|)^2.

All stored numbers are integers. The actual right factor is
H[k][b] = H_scaled[k][b] / denominators[b].

For every n >= 1, the construction has
    r(n) = 2**(n-1) + n + comb(n, 2) + comb(n, 4)
terms (comb(n,k)=0 for k>n). In particular r(7)=127<128.

Only the Python standard library is required.
"""
from __future__ import annotations

import argparse
import csv
from fractions import Fraction
from itertools import combinations
import json
from math import comb
from pathlib import Path
from typing import Any


def rank_bound(n: int) -> int:
    if type(n) is not int or n < 1:
        raise ValueError("n must be a positive integer")
    return (1 << (n - 1)) + n + comb(n, 2) + (comb(n, 4) if n >= 4 else 0)


def build_certificate(n: int) -> dict[str, Any]:
    """Return integer matrices W, H_scaled, and positive column denominators.

    Rows/columns use increasing integer subset masks; bit i denotes i+1.
    Memory is exponential in n; n=7 is the intended counterexample size.
    """
    r = rank_bound(n)
    size = 1 << n
    full = size - 1
    weights = [b.bit_count() for b in range(size)]
    denominators = [max(1, (p - 1) ** 2) for p in weights]
    left_columns: list[list[int]] = []
    right_rows: list[list[int]] = []
    labels: list[dict[str, Any]] = []

    # One atom for each unordered complementary pair {s, full^s}.
    # Representatives omit coordinate n, so their masks are 0,...,2**(n-1)-1.
    for s in range(size // 2):
        sc = full ^ s
        left_columns.append([int(a == s or a == sc) for a in range(size)])
        right_rows.append([
            (1 - (s & b).bit_count()) ** 2 *
            (1 - (sc & b).bit_count()) ** 2
            for b in range(size)
        ])
        labels.append({"family": "complement_pair", "mask": s,
                       "complement_mask": sc})

    # Singleton-column correction, required because (|b|-1)**2=0 there.
    for i in range(n):
        s = 1 << i
        left_columns.append([int(a & s == 0) for a in range(size)])
        right_rows.append([int(b == s) for b in range(size)])
        labels.append({"family": "singleton", "mask": s})

    for coordinates in combinations(range(n), 2):
        s = sum(1 << i for i in coordinates)
        left_columns.append([int(a & s == s) for a in range(size)])
        right_rows.append([
            4 * (weights[b] - 2) if b & s == s else 0
            for b in range(size)
        ])
        labels.append({"family": "pair", "mask": s})

    for coordinates in combinations(range(n), 4):
        s = sum(1 << i for i in coordinates)
        left_columns.append([max(0, (a & s).bit_count() - 2)
                             for a in range(size)])
        right_rows.append([12 if b & s == s else 0 for b in range(size)])
        labels.append({"family": "four_set", "mask": s})

    if len(left_columns) != r or len(right_rows) != r:
        raise RuntimeError("Internal atom-count error")
    W = [[left_columns[k][a] for k in range(r)] for a in range(size)]
    return {
        "schema": "NR03-integer-column-scaled-NMF-v1",
        "n": n,
        "r": r,
        "indexing": "Increasing integer masks; bit i denotes element i+1.",
        "identity": "W @ H_scaled = C_n @ diag(denominators); H = H_scaled @ diag(1/denominators)",
        "W": W,
        "H_scaled": right_rows,
        "denominators": denominators,
        "atoms": labels,
    }


def write_certificate(certificate: dict[str, Any], out: Path) -> None:
    out.mkdir(parents=True, exist_ok=True)
    n = certificate["n"]
    (out / f"factors_n{n}.json").write_text(
        json.dumps(certificate, indent=1) + "\n", encoding="utf-8")

    def csv_file(name: str, rows: Any) -> None:
        with (out / name).open("w", newline="", encoding="utf-8") as stream:
            csv.writer(stream, lineterminator="\n").writerows(rows)

    csv_file(f"W_n{n}.csv", certificate["W"])
    csv_file(f"H_scaled_n{n}.csv", certificate["H_scaled"])
    d = certificate["denominators"]
    csv_file(f"H_n{n}_rational.csv", [
        [str(Fraction(x, denominator)) for x, denominator in zip(row, d)]
        for row in certificate["H_scaled"]
    ])
    csv_file(f"column_denominators_n{n}.csv", [d])
    csv_file(f"atom_index_n{n}.csv", [
        ["zero_based_atom_index", "family", "mask", "complement_mask"],
        *[[k, atom["family"], atom["mask"], atom.get("complement_mask", "")]
          for k, atom in enumerate(certificate["atoms"])],
    ])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int, default=7)
    parser.add_argument("--out", type=Path, default=Path("data"))
    parser.add_argument("--allow-large", action="store_true",
                        help="allow n>10 (exponential memory/time)")
    args = parser.parse_args()
    if args.n > 10 and not args.allow_large:
        parser.error("n>10 requires --allow-large because the factors are exponentially large")
    certificate = build_certificate(args.n)
    write_certificate(certificate, args.out)
    print(f"W: {1 << args.n} x {certificate['r']}; "
          f"H: {certificate['r']} x {1 << args.n}")
    print(f"Certificate written to {args.out}")


if __name__ == "__main__":
    main()
