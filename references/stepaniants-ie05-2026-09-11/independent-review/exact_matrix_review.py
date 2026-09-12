#!/usr/bin/env python3
"""Independent integer-matrix audit of the frozen IE-05 manuscript.

This verifier parses the printed matrices. It does not import the author's
Gram-Schmidt code, its generated certificates, or the parent's checker.
"""
from argparse import ArgumentParser
from fractions import Fraction
from pathlib import Path
import hashlib
import json
import re


# Final manuscript changes only the original draft's attribution sentence.
EXPECTED_SOURCE_SHA256 = "18d49f30a3ef26f4c88a85c8ea1fc9e5c4e1702b4be6061d39aec892e96a4af7"


def multiply(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def lower_solve(lower, right):
    result = [row[:] for row in right]
    for i in range(len(lower)):
        assert lower[i][i] == 1
        for j in range(len(right[0])):
            result[i][j] -= sum(lower[i][k] * result[k][j] for k in range(i))
    return result


def check_case(h, norms, lower, expected_upper, expected_maxima):
    n = 8
    assert len(h) == n and all(len(row) == n for row in h)
    assert len(norms) == n and all(d > 0 for d in norms)
    gram = multiply([list(col) for col in zip(*h)], h)
    assert gram == [[norms[i] if i == j else 0 for j in range(n)] for i in range(n)]
    upper = lower_solve(lower, h)
    if expected_upper is not None:
        assert upper == expected_upper
    assert all(upper[i][j] == 0 for i in range(n) for j in range(i))
    assert all(upper[i][i] > 0 for i in range(n))
    assert multiply(lower, upper) == h

    active = [[Fraction(x) for x in row] for row in h]
    stages = []
    multipliers = []
    for k in range(n):
        # Positive scaling of each column does not change the pivot comparisons
        # within one column. The first maximizing row must be the diagonal row.
        selected = min(range(k, n), key=lambda i: (-abs(active[i][k]), i))
        assert selected == k
        assert active[k][k] > 0
        # Independently compare every active entry with the block LU expression.
        block = multiply([row[k:] for row in lower[k:]], [row[k:] for row in upper[k:]])
        assert [row[k:] for row in active[k:]] == block
        squares = {(i + 1, j + 1): active[i][j] ** 2 / norms[j]
                   for i in range(k, n) for j in range(k, n)}
        largest = max(squares.values())
        assert largest == expected_maxima[k]
        stages.append({"stage": k + 1, "max_squared": str(largest),
                       "maximizers": [list(loc) for loc, val in squares.items() if val == largest],
                       "active_entries_checked": len(squares), "selected_pivot_row": k + 1})
        for i in range(k + 1, n):
            mult = active[i][k] / active[k][k]
            assert mult == lower[i][k] and abs(mult) <= 1
            multipliers.append({"stage": k + 1, "row": i + 1, "multiplier": str(mult)})
            for j in range(k + 1, n):
                active[i][j] -= mult * active[k][j]
            active[i][k] = Fraction(0)

    return {"orthogonality": "H^T H = D, exact integer equality",
            "positive_diagonal_QR": "H=L T, upper T with positive diagonal",
            "upper": upper, "upper_diagonal": [upper[i][i] for i in range(n)],
            "column_absolute_maxima": [max(abs(h[i][j]) for i in range(n)) for j in range(n)],
            "squared_input_maximum": str(expected_maxima[0]),
            "squared_largest_active_entry": str(max(expected_maxima)),
            "squared_growth": str(max(expected_maxima) / expected_maxima[0]),
            "stages": stages, "multipliers": multipliers}


def main():
    parser = ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    blob = args.source.read_bytes()
    digest = hashlib.sha256(blob).hexdigest()
    assert digest == EXPECTED_SOURCE_SHA256, "This report is bound to the frozen reviewed manuscript."
    text = blob.decode()
    matrices = []
    for body in re.findall(r"\\begin\{pmatrix\}(.*?)\\end\{pmatrix\}", text, re.S):
        matrices.append([[int(x.strip()) for x in row.split("&")]
                         for row in body.strip().split(r"\\")])
    assert len(matrices) == 3
    h, upper, h0 = matrices
    diagonals = [[int(x) for x in group.split(",")]
                 for group in re.findall(r"D(?:_0)?=\\operatorname\{diag\}\(([^)]+)\)", text)]
    assert len(diagonals) == 2
    norms, norms0 = diagonals
    lower0 = [[1 if i == j else -1 if i > j else 0 for j in range(8)] for i in range(8)]
    lower = [row[:] for row in lower0]
    lower[7][1] = 0
    counter_maxima = [Fraction(v * v, 5272) for v in (63, 94, 173, 338, 672, 1342, 2683, 5272)]
    canonical_maxima = [Fraction(2601, 3286)] + [Fraction(v * v, 5462) for v in (96, 176, 344, 684, 1366, 2731, 5462)]
    counter = check_case(h, norms, lower, upper, counter_maxima)
    canonical = check_case(h0, norms0, lower0, None, canonical_maxima)
    assert counter["column_absolute_maxima"] == [1, 3, 13, 189, 581, 1507, 2683, 63]
    assert canonical["column_absolute_maxima"] == [1, 13, 51, 169, 511, 1365, 1, 64]
    assert canonical["upper_diagonal"] == [1, 8, 31, 106, 341, 1024, 1, 5462]
    assert Fraction(counter["squared_growth"]) == Fraction(5272, 63) ** 2
    assert Fraction(canonical["squared_growth"]) == Fraction(17948132, 2601)
    gap = Fraction(counter["squared_growth"]) - Fraction(canonical["squared_growth"])
    assert gap == Fraction(117335164, 1147041) > 0
    report = {"verdict": "PASS: exact counterexample to the full canonical IE-05 equality",
              "source_sha256": digest, "source_bytes": len(blob),
              "arithmetic": "Python integers and fractions.Fraction; no floating-point decisions",
              "method": "Printed-matrix multiplication and independent exact elimination; no imported certificate",
              "counterexample": counter, "canonical": canonical,
              "positive_squared_growth_gap": str(gap)}
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(report["verdict"])
    print("Squared growth gap:", gap)
    print("All 408 active entries and 56 elimination multipliers checked exactly.")
    print("Source SHA-256:", digest)


if __name__ == "__main__":
    main()
