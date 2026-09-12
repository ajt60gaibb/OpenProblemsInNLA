#!/usr/bin/env python3
"""Exact finite checks of exterior/block transcription; not a JSR proof.

Uses only the Python standard library and full minors of independently
constructed integer matrices. It does not import the author's checker.
Run from any directory; JSON evidence is written beside this script.
"""
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EXPECTED = "2471cce689608c9ff0dfe15e4ed0230f00ba6799c4df1129e593f08e50593f2d"
source = (ROOT / "reviewed-proof.md").read_bytes()
assert sha256(source).hexdigest() == EXPECTED


def det(a):
    n = len(a)
    if n == 0:
        return 1
    b = [[Fraction(x) for x in row] for row in a]
    ans = Fraction(1)
    for j in range(n):
        pivot = next((i for i in range(j, n) if b[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            b[j], b[pivot] = b[pivot], b[j]
            ans = -ans
        p = b[j][j]
        ans *= p
        for i in range(j + 1, n):
            q = b[i][j] / p
            for k in range(j + 1, n):
                b[i][k] -= q * b[j][k]
            b[i][j] = 0
    assert ans.denominator == 1
    return ans.numerator


def mul(a, b):
    return [[sum(x*y for x, y in zip(row, col))
             for col in zip(*b)] for row in a]


def wedge(a, j):
    basis = list(combinations(range(len(a)), j))
    return [[det([[a[r][c] for c in cols] for r in rows])
             for cols in basis] for rows in basis]


def kron(a, b):
    return [[x*y for x in ar for y in br] for ar in a for br in b]


profiles = [(1,), (1, 1), (1, 2), (2, 1), (2, 2), (1, 2, 1),
            (2, 1, 2), (1, 2, 2, 1)]
counts = Counter()
for dims in profiles:
    block = [i for i, d in enumerate(dims) for _ in range(d)]
    n = len(block)
    matrices = []
    for seed in (1, 3):
        a = [[0 if block[r] > block[c] else
              ((seed + 3*r + 5*c + r*c) % 11 - 5)
              for c in range(n)] for r in range(n)]
        matrices.append(a)
    a, b = matrices
    ab = mul(a, b)
    for j in range(n + 1):
        basis = list(combinations(range(n), j))
        allocations = [tuple(sum(block[t] == i for t in q)
                             for i in range(len(dims))) for q in basis]
        wa, wb, wab = wedge(a, j), wedge(b, j), wedge(ab, j)
        assert mul(wa, wb) == wab
        counts["exterior_product_identities"] += 1
        for matrix, wm in ((a, wa), (b, wb), (ab, wab)):
            for r, ar in enumerate(allocations):
                for c, ac in enumerate(allocations):
                    # Each strict upper-block move decreases total block index.
                    if ar != ac and sum(i*x for i, x in enumerate(ar)) >= sum(i*x for i, x in enumerate(ac)):
                        assert wm[r][c] == 0
                        counts["forced_zero_minors"] += 1
            for allocation in sorted(set(allocations)):
                ids = [t for t, z in enumerate(allocations) if z == allocation]
                actual = [[wm[r][c] for c in ids] for r in ids]
                expected = [[1]]
                offset = 0
                for size, degree in zip(dims, allocation):
                    diagonal = [row[offset:offset + size]
                                for row in matrix[offset:offset + size]]
                    expected = kron(expected, wedge(diagonal, degree))
                    offset += size
                assert actual == expected
                counts["diagonal_allocation_tensor_blocks"] += 1
        choices = sorted(set(allocations))
        for p, q in combinations(choices, 2):
            c = tuple(max(x, y) for x, y in zip(p, q))
            e = tuple(min(x, y) for x, y in zip(p, q))
            assert sum(c) > j and sum(c) <= n
            assert Counter((i, z) for i, pair in enumerate(zip(p, q)) for z in pair) == Counter((i, z) for i, pair in enumerate(zip(c, e)) for z in pair)
            counts["max_min_factor_reorderings"] += 1

result = {
    "verdict": "PASS",
    "scope": "Finite exact exterior-algebra transcription checks only; universal analytic JSR and perturbation claims are established by the separate written review.",
    "arithmetic": "Integers and fractions only; no floating point; no author checker imported.",
    "reviewed_source": {"path": "reviewed-proof.md", "bytes": len(source), "sha256": EXPECTED},
    "block_profiles": [list(x) for x in profiles],
    "counts": dict(sorted(counts.items())),
}
(ROOT / "independent-exterior-check.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
