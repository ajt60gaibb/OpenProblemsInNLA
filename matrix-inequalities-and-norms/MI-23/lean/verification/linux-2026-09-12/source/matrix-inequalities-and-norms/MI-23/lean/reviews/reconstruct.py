#!/usr/bin/env python3
"""Supplementary exact arithmetic for MI-23; this is not a Lean proof."""
from fractions import Fraction as Q
import json
from pathlib import Path


def matrix(rows):
    return [[Q(x) for x in row] for row in rows]


def mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(3))
             for j in range(3)] for i in range(3)]


def transpose(a):
    return [list(row) for row in zip(*a)]


def subtract(a, b):
    return [[a[i][j] - b[i][j] for j in range(3)] for i in range(3)]


def diagonal(v):
    return [[Q(v[i]) if i == j else Q(0) for j in range(3)] for i in range(3)]


def power(a, k):
    result = diagonal([1, 1, 1])
    while k:
        if k % 2:
            result = mul(result, a)
        a = mul(a, a)
        k //= 2
    return result


def readable(a):
    return [[str(x) for x in row] for row in a]


d = diagonal([16, Q(1, 12), 1])
di = diagonal([Q(1, 16), 12, 1])
t = matrix([[2, 1, 2], [1, 25, -10], [2, -10, 10]])
l = matrix([[1, 0, 0], [Q(1, 2), 1, 0], [1, Q(-22, 49), 1]])
p = diagonal([2, Q(49, 2), Q(150, 49)])
assert mul(mul(l, p), transpose(l)) == t
assert all(p[i][i] > 0 for i in range(3))
assert mul(d, di) == mul(di, d) == diagonal([1, 1, 1])
a = power(d, 2)
b = mul(mul(d, power(t, 8)), d)
g = mul(mul(d, t), d)
h = mul(mul(d, power(t, 7)), d)
assert mul(mul(di, b), di) == power(t, 8)
gh = mul(g, h)
ab = mul(a, b)
entry = gh[0][2]
frob = sum(x * x for row in ab for x in row)
gap = entry * entry - frob
assert entry == Q(1260589125202, 9)
assert frob == Q(2009446159144992718181231562721, 107495424)
assert gap == Q(99434824489435745411095588895, 107495424)
assert gap > 0
assert Q(1, 8) >= 0 and Q(1, 8) <= 1
assert 2 >= 1 and 1 >= 1 and 1 >= 1
report = {
    "status": "PASS: exact rational arithmetic only",
    "scope": "No CFC, matrix norm, eigenvalue, positive-definiteness or Lean proof is inferred.",
    "source": "Colbrook MI-23 source formulas, reconstructed with Python Fraction arithmetic.",
    "parameters": {"n": 3, "r": "1", "s": "1", "p": "2", "t": "1/8"},
    "exact_LDL_identity": True,
    "strictly_positive_diagonal_pivots": [str(p[i][i]) for i in range(3)],
    "diagonal_inverse_identities": True,
    "normalized_B_equals_T8": True,
    "T2": readable(power(t, 2)),
    "T4": readable(power(t, 4)),
    "T7": readable(power(t, 7)),
    "T8": readable(power(t, 8)),
    "A": readable(a), "B": readable(b), "G": readable(g), "H": readable(h),
    "GH_entry_0_2": str(entry),
    "frobenius_squared_AB": str(frob),
    "squared_gap": str(gap),
    "positive_gap": True,
}
Path(__file__).with_name("numerical-precheck.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({k: report[k] for k in ["status", "GH_entry_0_2", "frobenius_squared_AB", "squared_gap"]}, indent=2))
