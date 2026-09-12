#!/usr/bin/env python3
"""Exact finite witness arithmetic, not a Lean proof or a universal unitary check."""
from fractions import Fraction as F
import json


def add(a, b):
    return [[a[i][j] + b[i][j] for j in range(3)] for i in range(3)]


def scale(c, a):
    return [[c * x for x in row] for row in a]


def transpose(a):
    return [list(row) for row in zip(*a)]


def mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(3))
             for j in range(3)] for i in range(3)]


def outer(w):
    return [[x * y for y in w] for x in w]


def diag(a, b, c):
    return [[a, 0, 0], [0, b, 0], [0, 0, c]]


def main():
    a = [[1, F(3, 4), 0], [0, 0, 0], [0, 0, 0]]
    b = [[-1, 0, 0], [0, 0, 0], [-F(3, 4), 0, 0]]
    c = add(a, b)
    ra = [[F(4, 5), F(3, 5), 0], [F(3, 5), F(9, 20), 0], [0, 0, 0]]
    axis = diag(F(5, 4), 0, 0)
    lb = [[F(4, 5), 0, F(3, 5)], [0, 0, 0], [F(3, 5), 0, F(9, 20)]]
    rc = diag(F(3, 4), F(3, 4), 0)
    lc = diag(F(3, 4), 0, F(3, 4))
    squares = [(a, ra), (transpose(a), axis), (b, axis),
               (transpose(b), lb), (c, rc), (transpose(c), lc)]
    for x, h in squares:
        assert transpose(h) == h
        assert mul(h, h) == mul(transpose(x), x)
    assert ra == scale(F(1, 20), outer([4, 3, 0]))
    assert lb == scale(F(1, 20), outer([4, 0, 3]))
    assert axis == scale(F(5, 4), outer([1, 0, 0]))
    assert all(x >= 0 for x in [F(1, 20), F(5, 4), F(3, 4)])
    ha = [[F(41, 40), F(3, 10), 0], [F(3, 10), F(9, 40), 0], [0, 0, 0]]
    hb = [[F(41, 40), 0, F(3, 10)], [0, 0, 0], [F(3, 10), 0, F(9, 40)]]
    hc = diag(F(3, 4), F(3, 8), F(3, 8))
    assert ha == scale(F(1, 2), add(ra, axis))
    assert hb == scale(F(1, 2), add(axis, lb))
    assert hc == scale(F(1, 2), add(rc, lc))
    identity = diag(1, 1, 1)
    assert ha == add(add(scale(F(1, 8), identity),
                        scale(F(1, 10), outer([3, 1, 0]))),
                     scale(-F(1, 8), diag(0, 0, 1)))
    assert hb == add(add(scale(F(1, 8), identity),
                        scale(F(1, 10), outer([3, 0, 1]))),
                     scale(-F(1, 8), diag(0, 1, 0)))
    assert add(hc, scale(-F(3, 8), identity)) == diag(F(3, 8), 0, 0)
    assert F(2) < F(9, 4) == F(3, 2) ** 2
    print(json.dumps({
        "status": "PASS", "arithmetic": "Python fractions.Fraction; no floats",
        "modulus_square_identities": len(squares),
        "symmetric_modulus_identities": 3, "rank_one_decompositions": 2,
        "scalar_statement": "2 < 9/4", "exact_scalar_gap": "1/4",
        "scope": "finite rational identities only; no Lean certification or universal unitary proof"
    }, indent=2))


if __name__ == "__main__":
    main()
