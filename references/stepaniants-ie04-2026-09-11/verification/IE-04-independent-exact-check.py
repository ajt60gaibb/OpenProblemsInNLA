#!/usr/bin/env python3
"""Separate exact rational spot checks; the all-n proof is analytic.

This checker was written independently of the supplied interval-arithmetic
checker. It performs exact GEPP on W_n and on all corners in orders 2 and 3.
Corner checks are supplementary and do not certify the interior of a box.
"""
from fractions import Fraction as F
from itertools import product
import json


def model(n, k):
    c = F(3, 2) ** k
    return [[c if j == n - 1 else F(1) if i == j else
             F(-1, 2) if i > j else F(0)
             for j in range(k, n)] for i in range(k, n)]


def eliminate(a, delta):
    n = len(a)
    b = 2 ** (n + 2)
    initial = max(abs(x) for row in a for x in row)
    largest = initial
    stage = [row[:] for row in a]
    for k in range(n):
        exact = model(n, k)
        error = max(abs(stage[i][j] - exact[i][j])
                    for i in range(n-k) for j in range(n-k))
        assert error <= b ** k * delta <= F(1, 8)
        largest = max(largest, max(abs(x) for row in stage for x in row))
        assert stage[0][0] > 0
        if k == n - 1:
            break
        assert abs(stage[0][0]) > max(abs(row[0]) for row in stage[1:])
        stage = [[stage[i][j] - stage[i][0] * stage[0][j] / stage[0][0]
                  for j in range(1, n-k)] for i in range(1, n-k)]
    growth = largest / initial
    assert growth > F(1, 2) * F(3, 2) ** (n-1)
    return growth


def main():
    models = []
    for n in range(2, 25):
        delta = F(1, 2 ** (n*n+n+1))
        b = 2 ** (n+2)
        assert b ** (n-1) * delta == F(1, 8)
        growth = eliminate(model(n, 0), delta)
        assert growth == F(3, 2) ** (n-1)
        models.append(n)
    corners = {}
    for n in (2, 3):
        w = model(n, 0)
        delta = F(1, 2 ** (n*n+n+1))
        smallest = None
        count = 0
        for signs in product((-1, 1), repeat=n*n):
            a = [[w[i][j] + signs[i*n+j] * delta for j in range(n)]
                 for i in range(n)]
            growth = eliminate(a, delta)
            smallest = growth if smallest is None else min(smallest, growth)
            count += 1
        corners[n] = {"corners": count, "minimum_exact_growth": str(smallest)}
    scalar_cases = []
    for n in range(2, 513):
        e = F(1, 8)
        assert (F(1, 2) + e)/(1-e) == F(5, 7) < 1
        assert F(3, 2)/(1-e) <= 2
        assert 2 + 2**(n+1) <= 2**(n+2)
        assert n*n*(n*n+n+5) <= 3*n**4
        c = F(3, 2)**(n-1)
        assert (8*c-1)/9 >= 7*c/9 > c/2
        scalar_cases.append(n)
    print(json.dumps({
        "status": "PASS",
        "method": "exact Fraction GEPP, not interval arithmetic",
        "unperturbed_dimensions": models,
        "complete_corner_checks": corners,
        "scalar_dimensions": [min(scalar_cases), max(scalar_cases)],
        "scope": "Finite supplementary checks only; see analytic review for all n."
    }, indent=2) + "\n", end="")


if __name__ == "__main__":
    main()
