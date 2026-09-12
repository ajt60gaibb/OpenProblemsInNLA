#!/usr/bin/env python3
"""Independent finite exact checks; no universal or Lean proof is inferred."""
from fractions import Fraction as F
from itertools import combinations, product
from math import factorial
from pathlib import Path
import json


def subset_sum(xs, j):
    total = F(0)
    for indices in combinations(range(len(xs)), j):
        term = F(1)
        for i in indices:
            term *= xs[i]
        total += term
    return total


def coefficients(xs):
    p = [F(1)]
    for a in xs:
        q = [F(0)] * (len(p) + 1)
        for i, c in enumerate(p):
            q[i] += c
            q[i + 1] += a * c
        p = q
    return p


def derivative(p):
    return [F(j) * p[j] for j in range(1, len(p))] or [F(0)]


tuples = differences = endpoints = pair_cases = repeated_cases = 0
for n in range(0, 7):
    # Repeated and all-equal tuples occur naturally, including the empty tuple.
    for xs in product([F(1, 5), F(7, 3)], repeat=n):
        tuples += 1
        es = [subset_sum(xs, j) for j in range(n + 2)]
        assert es[0] == 1 and es[n + 1] == 0
        assert all(e > 0 for e in es[:n + 1])
        p = coefficients(xs)
        assert p == es[:-1]
        q = p
        for d in range(n + 2):
            expected = factorial(d) * (es[d] if d <= n else 0)
            assert q[0] == expected
            if d <= n:
                assert q[-1] > 0 and len(q) - 1 == n - d
            q = derivative(q)
        if n >= 3:
            seq = [(j + 1) * es[j + 1] / es[j] for j in range(n + 1)]
            assert seq[n] == 0
            for j in range(2, n):
                differences += 1
                gap = seq[j - 1] - 2 * seq[j] + seq[j + 1]
                assert gap >= 0
                q = p
                for _ in range(j - 1):
                    q = derivative(q)
                assert len(q) - 1 == n - (j - 1) >= 2
                q1, q2 = derivative(q), derivative(derivative(q))
                q3 = derivative(q2)
                assert q1[0] / q[0] == seq[j - 1]
                assert q2[0] / q1[0] == seq[j]
                assert q3[0] / q2[0] == seq[j + 1]
                if j == n - 1:
                    endpoints += 1
                    assert len(q) == 3 and q3 == [F(0)]
                if len(set(xs)) == 1:
                    repeated_cases += 1
                    assert gap == 0

for m in range(2, 7):
    for mu in product([F(2, 7), F(11, 5)], repeat=m):
        pair_cases += 1
        s1, s2, s3 = [sum(a ** r for a in mu) for r in (1, 2, 3)]
        pair = sum(mu[a] * mu[b] * (mu[a] - mu[b]) ** 2
                   for a, b in combinations(range(m), 2))
        den = s1 * (s1 * s1 - s2)
        assert den > 0 and pair >= 0
        assert s1 * s3 - s2 ** 2 == pair
        q = coefficients(mu)
        q1, q2 = derivative(q), derivative(derivative(q))
        q3 = derivative(q2)
        actual = q1[0] / q[0] - 2 * q2[0] / q1[0] + q3[0] / q2[0]
        assert actual == 2 * pair / den
        if m == 2:
            assert q3 == [F(0)]

result = {
    "status": "PASS: independent exact finite diagnostics",
    "scope": "Checks cannot prove universal convexity, derivative real-rootedness, or any Lean theorem.",
    "input_tuples": tuples,
    "canonical_second_differences": differences,
    "upper_endpoint_cases": endpoints,
    "all_equal_zero_second_differences": repeated_cases,
    "independent_positive_mu_pair_certificates": pair_cases,
    "checks": ["literal subset sums versus product coefficients", "e0=1; oversized e=0; positivity",
               "all derivative-at-zero factorial identities and exact degrees through d=n",
               "all canonical j=2..n-1 differences", "derivative order j-1, factor count n-j+1",
               "n=3 and upper-endpoint quadratic third derivative zero", "unordered pair count and exact factor2",
               "positive denominator; repeated and all-equal tuples", "empty dimension auxiliary identities"],
}
Path(__file__).with_name("exact-diagnostic.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
