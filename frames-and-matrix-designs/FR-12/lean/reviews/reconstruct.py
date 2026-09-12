"""Exact finite diagnostics for the proposed restricted construction, not a proof."""
from itertools import product, permutations
from math import factorial
import json


def hadamard(a):
    n = len(a)
    return all(len(row) == n and all(x in (-1, 1) for x in row) for row in a) and all(
        sum(a[i][k] * a[j][k] for k in range(n)) == (n if i == j else 0)
        for i in range(n) for j in range(n)
    )


def matrices(n):
    return [a for entries in product((-1, 1), repeat=n*n)
            if hadamard(a := tuple(tuple(entries[i*n:(i+1)*n]) for i in range(n)))]


records = []
for m, expected_inputs, expected_outputs in [(1, 2, 4), (2, 8, 128)]:
    source = matrices(m)
    assert len(source) == expected_inputs
    outputs = {}
    for a, b, sigma in product(source, source, permutations(range(m))):
        c = tuple(a[i] + b[i] for i in range(m)) + tuple(
            a[sigma[i]] + tuple(-x for x in b[sigma[i]]) for i in range(m)
        )
        assert hadamard(c)
        recovered_a = tuple(row[:m] for row in c[:m])
        recovered_b = tuple(row[m:] for row in c[:m])
        recovered_sigma = tuple(recovered_a.index(row[:m]) for row in c[m:])
        assert (recovered_a, recovered_b, recovered_sigma) == (a, b, sigma)
        assert c not in outputs
        outputs[c] = (a, b, sigma)
    assert len(outputs) == expected_outputs == factorial(m) * len(source)**2
    records.append({"m": m, "H_m": len(source), "distinct_valid_outputs": len(outputs),
                    "all_triples_recovered": True})

# Exact integer reformulation of the claimed real-exponent bound for a lower
# recurrence starting with just one known order-one matrix. Checking finitely
# many k is a transcription diagnostic, not the universal induction.
lower = 1
recurrence_checks = []
for K in range(1, 11):
    m = 2**(K-1)
    lower = factorial(m) * lower**2
    if K >= 2:
        exponent_eighth_power = 2**K * (K-1) * (K-2)
        assert lower**8 >= 2**exponent_eighth_power
        recurrence_checks.append({"K": K, "eighth_power_bound": True})
print(json.dumps({"scope": "Finite exact diagnostics only; no universal certificate",
                  "restricted_constructions": records,
                  "lower_recurrence_checks": recurrence_checks}, indent=2))
