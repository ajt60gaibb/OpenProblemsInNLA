"""Independent integer reconstruction from all actual generator-index tuples.

This is supplementary statement-review evidence, not a Lean proof certificate.
No floating-point arithmetic or symbolic equations are assumed from the source.
"""

from collections import defaultdict
from itertools import product
from pathlib import Path
import json

h = (2, 0, 1, 0, 2, 0, -1)

lower = []
for i in range(3):
    coefficients = defaultdict(int)
    for j, k in product(range(3), repeat=2):
        powers = tuple(int(a == j) + int(a == k) for a in range(3))
        coefficients[powers] += h[i + j + k]
    lower.append({p: c for p, c in coefficients.items() if c})

expected_lower = [
    {(2, 0, 0): 2, (0, 2, 0): 1, (1, 0, 1): 2, (0, 0, 2): 2},
    {(1, 1, 0): 2, (0, 1, 1): 4},
    {(2, 0, 0): 1, (0, 2, 0): 2, (1, 0, 1): 4, (0, 0, 2): -1},
]
assert lower == expected_lower

v = (0, 1)
upper = []
upper_survivors = []
for i in range(2):
    total = 0
    surviving_tuples = []
    for indices in product(range(2), repeat=5):
        factor = 1
        for j in indices:
            factor *= v[j]
        total += h[i + sum(indices)] * factor
        if factor:
            surviving_tuples.append(indices)
    upper.append(total)
    upper_survivors.append(surviving_tuples)
assert upper == [0, -1]
assert upper == [-1 * z**5 for z in v]
assert all(s == [(1, 1, 1, 1, 1)] for s in upper_survivors)

# At x=(1,0,t), reconstruct the three contraction polynomials in t from h.
lower_t = []
for coefficients in lower:
    poly = defaultdict(int)
    for (p0, p1, p2), c in coefficients.items():
        if p1 == 0:
            poly[p2] += c
    lower_t.append(dict(poly))
assert lower_t == [{0: 2, 1: 2, 2: 2}, {}, {0: 1, 1: 4, 2: -1}]
root_poly = defaultdict(int)
for degree, c in lower_t[0].items():
    root_poly[degree + 2] += c
for degree, c in lower_t[2].items():
    root_poly[degree] -= c
root_poly = dict(root_poly)
assert root_poly == {4: 2, 3: 2, 2: 3, 1: -4, 0: -1}
evaluate = lambda t: sum(c * t**d for d, c in root_poly.items())
assert evaluate(0) == -1
assert evaluate(1) == 2

result = {
    "status": "PASS",
    "scope": "Exact supplementary finite statement checks; no universal Lean proof claimed",
    "parameters": {"m": 3, "q": 2, "n": 2},
    "generator": h,
    "generating_lengths": [3 * (3 - 1) + 1, 6 * (2 - 1) + 1],
    "lower_entries_reconstructed": 27,
    "lower_contraction_coefficients": [
        {str(p): c for p, c in sorted(coefficients.items())} for coefficients in lower
    ],
    "upper_entries_contracted": 64,
    "upper_contraction": upper,
    "upper_surviving_tuples_per_component": upper_survivors,
    "upper_eigenvalue": -1,
    "upper_vector": v,
    "root_polynomial_coefficients": dict(sorted(root_poly.items())),
    "root_polynomial_at_zero": evaluate(0),
    "root_polynomial_at_one": evaluate(1),
}
output = Path(__file__).with_suffix(".json")
output.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
