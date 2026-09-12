"""Independent exact tensor transcription check; not a universal Lean proof."""
from collections import defaultdict
from itertools import product
import json

h = (2, 0, 1, 0, 2, 0, -1)
expected = [
    {(2, 0, 0): 2, (0, 2, 0): 1, (1, 0, 1): 2, (0, 0, 2): 2},
    {(1, 1, 0): 2, (0, 1, 1): 4},
    {(2, 0, 0): 1, (0, 2, 0): 2, (1, 0, 1): 4, (0, 0, 2): -1},
]
lower = []
for i in range(3):
    polynomial = defaultdict(int)
    for j, k in product(range(3), repeat=2):
        exponent = tuple(int(j == r) + int(k == r) for r in range(3))
        # Independent one-based source index sum minus the tensor order.
        coefficient = h[(i+1) + (j+1) + (k+1) - 3]
        polynomial[exponent] += coefficient
    polynomial = {e: c for e, c in polynomial.items() if c}
    assert polynomial == expected[i]
    lower.append({str(e): c for e, c in sorted(polynomial.items())})

upper = []
survivors = []
v = (0, 1)
for i in range(2):
    value = 0
    surviving = []
    for contracted in product(range(2), repeat=5):
        weight = 1
        for j in contracted:
            weight *= v[j]
        if weight:
            surviving.append(contracted)
        source_index = (i+1) + sum(j+1 for j in contracted) - 6
        value += h[source_index] * weight
    assert surviving == [(1, 1, 1, 1, 1)]
    upper.append(value)
    survivors.append(surviving)
assert upper == [0, -1]
assert upper == [-x**5 for x in v]

# λ(t)*t² minus the third contraction at (1,0,t), coefficients ascending.
eigenvalue = [2, 2, 2]
third = [1, 4, -1]
residual = [0, 0] + eigenvalue
for j, coefficient in enumerate(third):
    residual[j] -= coefficient
assert residual == [-1, -4, 3, 2, 2]
assert residual[0] == -1 and sum(residual) == 2
print(json.dumps({
    "status": "PASS: finite exact transcription diagnostics, not a universal proof",
    "all_lower_entries": 27, "lower_contraction_coefficients": lower,
    "all_upper_entries_used_in_components": 64, "upper_contraction": upper,
    "only_surviving_contracted_tuple_per_component": survivors,
    "IVT_polynomial_ascending_coefficients": residual,
    "IVT_endpoint_values": [-1, 2],
    "first_lower_slice_strict_positivity_reason": "sum of all three coordinate squares plus (x0+x2)^2",
    "generating_vector_length": len(h)
}, indent=2))
