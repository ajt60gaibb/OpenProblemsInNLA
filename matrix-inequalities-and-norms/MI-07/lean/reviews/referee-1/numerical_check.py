"""Independent exact statement checks; not a Lean proof or an assumed certificate."""
from fractions import Fraction as Q
from pathlib import Path
import json


def product(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(2)) for j in range(2)]
            for i in range(2)]


def adjoint(a):
    # Every entry in this concrete witness is real.
    return [[a[j][i] for j in range(2)] for i in range(2)]


def scalar(c, a):
    return [[c * x for x in row] for row in a]


def plus(a, b):
    return [[a[i][j] + b[i][j] for j in range(2)] for i in range(2)]


def det(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


t, s = Q(5, 12), Q(13, 12)
assert s > 0 and s * s == 1 + t * t
a = [[Q(1), Q(0)], [Q(0), Q(0)]]
b = [[Q(0), t], [Q(0), Q(0)]]
x = plus(a, b)
v = [1 / s, t / s]
assert sum(z * z for z in v) == 1
q = [[v[i] * v[j] for j in range(2)] for i in range(2)]
assert q == [[Q(144, 169), Q(60, 169)], [Q(60, 169), Q(25, 169)]]
r = plus(a, q)
assert product(a, a) == a and product(q, q) == q
assert r[0][0] == Q(313, 169) and det(r) == Q(25, 169)
assert r[0][0] > 0 and det(r) > 0
right_b = [[Q(0), Q(0)], [Q(0), t]]
left_b = scalar(t, a)
right_x, left_x = scalar(s, q), scalar(s, a)
for z, right, left in [(a, a, a), (b, right_b, left_b), (x, right_x, left_x)]:
    assert product(right, right) == product(adjoint(z), z)
    assert product(left, left) == product(z, adjoint(z))
    for candidate in [right, left]:
        assert candidate == adjoint(candidate)
        assert candidate[0][0] >= 0 and candidate[1][1] >= 0 and det(candidate) >= 0
left_trace = 2 * s
right_trace = 1 + 2 * t
assert left_trace == Q(13, 6)
assert right_trace == Q(11, 6)
assert right_trace - left_trace == -Q(1, 3)

out = {
    "arithmetic": "Independent Python Fraction reconstruction, without floating point",
    "scope": "Statements only; actual CFC identification and convergence remain proof obligations",
    "squared_scale": str(s * s),
    "right_direction": [str(z) for z in v],
    "spanning_principal_minor": str(r[0][0]),
    "spanning_determinant": str(det(r)),
    "all_six_Gram_square_identities": True,
    "all_six_candidates_PSD_by_real_order_two_minors": True,
    "left_trace": str(left_trace),
    "right_trace": str(right_trace),
    "right_minus_left": str(right_trace - left_trace),
    "passed": True,
}
Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2) + "\n")
print("PASS: independent rational polar/projector/trace statement checks")
