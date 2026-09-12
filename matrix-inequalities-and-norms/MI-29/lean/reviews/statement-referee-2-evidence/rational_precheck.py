"""Independent exact statement precheck; not a Lean certificate or CFC proof."""
from fractions import Fraction as Q
from itertools import permutations
import json
from pathlib import Path


def matrix(rows):
    return [[Q(x) for x in row] for row in rows]


def mul(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(3)), Q(0))
             for j in range(3)] for i in range(3)]


def power(a, exponent):
    out = matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]])
    for _ in range(exponent):
        out = mul(out, a)
    return out


def add(a, b):
    return [[a[i][j] + b[i][j] for j in range(3)] for i in range(3)]


def scale(q, a):
    return [[q * x for x in row] for row in a]


def sign(p):
    return (-1) ** sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3))


def det(a):
    return sum((sign(p) * a[0][p[0]] * a[1][p[1]] * a[2][p[2]]
                for p in permutations(range(3))), Q(0))


def polynomial_mul(a, b):
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def determinant_polynomial(d, h):
    out = [Q(0)] * 4
    for p in permutations(range(3)):
        term = [Q(sign(p))]
        for i in range(3):
            term = polynomial_mul(term, [d[i][p[i]], h[i][p[i]]])
        for i, x in enumerate(term):
            out[i] += x
    return out


def strings(a):
    if isinstance(a, list):
        return [strings(x) for x in a]
    return str(a)


a = matrix([[2, 0, 0], [0, 1, 0], [0, 0, Q(1, 2)]])
m = matrix([[-1, 2, 0], [2, 1, 2], [0, 2, 1]])
b = scale(Q(1, 5), m)
assert all(a[i][i] > 0 for i in range(3))
assert all(b[i][j] == b[j][i] for i in range(3) for j in range(3))
assert b[0][0] < 0 and b[1][1] > 0
assert det(b) == Q(-1, 125)
d = power(a, 6)
ab_gram = mul(mul(b, power(a, 2)), b)
ba_gram = mul(mul(a, power(b, 2)), a)
left = det(add(d, power(ab_gram, 4)))
right = det(add(d, power(ba_gram, 4)))
gap = right - left
assert left == Q(136990346414301954149, 61035156250000000000)
assert right == Q(4537743716162890657, 1907348632812500000)
assert gap == Q(21036678407451, 156250000000000) > 0
h = power(mul(mul(m, power(a, 2)), m), 4)
j = power(mul(mul(a, power(m, 2)), a), 4)
left_poly = determinant_polynomial(d, h)
right_poly = determinant_polynomial(d, j)
delta_poly = [x - y for x, y in zip(right_poly, left_poly)]
assert delta_poly == [Q(0), Q(2089017, 16), Q(-31188746592549, 1024), Q(0)]
z = Q(1, 5**8)
assert sum((c * z**k for k, c in enumerate(delta_poly)), Q(0)) == gap
assert det(h) == det(j)
record = {
    'status': 'PASS: exact rational statement precheck only',
    'method': 'Independent Fraction matrix products, repeated ring powers, six-permutation determinant and polynomial convolution',
    'a': strings(a), 'b': strings(b),
    'det_b': str(det(b)), 'indefiniteness_diagonal_witnesses': [str(b[0][0]), str(b[1][1])],
    'a_sixth_power': strings(d), 'ab_gram': strings(ab_gram), 'ba_gram': strings(ba_gram),
    'left_determinant': str(left), 'right_determinant': str(right), 'right_minus_left': str(gap),
    'optional_right_minus_left_polynomial_coefficients': strings(delta_poly),
    'optional_scale_z': str(z), 'exact_common_h_j_determinant': str(det(h)),
    'scope': 'CFC identities and complex positive definiteness remain Lean proof obligations; rational arithmetic does not establish them.'
}
Path(__file__).with_name('rational-precheck.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
