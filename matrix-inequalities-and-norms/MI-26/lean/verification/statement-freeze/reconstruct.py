"""Exact rational pre-proof check; not a replacement for Lean verification."""
from fractions import Fraction as F


def add(a, b):
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def sub(a, b):
    return [[x - y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def vec(a, v):
    return [sum(x * y for x, y in zip(row, v)) for row in a]


def display(name, a):
    print(name, [[str(x) for x in row] for row in a])


p = [[F(1), F(0)], [F(0), F(0)]]
q = [[F(9, 25), F(12, 25)], [F(12, 25), F(16, 25)]]
f = [[F(-18, 25), F(-12, 25)], [F(-12, 25), F(0)]]
w = [F(1), F(-2)]
u = [F(3, 5), F(4, 5)]
assert sum(x * x for x in u) == 1
assert q == [[x * y for y in u] for x in u]
assert mul(p, p) == p
assert mul(q, q) == q
s = add(p, q)
s2 = mul(s, s)
assert s == [[F(34, 25), F(12, 25)], [F(12, 25), F(16, 25)]]
assert s2 == [[F(52, 25), F(24, 25)], [F(24, 25), F(16, 25)]]
assert sub(s, s2) == f
assert sub(p, mul(p, p)) == [[0, 0], [0, 0]]
assert sub(q, mul(q, q)) == [[0, 0], [0, 0]]
assert vec(f, w) == [F(6, 25), F(-12, 25)]
quadratic = sum(x * y for x, y in zip(w, vec(f, w)))
assert quadratic == F(6, 5) and quadratic > 0
assert 2 - 2**2 == -2
for name, value in [('P', p), ('Q', q), ('P+Q', s), ('(P+Q)^2', s2), ('F', f)]:
    display(name, value)
print('Fw', [str(x) for x in vec(f, w)])
print('w*Fw', str(quadratic))
print('Admissibility Gram/projection and exact rational numerical data: PASS')
print('This is supplementary finite arithmetic, not a Lean proof.')
