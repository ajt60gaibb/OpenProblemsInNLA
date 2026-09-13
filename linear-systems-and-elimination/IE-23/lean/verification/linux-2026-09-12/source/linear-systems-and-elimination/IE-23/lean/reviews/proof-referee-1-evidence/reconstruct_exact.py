"""Referee 1 independent rational and complex-polynomial FINAL proof diagnostics.

The same referee independently reuses its prior coefficient-polynomial checker,
now parses the actual frozen Lean data and reruns all identities. No author code.

No submitted verification code, author diagnostic, SymPy, or floating point.
Polynomial variables represent arbitrary real and imaginary parts, not samples.
"""
from pathlib import Path
from fractions import Fraction as Q
import json
import hashlib
import re


class Poly:
    def __init__(self, x=0):
        self.c = dict(x) if isinstance(x, dict) else ({(0, 0, 0, 0): Q(x)} if x else {})
        self.c = {e: Q(c) for e, c in self.c.items() if c}

    def __add__(self, other):
        other = lift(other)
        d = self.c.copy()
        for e, c in other.c.items():
            d[e] = d.get(e, Q(0)) + c
        return Poly(d)

    __radd__ = __add__

    def __neg__(self):
        return Poly({e: -c for e, c in self.c.items()})

    def __sub__(self, other):
        return self + -lift(other)

    def __rsub__(self, other):
        return lift(other) + -self

    def __mul__(self, other):
        other = lift(other)
        d = {}
        for e, c in self.c.items():
            for f, k in other.c.items():
                g = tuple(a + b for a, b in zip(e, f))
                d[g] = d.get(g, Q(0)) + c * k
        return Poly(d)

    __rmul__ = __mul__

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        p = Poly(1)
        for _ in range(n):
            p = p * self
        return p

    def __eq__(self, other):
        return self.c == lift(other).c


def lift(x):
    return x if isinstance(x, Poly) else Poly(x)


def variable(i):
    return Poly({tuple(int(j == i) for j in range(4)): 1})


def transpose(m):
    return [list(row) for row in zip(*m)]


def matmul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def act(a, x):
    return [sum(a[i][j] * x[j] for j in range(len(x))) for i in range(len(a))]


P = Path(__file__).resolve().parents[2]
source = (P / 'NLA/IE23/Definitions.lean').read_text()
def matrix_literal(name):
    match = re.search(r'^def ' + name + r'[^\n]*:=\s*(.*?)!!\[([^]]+)\]', source, re.M)
    assert match, name
    scale = Q(1, 3) if match[1].strip() == '(1 / 3 : ℂ) •' else Q(1)
    assert match[1].strip() in ('', '(1 / 3 : ℂ) •'), match[1]
    return [[scale * Q(x.strip()) for x in row.split(',')] for row in match[2].split(';')]
A = matrix_literal('witnessA')
B = matrix_literal('witnessB')
X = matrix_literal('witnessX')
G = matrix_literal('witnessGram')
Gi = matrix_literal('witnessGramInv')
I2 = [[Q(1), Q(0)], [Q(0), Q(1)]]
assert matmul(A, transpose(A)) == G
assert matmul(G, Gi) == I2 and matmul(Gi, G) == I2
assert matmul(transpose(A), Gi) == B
assert matmul(A, B) == I2 and matmul(A, X) == I2 and B != X
assert matmul(transpose(B), B) == Gi and matmul(transpose(X), X) == I2
assert A[0][1] * A[1][2] - A[0][2] * A[1][1] == 1  # a nonzero full-row minor
z = [Q(x.strip()) for x in re.search(r'^def normingVector[^\n]*:= !\[([^]]+)\]',source,re.M)[1].split(',')]
assert act(B, z) == act(X, z) == [Q(0), Q(1), Q(-1)]
assert sum(t * t for t in act(B, z)) == 2 and sum(t**4 for t in z) == 2

u = [variable(0), variable(1)]
v = [variable(2), variable(3)]


def norm_sq(w):
    return w[0]**2 + w[1]**2


def complex_real_matrix_action(m, vec):
    return [[sum(m[i][j] * vec[j][part] for j in range(len(vec))) for part in range(2)]
            for i in range(len(m))]


by = complex_real_matrix_action(B, [u, v])
xy = complex_real_matrix_action(X, [u, v])
rhs = norm_sq(u) + norm_sq(v)
sum_uv = [u[k] + v[k] for k in range(2)]
assert sum(norm_sq(w) for w in by) + Q(1, 3) * norm_sq(sum_uv) == rhs
assert sum(norm_sq(w) for w in xy) == rhs
assert 2 * (norm_sq(u)**2 + norm_sq(v)**2) - rhs**2 == (norm_sq(u) - norm_sq(v))**2

# A Y = I gives row1=(1,0)-row0 and row2=(0,1)-row0,
# uniquely for every complex row0=(a,b); check the resulting universal equations.
Yre = [[u[0], v[0]], [1 - u[0], -v[0]], [-u[0], 1 - v[0]]]
Yim = [[u[1], v[1]], [-u[1], -v[1]], [-u[1], -v[1]]]
assert matmul(A, Yre) == I2
assert matmul(A, Yim) == [[Q(0), Q(0)], [Q(0), Q(0)]]
yz = list(zip(act(Yre, z), act(Yim, z)))
t = [u[k] - v[k] for k in range(2)]
assert sum(norm_sq(w) for w in yz) == 2 + 3 * norm_sq(t)

record = {
    'verdict': 'PASS', 'actual_frozen_definition_sha256': hashlib.sha256(source.encode()).hexdigest(), 'arithmetic': 'exact rational matrices and four-real-variable coefficientwise polynomials',
    'matrix_products': 8, 'nonzero_rank_minor': '1',
    'norming_vector': [1, -1], 'Bz_and_Xz': ['0', '1', '-1'],
    'norming_numerator_squared': '2', 'norming_denominator_fourth_power': '2',
    'universal_complex_B_action_identity': True,
    'universal_complex_X_squared_norm_identity': True,
    'universal_complex_all_competitor_squared_norm_identity': True,
    'norm_comparison_SOS_identity': True,
    'continuum_status': 'Coefficient identities cover arbitrary real/imaginary parts; actual roots, norms, suprema, rank and totalized inverse bridges remain Lean theorem conclusions.',
    'no_oracle_or_Lean_premise': True,
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
}
Path(__file__).with_name('exact-reconstruction.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
