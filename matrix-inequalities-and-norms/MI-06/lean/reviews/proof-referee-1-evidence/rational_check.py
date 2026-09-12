"""Independent exact arithmetic reconstruction; supplementary, not a Lean proof."""
from fractions import Fraction as F
from pathlib import Path
import json

def matrix(rows):
    return [[F(value) for value in row] for row in rows]

def transpose(a):
    return [list(row) for row in zip(*a)]

def add(a, b):
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]

def scale(c, a):
    return [[F(c) * x for x in row] for row in a]

def mul(a, b):
    return [[sum(x * y for x, y in zip(row, col))
             for col in transpose(b)] for row in a]

def outer(w):
    return [[F(x) * F(y) for y in w] for x in w]

def diagonal(values):
    return [[F(values[i]) if i == j else F(0)
             for j in range(len(values))] for i in range(len(values))]

def cone(terms):
    out = matrix([[0] * 3 for _ in range(3)])
    for coefficient, vector in terms:
        assert coefficient >= 0
        out = add(out, scale(coefficient, outer(vector)))
    return out

t = F(3, 4)
A = matrix([[1, t, 0], [0, 0, 0], [0, 0, 0]])
B = matrix([[-1, 0, 0], [0, 0, 0], [-t, 0, 0]])
AB = add(A, B)
e1, e2, e3 = [1, 0, 0], [0, 1, 0], [0, 0, 1]
terms = [
    [(F(1, 20), [4, 3, 0])],
    [(F(5, 4), e1)],
    [(F(5, 4), e1)],
    [(F(1, 20), [4, 0, 3])],
    [(t, e1), (t, e2)],
    [(t, e1), (t, e3)],
]
names = ['abs(A)', 'abs(A*)', 'abs(B)', 'abs(B*)', 'abs(A+B)', 'abs((A+B)*)']
arguments = [A, transpose(A), B, transpose(B), AB, transpose(AB)]
roots = [cone(ts) for ts in terms]
reported = [
    matrix([['4/5', '3/5', 0], ['3/5', '9/20', 0], [0, 0, 0]]),
    diagonal(['5/4', 0, 0]),
    diagonal(['5/4', 0, 0]),
    matrix([['4/5', 0, '3/5'], [0, 0, 0], ['3/5', 0, '9/20']]),
    diagonal(['3/4', '3/4', 0]),
    diagonal(['3/4', 0, '3/4']),
]
checks = []
for name, x, root, expected, decomposition in zip(names, arguments, roots, reported, terms):
    assert root == expected
    assert root == transpose(root)
    gram = mul(transpose(x), x)
    assert mul(root, root) == gram
    checks.append({'quantity': name, 'candidate': root, 'gram': gram,
                   'positive_outer_product_terms': decomposition,
                   'hermitian': True, 'squares_to_actual_gram': True,
                   'matches_statement_table': True})

SA, SB, SAB = [scale(F(1, 2), add(roots[i], roots[i + 1])) for i in [0, 2, 4]]
assert SA == matrix([['41/40', '3/10', 0], ['3/10', '9/40', 0], [0, 0, 0]])
assert SB == matrix([['41/40', 0, '3/10'], [0, 0, 0], ['3/10', 0, '9/40']])
assert SAB == diagonal(['3/4', '3/8', '3/8'])
identity = diagonal([1, 1, 1])
u, v = [3, 1, 0], [3, 0, 1]
DA = add(add(scale(F(1, 8), identity), scale(F(1, 10), outer(u))),
         scale(F(-1, 8), outer(e3)))
DB = add(add(scale(F(1, 8), identity), scale(F(1, 10), outer(v))),
         scale(F(-1, 8), outer(e2)))
assert SA == DA and SB == DB
lower_remainder = add(SAB, scale(F(-3, 8), identity))
assert lower_remainder == scale(F(3, 8), outer(e1))
gap = F(9, 4) - F(2)
assert gap == F(1, 4) and gap > 0
assert F(3, 2) / 4 == F(3, 8)

out = {
    'scope': 'Independent rational reconstruction only; not a Lean proof, certificate, or replacement for the separately recompiled Lean proof.',
    'parameter': t, 'A': A, 'B': B, 'A_plus_B': AB,
    'moduli': checks,
    'symmetric_A': SA, 'symmetric_B': SB, 'symmetric_sum': SAB,
    'decomposition_A': {'direction': u, 'missing_projector': outer(e3), 'identity_checked': True},
    'decomposition_B': {'direction': v, 'missing_projector': outer(e2), 'identity_checked': True},
    'sum_lower_bound_remainder': lower_remainder,
    'scalar_gap_9_over_4_minus_2': gap,
    'all_checks_pass': True,
}
path = Path(__file__).with_name('rational-check.json')
path.write_text(json.dumps(out, indent=2, default=str) + '\n')
print('PASS: six PSD root decompositions and actual Gram squares; three arithmetic averages; both rank-one identities; homogeneous lower-bound remainder; positive gap 1/4.')
