"""Independent integer/polynomial diagnostics; not premises of any Lean theorem.

This does not import the submitted checker, SymPy, or any floating-point library.
The polynomial identity is checked coefficientwise in three indeterminates.
"""
from itertools import permutations, product, combinations
from pathlib import Path
import hashlib
import json


def constant(n):
    return {(0, 0, 0): n} if n else {}


def add(*ps):
    out = {}
    for p in ps:
        for e, c in p.items():
            out[e] = out.get(e, 0) + c
    return {e: c for e, c in out.items() if c}


def neg(p):
    return {e: -c for e, c in p.items()}


def sub(p, q):
    return add(p, neg(q))


def mul(p, q):
    out = {}
    for e, c in p.items():
        for f, d in q.items():
            g = tuple(x + y for x, y in zip(e, f))
            out[g] = out.get(g, 0) + c * d
    return {e: c for e, c in out.items() if c}


def determinant(matrix):
    terms = []
    for perm in permutations(range(3)):
        inversions = sum(perm[i] > perm[j] for i in range(3) for j in range(i + 1, 3))
        term = constant((-1) ** inversions)
        for i in range(3):
            term = mul(term, matrix[i][perm[i]])
        terms.append(term)
    return add(*terms)


ell, a, b = {(1, 0, 0): 1}, {(0, 1, 0): 1}, {(0, 0, 1): 1}
matrix = [[sub(ell, constant(25)), neg(a), neg(b)],
          [constant(-1), add(ell, constant(1)), {}],
          [constant(-1), {}, sub(ell, constant(1))]]
actual = determinant(matrix)
expected = sub(sub(mul(sub(ell, constant(25)), sub(mul(ell, ell), constant(1))),
                   mul(a, sub(ell, constant(1)))), mul(b, add(ell, constant(1))))
assert actual == expected


def family(x, y):
    return [[25, x, y], [1, -1, 0], [1, 0, 1]]


def det_value(value, x, y):
    shifted = [[constant((value if i == j else 0) - family(x, y)[i][j])
                for j in range(3)] for i in range(3)]
    return determinant(shifted).get((0, 0, 0), 0)


witnesses = [(-3, -21, 154, [-4, 2, 1]), (0, -16, 9, [-1, -1, 1]),
             (3, -146, 29, [4, 1, 2]), (25, -91, 84, [312, 12, 13])]
eigenpairs = []
lower, upper = family(-166, 9), family(-16, 159)
assert all(lower[i][j] <= upper[i][j] for i in range(3) for j in range(3))
assert [(i, j) for i in range(3) for j in range(3) if lower[i][j] != upper[i][j]] == [(0, 1), (0, 2)]
for value, x, y, vector in witnesses:
    m = family(x, y)
    image = [sum(m[i][j] * vector[j] for j in range(3)) for i in range(3)]
    assert -166 <= x <= -16 and 9 <= y <= 159
    assert any(vector) and image == [value * c for c in vector]
    assert all(lower[i][j] <= m[i][j] <= upper[i][j] for i in range(3) for j in range(3))
    assert det_value(value, x, y) == 0
    eigenpairs.append({'lambda': value, 'a': x, 'b': y, 'vector': vector, 'image': image})

separators = [(-1, -332, -32), (1, -318, -18), (12, -3750, -150)]
excluded = []
for value, low, high in separators:
    corners = [{'a': x, 'b': y, 'det': det_value(value, x, y)}
               for x, y in product([-166, -16], [9, 159])]
    assert (min(c['det'] for c in corners), max(c['det'] for c in corners)) == (low, high)
    assert high <= -18 < 0
    center = (value - 25) * (value * value + 6)
    radius = 75 * (abs(value - 1) + abs(value + 1))
    assert (center - radius, center + radius) == (low, high)
    excluded.append({'lambda': value, 'bounds': [low, high], 'corners': corners,
                     'affine_slopes_a_b': [-(value - 1), -(value + 1)]})

pair_separations = []
for i, j in combinations(range(4), 2):
    choices = [s for s, _, _ in separators if witnesses[i][0] < s < witnesses[j][0]]
    assert choices
    pair_separations.append({'indices': [i, j], 'strictly_intervening_separators': choices})

record = {
    'verdict': 'PASS: exact polynomial identity, four nonzero eigenpairs, twelve corner values, six pair separations',
    'scope': 'Independent diagnostics only; universal interval bounds and topology remain Lean proof obligations.',
    'coefficient_order': ['lambda', 'a', 'b'],
    'determinant_coefficients': [{'exponents': list(e), 'coefficient': c} for e, c in sorted(actual.items())],
    'eigenpairs': eigenpairs, 'separators': excluded, 'pair_separations': pair_separations,
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
}
Path(__file__).with_name('exact-checks.json').write_text(json.dumps(record, indent=2) + '\n')
print(record['verdict'])
