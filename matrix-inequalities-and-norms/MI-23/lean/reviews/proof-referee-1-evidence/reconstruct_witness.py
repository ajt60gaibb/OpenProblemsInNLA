#!/usr/bin/env python3
"""Independent exact reconstruction for MI-23 referee 1.

This supplementary Fraction calculation is not a Lean proof certificate.
It recomputes each power by repeated multiplication from the original T,
independently of the proof author's squaring/addition-chain certificates.
"""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import json


def matrix(rows):
    return [[F(x) for x in row] for row in rows]


def eye(n):
    return matrix([[int(i == j) for j in range(n)] for i in range(n)])


def transpose(A):
    return list(map(list, zip(*A)))


def mul(A, B):
    assert len(A[0]) == len(B)
    return [[sum((a * b for a, b in zip(row, col)), F(0))
             for col in transpose(B)] for row in A]


def power(A, k):
    result = eye(len(A))
    for _ in range(k):
        result = mul(result, A)
    return result


def determinant(A):
    n = len(A)
    value = F(0)
    for p in permutations(range(n)):
        sign = (-1) ** sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n))
        term = F(sign)
        for i in range(n):
            term *= A[i][p[i]]
        value += term
    return value


def serial(A):
    return [[str(x) for x in row] for row in A]


D = matrix([[16, 0, 0], [0, F(1, 12), 0], [0, 0, 1]])
Di = matrix([[F(1, 16), 0, 0], [0, 12, 0], [0, 0, 1]])
T = matrix([[2, 1, 2], [1, 25, -10], [2, -10, 10]])
L = matrix([[1, 0, 0], [F(1, 2), 1, 0], [1, F(-22, 49), 1]])
P = matrix([[2, 0, 0], [0, F(49, 2), 0], [0, 0, F(150, 49)]])
assert mul(D, Di) == eye(3) == mul(Di, D)
assert mul(mul(L, P), transpose(L)) == T
assert determinant(L) == 1
minors = [determinant([row[:k] for row in T[:k]]) for k in (1, 2, 3)]
assert minors == [2, 49, 150]
assert all(P[i][i] > 0 and D[i][i] > 0 for i in range(3))

expected_powers = {
    2: [[9, 7, 14], [7, 726, -348], [14, -348, 204]],
    4: [[326, 273, 546], [273, 648229, -323542], [546, -323542, 162916]],
    7: [[77338, 64849, 129698], [64849, 17496054377, -8747891246],
        [129698, -8747891246, 4374217508]],
    8: [[478921, 401583, 803166], [401583, 524880336734, -262439326532],
        [803166, -262439326532, 131221346936]],
}
powers = {k: power(T, k) for k in expected_powers}
assert all(powers[k] == matrix(expected_powers[k]) for k in powers)

A = power(D, 2)
B = mul(mul(D, powers[8]), D)
G = mul(mul(D, T), D)
H = mul(mul(D, powers[7]), D)
assert B == matrix([[122603776, 535444, 12850656],
                    [535444, F(262440168367, 72), F(-65609831633, 3)],
                    [12850656, F(-65609831633, 3), 131221346936]])
assert G == matrix([[512, F(4, 3), 32], [F(4, 3), F(25, 144), F(-5, 6)],
                    [32, F(-5, 6), 10]])
assert H == matrix([[19798528, F(259396, 3), 2075168],
                    [F(259396, 3), F(17496054377, 144), F(-4373945623, 6)],
                    [2075168, F(-4373945623, 6), 4374217508]])
assert mul(mul(Di, B), Di) == powers[8]
assert all(M == transpose(M) for M in (D, T, A, B, G, H))
all_minors = {name: [determinant([row[:k] for row in M[:k]]) for k in (1, 2, 3)]
              for name, M in [('D', D), ('T', T), ('A', A), ('B', B), ('G', G), ('H', H)]}
assert all(v > 0 for values in all_minors.values() for v in values)

AB = mul(A, B)
GH = mul(G, H)
entry = GH[0][2]
frob = sum((x * x for row in AB for x in row), F(0))
gap = entry * entry - frob
assert entry == F(1260589125202, 9)
assert frob == F(2009446159144992718181231562721, 107495424)
assert gap == F(99434824489435745411095588895, 107495424) > 0
# The selected canonical parameters satisfy the actual unrestricted target's hypotheses.
r = s = F(1)
p = F(2)
t = F(1, 8)
assert p >= 1 and 0 <= t <= 1 and ((r >= 1 and s >= 1) or (r <= 0 and s <= 0))
assert p * (r + s - 1) == 2 and 1 - t == F(7, 8)

result = {
    'scope': 'Independent exact Fraction diagnostic; no approximate eigenvalue computation; not a replacement for the Lean proof.',
    'method': 'Naive repeated multiplication for each power, permutation determinant, full entrywise squared sum.',
    'powers': {str(k): serial(M) for k, M in powers.items()},
    'matrices': {name: serial(M) for name, M in [('D', D), ('T', T), ('A', A), ('B', B), ('G', G), ('H', H), ('AB', AB), ('GH', GH)]},
    'leading_principal_minors': {name: list(map(str, values)) for name, values in all_minors.items()},
    'GH_entry_0_2': str(entry),
    'frobeniusSquared_AB': str(frob),
    'exact_gap': str(gap),
    'parameters': {name: str(value) for name, value in [('r', r), ('s', s), ('p', p), ('t', t)]},
    'verdict': 'PASS',
}
target = Path(__file__).with_name('independent-rational-check.json')
target.write_text(json.dumps(result, indent=2) + '\n')
print('PASS: exact powers, LDL, all six PD minor diagnostics, CFC normalizing identity, full Frobenius sum and strict rational gap.')
print('Retained numerical target:', gap)
