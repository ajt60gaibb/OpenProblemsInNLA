"""Independent MI-22 final proof referee 1 exact adapted-witness reconstruction.
Uses only Fraction, permutation determinants and naive repeated products.
Does not import any author/submission verifier and evaluates no spectral root.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import permutations
import hashlib, json, re

OUT = Path(__file__).resolve().parent
PROJECT = OUT.parents[1]
REPO = PROJECT.parents[2]


def matrix(rows): return [[F(x) for x in row] for row in rows]
def transpose(A): return list(map(list, zip(*A)))
def eye(n): return matrix([[int(i == j) for j in range(n)] for i in range(n)])


def mul(A, B):
    assert len(A[0]) == len(B)
    return [[sum((x * y for x, y in zip(row, col)), F(0))
             for col in transpose(B)] for row in A]


def power(A, k):
    answer = eye(len(A))
    for _ in range(k): answer = mul(answer, A)
    return answer


def determinant(A):
    result = F(0)
    for p in permutations(range(len(A))):
        term = F((-1) ** sum(p[i] > p[j] for i in range(len(A)) for j in range(i + 1, len(A))))
        for i in range(len(A)): term *= A[i][p[i]]
        result += term
    return result


def encode(A): return [[str(x) for x in row] for row in A]


source = REPO / 'references/colbrook-matrix-2026-09-11/original-proofs/MI-22.tex'
assert hashlib.sha256(source.read_bytes()).hexdigest() == '4c7c612af0a3f285c1d373d16847450d7fb99582fd2906eec8202c2a8ea9c5a4'
block = re.search(r'R=10\^\{-15\}\\begin\{pmatrix\}(.*?)\\end\{pmatrix\}', source.read_text(), re.S)
assert block is not None
values = [int(x) for x in re.findall(r'-?\d+', block.group(1))]
assert len(values) == 9
R = [[F(values[3 * i + j], 10**15) for j in range(3)] for i in range(3)]
M = matrix([[4616, -39, -1250], [-39, 55069, -1519], [-1250, -1519, 6499]])
T = [[x / 8192 for x in row] for row in M]
errors = [[abs(8192 * R[i][j] - M[i][j]) for j in range(3)] for i in range(3)]
# A strict half-unit distance proves unique nearest rounding without any tie rule.
assert all(x < F(1, 2) for row in errors for x in row)
assert R == transpose(R) and T == transpose(T)
minors_M = [determinant([row[:k] for row in M[:k]]) for k in (1, 2, 3)]
assert minors_M == [4616, 254196983, 1555181999141]
H = matrix([[1, 0, 0], [F(-39, 4616), 1, 0],
            [F(-625, 2308), F(-7060454, 254196983), 1]])
P = matrix([[F(577, 1024), 0, 0], [0, F(254196983, 37814272), 0],
            [0, 0, F(1555181999141, 2082381684736)]])
assert mul(mul(H, P), transpose(H)) == T
assert determinant(H) == 1 and all(P[i][i] > 0 for i in range(3))

D = matrix([[16, 0, 0], [0, F(1, 16), 0], [0, 0, 1]])
Di = matrix([[F(1, 16), 0, 0], [0, 16, 0], [0, 0, 1]])
A = power(D, 2)
Fdiag = matrix([[2, 0, 0], [0, F(1, 2), 0], [0, 0, 1]])
Ediag = matrix([[32, 0, 0], [0, F(1, 32), 0], [0, 0, 1]])
assert A == matrix([[256, 0, 0], [0, F(1, 256), 0], [0, 0, 1]])
assert mul(D, Di) == eye(3) == mul(Di, D)
assert power(Fdiag, 8) == A and power(Fdiag, 4) == D
assert power(Fdiag, 5) == Ediag and mul(Fdiag, D) == Ediag
powers = {k: power(T, k) for k in (2, 4, 8)}
B = mul(mul(D, powers[8]), D)
assert mul(mul(Di, B), Di) == powers[8]
printed_B = matrix([[17, -4, 0], [-4, 16385, -8192], [0, -8192, 4096]])
assert B != printed_B
assert B == transpose(B)
minors_B = [determinant([row[:k] for row in B[:k]]) for k in (1, 2, 3)]
assert all(x > 0 for x in minors_B)
N = mul(mul(mul(Ediag, T), D), B)
AB = mul(A, B)
v = [F(0), F(4, 5), F(-3, 5)]
assert sum(x * x for x in v) == 1
Nv = [sum((a * b for a, b in zip(row, v)), F(0)) for row in N]
trace = sum((B[i][i] for i in range(3)), F(0))
frob = sum((x * x for row in AB for x in row), F(0))
test = Nv[0]
margins = {'4^8_minus_traceB': 4**8 - trace,
           'testValue_minus_44000': test - 44000,
           '10500^2_minus_frobeniusSquaredAB': 10500**2 - frob,
           '11000_minus_10500': F(500)}
assert all(x > 0 for x in margins.values())

result = {
    'scope': 'Independent exact finite diagnostic; spectral powers and norms are not numerically evaluated. Supplementary diagnostic; the independent fresh Lean check establishes the proof obligations.',
    'method': 'R parsed directly from immutable Colbrook TeX; strict nearest-dyadic distances; generic naive products and permutation determinants; no imported verifier or float.',
    'source_R': encode(R), 'unique_nearest_rounding_distances_in_integer_units': encode(errors),
    'numerator_leading_minors': list(map(str, minors_M)),
    'LDL': {'factor': encode(H), 'pivots': [str(P[i][i]) for i in range(3)], 'factor_determinant': '1'},
    'powers': {str(k): encode(V) for k, V in powers.items()},
    'matrices': {name: encode(V) for name, V in [('D', D), ('A', A), ('T', T), ('B_adapted', B), ('N', N), ('AB', AB)]},
    'adapted_B_differs_from_printed_integer_B': True,
    'adapted_B_leading_minors': list(map(str, minors_B)),
    'vector': list(map(str, v)), 'vector_squared_norm': '1', 'Nv': list(map(str, Nv)),
    'traceB': str(trace), 'testValue': str(test), 'frobeniusSquaredAB': str(frob),
    'strict_margins': {name: str(value) for name, value in margins.items()},
    'normalizing_and_diagonal_power_certificates': 'PASS',
    'verdict': 'PASS'
}
(OUT / 'reconstruction.json').write_text(json.dumps(result, indent=2) + '\n')
print('PASS: unique source-R dyadic provenance, exact LDL/positivity, adapted eighth power, true unit vector and all strict finite certificate margins.')
for name, value in margins.items(): print(name + ': ' + str(value))
