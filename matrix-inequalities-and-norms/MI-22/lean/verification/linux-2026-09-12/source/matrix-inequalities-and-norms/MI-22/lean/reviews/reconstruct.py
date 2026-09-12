"""Exact statement-stage reconstruction of the adapted MI-22 witness.

All decisive checks use Python's standard-library Fraction and integer
arithmetic. This is a finite diagnostic, not a Lean proof certificate.
No submitted numerical verifier or floating-point eigensolver is imported.
The source's R is parsed only to document the witness-selection adaptation.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import permutations
from functools import reduce
import hashlib
import json
import re

PROJECT = Path(__file__).resolve().parents[1]
SOURCE = PROJECT.parent / 'solution.tex'
TEXT = SOURCE.read_text()
MATCH = re.search(r'R=10\^\{-15\}\\begin\{pmatrix\}(.*?)\\end\{pmatrix\}', TEXT, re.S)
assert MATCH is not None
R = [F(int(x), 10**15) for x in re.findall(r'-?\d+', MATCH.group(1))]
assert len(R) == 9
K = [[4616, -39, -1250], [-39, 55069, -1519], [-1250, -1519, 6499]]
assert [round(x * 8192) for x in R] == [x for row in K for x in row]


def matrix(values):
    return [[F(x) for x in row] for row in values]


def diagonal(values):
    return [[F(values[i]) if i == j else F(0) for j in range(3)] for i in range(3)]


def transpose(A):
    return [list(row) for row in zip(*A)]


def mul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(3)) for j in range(3)]
            for i in range(3)]


def determinant(A):
    n = len(A)
    return sum((-1)**sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n)) *
               reduce(lambda x, y: x * y, [A[i][p[i]] for i in range(n)], F(1))
               for p in permutations(range(n)))


def frobenius_sq(A):
    return sum(x * x for row in A for x in row)


def rows(A):
    return [[str(x) for x in row] for row in A]


T = [[F(x, 8192) for x in row] for row in K]
D = diagonal([16, F(1, 16), 1])
DI = diagonal([F(1, 16), 16, 1])
A = mul(D, D)
ONE_EIGHTH = diagonal([2, F(1, 2), 1])
FIVE_EIGHTHS = diagonal([32, F(1, 32), 1])
assert mul(ONE_EIGHTH, D) == FIVE_EIGHTHS
assert A == diagonal([256, F(1, 256), 1])
assert mul(D, DI) == diagonal([1, 1, 1]) == mul(DI, D)
LDL = matrix([[1, 0, 0], [F(-39, 4616), 1, 0],
              [F(-625, 2308), F(-7060454, 254196983), 1]])
PIVOTS = [F(577, 1024), F(254196983, 37814272), F(1555181999141, 2082381684736)]
assert mul(mul(LDL, diagonal(PIVOTS)), transpose(LDL)) == T
assert all(x > 0 for x in PIVOTS)
assert determinant(LDL) == 1
K_MINORS = [determinant([row[:k] for row in matrix(K)[:k]]) for k in [1, 2, 3]]
assert K_MINORS == [4616, 254196983, 1555181999141]
assert all(x > 0 for x in K_MINORS)
assert T == transpose(T)
T2 = mul(T, T)
T4 = mul(T2, T2)
T8 = mul(T4, T4)
B = mul(mul(D, T8), D)
assert B == transpose(B)
assert mul(mul(DI, B), DI) == T8
B_MINORS = [determinant([row[:k] for row in B[:k]]) for k in [1, 2, 3]]
assert all(x > 0 for x in B_MINORS)
N = mul(mul(mul(FIVE_EIGHTHS, T), D), B)
AB = mul(A, B)
V = [F(0), F(4, 5), F(-3, 5)]
assert sum(x * x for x in V) == 1
NV = [sum(N[i][j] * V[j] for j in range(3)) for i in range(3)]
Q = NV[0]
TRACE_B = sum(B[i][i] for i in range(3))
FROB_AB = frobenius_sq(AB)
assert TRACE_B < 4**8
assert 44000 < Q
assert FROB_AB < 10500**2
assert 44000 == 4 * 11000
assert 10500 < 11000

RESULT = {
    'status': 'PASS',
    'scope': 'Exact finite diagnostics for a new rational adaptation; no Lean proof or spectral oracle',
    'original_source_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    'source_R': rows([R[i:i+3] for i in range(0, 9, 3)]),
    'adaptation': 'T is source R rounded exactly to multiples of 1/8192; B is redefined as D T^8 D',
    'K': K, 'T': rows(T), 'D': rows(D), 'D_inverse': rows(DI), 'A': rows(A),
    'LDL_factor': rows(LDL), 'positive_T_pivots': [str(x) for x in PIVOTS],
    'positive_K_leading_minors': [str(x) for x in K_MINORS],
    'T2': rows(T2), 'T4': rows(T4), 'T8': rows(T8), 'B': rows(B),
    'positive_B_leading_minors': [str(x) for x in B_MINORS],
    'N': rows(N), 'AB': rows(AB), 'unit_vector': [str(x) for x in V],
    'N_times_vector': [str(x) for x in NV],
    'trace_B': str(TRACE_B), 'trace_bound_gap': str(F(4**8) - TRACE_B),
    'test_value': str(Q), 'test_value_gap': str(Q - 44000),
    'frobenius_squared_AB': str(FROB_AB),
    'frobenius_squared_bound_gap': str(F(10500**2) - FROB_AB),
    'strict_comparison': '10500 < 11000; retained kernel LeanCert point check planned',
    'analytic_obligations_not_assumed': [
        'Actual CFC powers give weightedMean(A,B,1/8)=D T D',
        'Y is actual B^(1/8), is positive definite, and satisfies Y^8=B',
        'L Y=N with the original noncommuting factor order',
        'trace_B<4^8 implies actual Euclidean operatorNorm(Y)<4',
        'Actual matrix action on the Euclidean unit vector gives the operator lower bound',
        'Actual first singular value equals Euclidean operator norm',
        'Strict first singular-value reversal refutes all-parameter full log-majorization']}
(PROJECT / 'reviews/reconstruction.json').write_text(json.dumps(RESULT, indent=2) + '\n')
print('PASS: source adaptation, exact LDL/positivity, repeated-squaring data, trace, test vector, '
      'test value, Frobenius bound, and strict scalar gap; all arithmetic exact.')
