"""Independent exact diagnostics of the frozen RA-08 constants and minorant.

This script imports no author checker and no numerical library. Its actual
Lean-literal parsing is restricted to this frozen file, and every comparison
uses fractions.Fraction. It is not a proof oracle or a general spectral proof.
"""
from pathlib import Path
from fractions import Fraction as Q
import ast
import hashlib
import json
import re

E = Path(__file__).resolve().parent
P = E.parents[1]
source = (P / 'NLA/RA08/Definitions.lean').read_text()
assert hashlib.sha256(source.encode()).hexdigest() == '8c2f3a76e44730b1f9d5bc8e896070c10868bae817d0c3d11ace22b3c7d94c41'


def body(name):
    match = re.search(r'^def ' + name + r'\b[\s\S]*?:=\s*([\s\S]*?)(?=\n(?:/--|def |end ))', source, re.M)
    assert match, name
    return match[1].strip()


def number(text, environment=None):
    environment = environment or {}

    def go(node):
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return Q(node.value)
        if isinstance(node, ast.Name):
            return environment[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -go(node.operand)
        if isinstance(node, ast.BinOp):
            a, b = go(node.left), go(node.right)
            if isinstance(node.op, ast.Add): return a + b
            if isinstance(node.op, ast.Sub): return a - b
            if isinstance(node.op, ast.Mult): return a * b
            if isinstance(node.op, ast.Div): return a / b
            if isinstance(node.op, ast.Pow):
                assert b.denominator == 1 and b >= 0
                return a ** b.numerator
        raise ValueError(ast.dump(node))

    return go(ast.parse(text.strip().replace('^', '**'), mode='eval').body)


def vector(name, environment=None):
    match = re.search(r'!\[([\s\S]*?)\]', body(name))
    assert match
    return [number(x, environment) for x in match[1].split(',')]


def scaled_matrix(name):
    text = body(name)
    scale = number(re.search(r'\(([^:]+):\s*ℝ\)\s*•', text)[1])
    matrix = re.search(r'!!\[([\s\S]*?)\]', text)[1]
    return [[scale * number(x) for x in row.split(',')] for row in matrix.split(';')]


def eye(n): return [[Q(i == j) for j in range(n)] for i in range(n)]
def transpose(a): return [list(x) for x in zip(*a)]
def mm(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), Q(0))
             for j in range(len(b[0]))] for i in range(len(a))]
def mv(a, x): return [sum((v * z for v, z in zip(row, x)), Q(0)) for row in a]
def dot(x, y): return sum((a * b for a, b in zip(x, y)), Q(0))
def shift(a, s): return [[a[i][j] - (s if i == j else 0) for j in range(len(a))] for i in range(len(a))]


def positive_ldl(a):
    n = len(a)
    assert transpose(a) == a
    l, d = eye(n), []
    for j in range(n):
        d.append(a[j][j] - sum((l[j][k] ** 2 * d[k] for k in range(j)), Q(0)))
        assert d[j] > 0
        for i in range(j + 1, n):
            l[i][j] = (a[i][j] - sum((l[i][k] * l[j][k] * d[k] for k in range(j)), Q(0))) / d[j]
    diagonal = [[d[i] if i == j else Q(0) for j in range(n)] for i in range(n)]
    assert mm(mm(l, diagonal), transpose(l)) == a
    return d


t, a, b = [number(body(name)) for name in ['witnessT', 'witnessA', 'witnessB']]
assert (t, a, b) == (Q(1, 65536), Q(17, 16), Q(127, 128))
coefficient, gap = number(body('minorantCoefficient')), number(body('witnessGap'))
u, f = scaled_matrix('witnessU'), scaled_matrix('witnessF')
assert u == [[Q(x, 9) for x in row] for row in [[1, 8], [8, 1], [-4, 4]]]
assert mm(transpose(u), u) == eye(2)
ee = mm(u, transpose(u))
expected_f = [[Q(0) for _ in range(6)] for _ in range(6)]
for i in range(3):
    for j in range(3): expected_f[i][j] = Q(64, 65) * ee[i][j]
    for j in range(2): expected_f[i][j + 3] = expected_f[j + 3][i] = Q(8, 65) * u[i][j]
for i in range(2): expected_f[i + 3][i + 3] = Q(1, 65)
expected_f[5][5] = 1
assert f == expected_f and transpose(f) == f and mm(f, f) == f
complement = [[Q(i == j) - f[i][j] for j in range(6)] for i in range(6)]
assert mm(complement, complement) == complement
diagonal = vector('witnessApproximation', {'witnessA': a, 'witnessB': b})
assert diagonal == [Q(1, 2), b, a, 0, 0, 0]
ahat = [[diagonal[i] if i == j else Q(0) for j in range(6)] for i in range(6)]
assert re.sub(r'\s+', '', body('witnessMatrix')) == 'witnessApproximation+witnessT•witnessF'
matrix = [[ahat[i][j] + t * f[i][j] for j in range(6)] for i in range(6)]
pivots = positive_ldl(matrix)
assert matrix[5][5] == t and all(matrix[i][5] == matrix[5][i] == 0 for i in range(5))
complement_indices = [0, 1, 3, 4, 5]
compression = [[matrix[i][j] for j in complement_indices] for i in complement_indices]
compression_difference = [[(b + t if i == j else 0) - compression[i][j]
                           for j in range(5)] for i in range(5)]
compression_pivots = positive_ldl(compression_difference)
assert matrix[2][2] >= a and b + t == Q(65025, 65536) < 1

w = vector('witnessVector')
assert w == [4, 3, 1, 0, 0, 0]
assert dot(w, w) == 26 and dot(w, mv(f, w)) == Q(14912, 585)


def apply_k(x):
    return mv(matrix, mv(shift(matrix, Q(1, 2)), mv(shift(matrix, b), x)))


kw = apply_k(w)
assert kw == vector('witnessKVector')
kw_squared = dot(kw, kw)
assert kw_squared == Q(1800760572753083906132034496291, 1019907849866242673982515970048000)
assert dot(w, apply_k(kw)) == kw_squared
image = vector('witnessApproximationImage', {'witnessB': b})
assert image == [Q(1, 2), b, 1, 0, 0, 0]
rayleigh = dot(w, mv(matrix, w)) - coefficient * dot(w, apply_k(kw)) - dot(w, [z * x for z, x in zip(image, w)])
assert gap == Q(78605142319958855341529309, 11432529876841442781954048000) > 0
assert rayleigh == 26 * t * (1 + gap)


def product(p, q):
    r = [Q(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q): r[i + j] += x * y
    return r


assert re.sub(r'\s+', '', body('minorantFunction')) == 'x-minorantCoefficient*x^2*(x-1/2)^2*(x-witnessB)^2'
polynomial = [Q(1)]
for factor in [[a, 1], [a, 1], [a - Q(1, 2), 1], [a - Q(1, 2), 1], [a - b, 1], [a - b, 1]]:
    polynomial = product(polynomial, factor)
shifted = [coefficient * x for x in polynomial]
shifted[0] += 1 - a
shifted[1] -= 1
assert shifted == [Q(0), Q(19, 17), Q(537952, 23409), Q(2069504, 23409),
                   Q(288428032, 1896129), Q(227540992, 1896129), Q(67108864, 1896129)]
assert all(x > 0 for x in shifted[1:])

result = {
    'verdict': 'PASS: independent exact finite diagnostics; not a Lean proof or numerical oracle',
    'actual_Definitions_sha256': hashlib.sha256(source.encode()).hexdigest(),
    'source_U_and_F_match': True, 'projection_and_complement_identities': True,
    'actual_matrix_positive_LDL_pivots': [str(x) for x in pivots],
    'complement_compression_upper_difference_positive_LDL_pivots': [str(x) for x in compression_pivots],
    'isolated_sixth_coordinate_eigenvalue': str(t),
    'omitted_coordinate_diagonal_at_least_a': True,
    'b_plus_t': str(b + t), 'w_squared': str(dot(w, w)),
    'w_F_w': str(dot(w, mv(f, w))), 'three_product_Kw': [str(x) for x in kw],
    'Kw_squared': str(kw_squared), 'actual_double_K_application_agrees_with_squared_norm': True,
    'minorant_Rayleigh': str(rayleigh), 'exact_relative_gap': str(gap),
    'shifted_one_minus_minorant_coefficients': [str(x) for x in shifted],
    'universal_obligations_not_discharged_by_diagnostic': [
        'ordered eigenbasis existence and all-choice truncation semantics',
        'actual fourth eigenvalue, Euclidean norms and spectrum containment',
        'generic and polynomial genuine CFC agreement and PSD order',
        'kernel LeanCert sign and full original conjecture negation'],
}
(E / 'exact-checks.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
