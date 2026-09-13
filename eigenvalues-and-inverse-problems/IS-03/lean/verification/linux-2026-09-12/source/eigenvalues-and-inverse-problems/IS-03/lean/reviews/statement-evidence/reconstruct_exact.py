"""Independent rational diagnostics parsed from the actual IS03 definitions.

Sparse determinant expansion visits only supported permutations. These finite
checks are not a universal trace theorem or a Lean proof certificate.
"""
from pathlib import Path
from fractions import Fraction as F
import ast
import hashlib
import json
import re

P = Path(__file__).resolve().parents[2]
E = Path(__file__).resolve().parent
source = P / 'NLA/IS03/Definitions.lean'
text = source.read_text()


def add(a, b):
    c = dict(a)
    for k, v in b.items():
        c[k] = c.get(k, F(0)) + v
    return {k: v for k, v in c.items() if v}


def scale(a, c):
    return {k: v * c for k, v in a.items() if v * c}


def mul(a, b):
    c = {}
    for i, u in a.items():
        for j, v in b.items():
            c[i + j] = c.get(i + j, F(0)) + u * v
    return {k: v for k, v in c.items() if v}


def power(a, n):
    c = {0: F(1)}
    for _ in range(n):
        c = mul(c, a)
    return c


def constant(p):
    assert set(p) <= {0}, p
    return p.get(0, F(0))


def parse_poly(node):
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return {0: F(node.value)} if node.value else {}
    if isinstance(node, ast.Name) and node.id == 'X':
        return {1: F(1)}
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return scale(parse_poly(node.operand), -1)
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'C':
        assert len(node.args) == 1 and not node.keywords
        p = parse_poly(node.args[0])
        constant(p)
        return p
    if isinstance(node, ast.BinOp):
        a, b = parse_poly(node.left), parse_poly(node.right)
        if isinstance(node.op, ast.Add):
            return add(a, b)
        if isinstance(node.op, ast.Sub):
            return add(a, scale(b, -1))
        if isinstance(node.op, ast.Mult):
            return mul(a, b)
        if isinstance(node.op, ast.Div):
            return scale(a, 1 / constant(b))
        if isinstance(node.op, ast.Pow):
            n = constant(b)
            assert n.denominator == 1 and n >= 0
            return power(a, int(n))
    raise ValueError(ast.dump(node))


def polynomial(name):
    body = re.search(r'def ' + name + r'\s*: ℝ\[X\] :=\s*(.*?)\n\n', text, re.S).group(1)
    expr = ' '.join(body.split()).replace('^', '**')
    return parse_poly(ast.parse(expr, mode='eval').body)


def matrix_literal(name):
    body = re.search(r'def ' + name + r'.*?!!\[(.*?)\]', text, re.S).group(1)
    return [[F(x.strip()) for x in row.split(',')] for row in body.split(';')]


def det_charpoly(a):
    n = len(a)
    entries = [[add({1: F(1)} if i == j else {}, {0: -a[i][j]} if a[i][j] else {})
                for j in range(n)] for i in range(n)]
    total = {}
    supported = 0

    def visit(columns, product, sign):
        nonlocal total, supported
        i = len(columns)
        if i == n:
            total = add(total, scale(product, sign))
            supported += 1
            return
        for j in range(n):
            if j not in columns and entries[i][j]:
                parity = sum(c > j for c in columns) % 2
                visit(columns + [j], mul(product, entries[i][j]), sign * (-1 if parity else 1))

    visit([], {0: F(1)}, 1)
    return total, supported


def matmul(a, b):
    n = len(a)
    return [[sum((a[i][k] * b[k][j] for k in range(n)), F(0))
             for j in range(n)] for i in range(n)]


def coefficients(p):
    return [str(p.get(k, F(0))) for k in range(max(p, default=0) + 1)]


a = matrix_literal('witnessMatrix')
assert len(a) == 7 and all(len(row) == 7 for row in a)
assert all(x >= 0 for row in a for x in row)
assert sum(a[i][i] for i in range(7)) == F(1, 2)
p = polynomial('witnessPolynomial')
q = polynomial('derivativePolynomial')
det_p, supported_p = det_charpoly(a)
assert det_p == p
q_from_p = {k - 1: k * v / 7 for k, v in p.items() if k}
assert q == q_from_p and max(q) == 6 and q[6] == 1
c = [q.get(6 - j, F(0)) for j in range(1, 7)]
newton = []
for k in range(1, 8):
    mixed = sum((c[j - 1] * newton[k - j - 1] for j in range(1, min(k, 7))), F(0))
    newton.append(-mixed - (k * c[k - 1] if k <= 6 else 0))

moment_body = re.search(r'def traceMoments.*?!\[(.*?)\]', text, re.S).group(1)
declared_moments = [F(s.strip()) for s in moment_body.split(',')]
assert newton == declared_moments
companion = [[F(0) for _ in range(6)] for _ in range(6)]
for i in range(1, 6):
    companion[i][i - 1] = F(1)
for i in range(6):
    companion[i][5] = -q.get(i, F(0))
det_q, supported_q = det_charpoly(companion)
assert det_q == q
power_matrix = [[F(i == j) for j in range(6)] for i in range(6)]
companion_traces = []
for k in range(1, 8):
    power_matrix = matmul(power_matrix, companion)
    companion_traces.append(sum(power_matrix[i][i] for i in range(6)))
assert companion_traces == newton
weighted = [3 * newton[5], 5 * newton[4], -2 * newton[3],
            3 * newton[2], -newton[1], -newton[0]]
numerators = [x * 7**6 for x in weighted]
assert all(x.denominator == 1 for x in numerators)
assert numerators == [659298, 182455, -659638, 49392, -189679, -50421]
assert sum(weighted) == 7 * newton[6] and newton[6] == F(-8593, 823543) < 0
out = {
    'verdict': 'PASS: exact finite rational diagnostics only',
    'source': str(source), 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'method': 'Parse actual Lean literals; sparse permutation determinant; formal polynomial differentiation; Newton recurrence; independently multiply companion matrix powers.',
    'scope_limit': 'The companion is one diagnostic matrix, not a nonnegative realization. No finite computation proves the target for all B. The universal matrix trace bridge remains a separate Lean obligation.',
    'witness_order': 7, 'witness_trace': '1/2', 'witness_entrywise_nonnegative': True,
    'witness_supported_determinant_permutations': supported_p,
    'p_coefficients_ascending': coefficients(p), 'q_coefficients_ascending': coefficients(q),
    'q_monic': True, 'q_degree': 6, 'newton_moments_1_to_7': list(map(str, newton)),
    'companion_supported_determinant_permutations': supported_q,
    'companion_trace_moments_1_to_7': list(map(str, companion_traces)),
    'last_recurrence_term_numerators_over_7_to_6': list(map(int, numerators)),
    'planned_LeanCert_input': '(-8593 / 823543 : ℝ) < 0',
    'LeanCert_execution_claimed': False}
(E / 'exact-checks.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
