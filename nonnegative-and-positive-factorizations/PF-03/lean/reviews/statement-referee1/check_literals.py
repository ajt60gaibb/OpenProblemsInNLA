"""Independent read-only parser audit of PF03 Lean rational literals.

Does not import the source generator, evaluate Lean, or certify its theorems.
"""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import re

D = Path(__file__).resolve().parents[2]
P = D / 'development/PF03'
data_dir = D / 'recovered-statements/next-statements/PF03-full-20260918/canonical/references/holden-pf03-2026-09-13/data'
source = P / 'NLA/PF03/RawData.lean'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
seed = json.loads((data_dir / 'exact_algebraic_certificate.json').read_text())
cone = json.loads((data_dir / 'rational_cone_certificate.json').read_text())
expected = {
    'coefficientMatrices': [[[entry[0] for entry in row] for row in mat]
                            for mat in seed['coefficient_matrices']],
    'orthogonalMatrix': seed['orthogonal_matrix'],
    'quadraticMatrix': seed['Q'],
    'restrictedGram': seed['restricted_gram'],
    'triangle': cone['coefficient_triangle'],
    'barycentricCoefficients': cone['barycentric_coefficients'],
    'generators': cone['generators'],
    'positiveSlice': cone['positive_slice_functional'],
}
assert all(Fraction(e[1]) == Fraction(e[2]) == 0
           for mat in seed['coefficient_matrices'] for row in mat for e in row)

def rationals(x):
    return [rationals(v) for v in x] if isinstance(x, list) else Fraction(x)

def count_leaves(x):
    return sum(map(count_leaves, x)) if isinstance(x, list) else 1

def parse_literal(expr):
    tokens = re.findall(r'!\[|\]|,|\(|\)|/|-?\d+', expr)
    assert ''.join(tokens) == re.sub(r'\s+', '', expr), 'Non-literal syntax'
    cursor = 0

    def read():
        nonlocal cursor
        token = tokens[cursor]
        cursor += 1
        if token == '![':
            values = [read()]
            while tokens[cursor] == ',':
                cursor += 1
                values.append(read())
            assert tokens[cursor] == ']'
            cursor += 1
            return values
        if token == '(':
            value = read()
            if tokens[cursor] == '/':
                cursor += 1
                value /= read()
            assert tokens[cursor] == ')'
            cursor += 1
            return value
        return Fraction(int(token))

    result = read()
    assert cursor == len(tokens)
    return result

blocks = re.findall(r'^def (\w+) :[^\n]*:=\n(.*?)(?=^def |^end RawData)',
                    source.read_text(), re.M | re.S)
assert [name for name, _ in blocks] == list(expected)
checks = []
for name, expr in blocks:
    value = parse_literal(expr)
    assert value == rationals(expected[name]), name
    checks.append({'declaration': name, 'rational_entries': count_leaves(value), 'match': True})
ell = Fraction(12599210498948731647672106072782283505702, 10 ** 40)
upp = Fraction(12599210498948731647672106072782283505703, 10 ** 40)
assert 0 < ell and ell ** 3 < 2 < upp ** 3
mins = []
for i in range(7):
    C = [[Fraction(seed['coefficient_matrices'][k][r][i][0]) for k in range(3)]
         for r in range(7)]
    minor = C[0][0] * C[1][1] - C[0][1] * C[1][0]
    assert minor != 0
    mins.append({'column': i, 'rows': [0, 1], 'coefficient_columns': [0, 1], 'nonzero': True})
print(json.dumps({
    'scope': 'Independent literal/source feasibility audit only; not Lean or Comparator verification',
    'source_sha256': sha(source), 'script_sha256': sha(Path(__file__)),
    'primary_sha256': {p.name: sha(p) for p in [data_dir / 'exact_algebraic_certificate.json',
                                              data_dir / 'rational_cone_certificate.json']},
    'literal_checks': checks, 'total_rational_entries': sum(c['rational_entries'] for c in checks),
    'root_endpoint_strict_rational_inequalities': True, 'fixed_minor_checks': mins,
    'Lean_executed_by_this_script': False,
}, indent=2))
