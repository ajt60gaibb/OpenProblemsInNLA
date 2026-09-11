"""Independent standard-library audit of the seven-product degree-42 certificate.

Polynomials and directional derivatives are evaluated over the integers, without
coefficient truncation or modular arithmetic. A 43-by-43 minor is then computed
by fraction-free Bareiss elimination and compared with the finite-field result.
No NumPy or symbolic-algebra package is needed. This proves only complex dense
coverage through degree 42; it proves neither maximality nor real dense coverage.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import json
from math import isqrt

Poly = list[int]
Dual = tuple[Poly, Poly]

def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)

def add(a: Poly, b: Poly) -> Poly:
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a): out[i] += x
    for i, x in enumerate(b): out[i] += x
    while len(out) > 1 and out[-1] == 0: out.pop()
    return out

def mul(a: Poly, b: Poly) -> Poly:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): out[i+j] += x*y
    while len(out) > 1 and out[-1] == 0: out.pop()
    return out

def dadd(*args: Dual) -> Dual:
    value, derivative = [0], [0]
    for v, d in args:
        value = add(value, v)
        derivative = add(derivative, d)
    return value, derivative

def dmul(a: Dual, b: Dual) -> Dual:
    return mul(a[0], b[0]), add(mul(a[1], b[0]), mul(a[0], b[1]))

def polynomial_and_derivative(pars: dict[str, int], direction: str | None) -> Dual:
    def a(name: str) -> Dual:
        return [pars[name]], [int(name == direction)]
    def scaled(name: str, q: Dual) -> Dual:
        return dmul(a(name), q)
    q0: Dual = ([1], [0])
    x: Dual = ([0, 1], [0])
    # Written directly, separately from the discovery code's sparse dictionaries.
    q2 = dmul(x, x)
    q3 = dmul(dadd(scaled('a22', x), q2),
              dadd(scaled('b22', x), q2))
    q4 = dmul(dadd(scaled('a32', x), q3),
              dadd(scaled('b32', x), q2))
    q5 = dmul(dadd(scaled('a42', x), scaled('a43', q2), scaled('a44', q3), q4),
              dadd(scaled('b42', x), scaled('b43', q2), q3))
    q6 = dmul(dadd(scaled('a52', x), scaled('a54', q3), scaled('a55', q4), q5),
              dadd(scaled('b52', x), scaled('b53', q2), scaled('b54', q3), q4))
    q7 = dmul(dadd(scaled('a62', x), scaled('a63', q2), scaled('a64', q3),
                   scaled('a65', q4), scaled('a66', q5), q6),
              dadd(scaled('b62', x), scaled('b63', q2), scaled('b64', q3),
                   scaled('b65', q4), q5))
    q8 = dmul(dadd(scaled('a72', x), scaled('a73', q2), scaled('a74', q3),
                   scaled('a75', q4), scaled('a76', q5), scaled('a77', q6), q7),
              dadd(scaled('b72', x), scaled('b73', q2), scaled('b74', q3),
                   scaled('b75', q4), scaled('b76', q5), q6))
    return dadd(*(scaled(f'c{i}', q) for i, q in enumerate((q0, x, q2, q3, q4, q5, q6, q7, q8))))

NAMES = ('a22 b22 a32 b32 a42 a43 a44 b42 b43 a52 a54 a55 b52 b53 b54 '
         'a62 a63 a64 a65 a66 b62 b63 b64 b65 a72 a73 a74 a75 a76 a77 '
         'b72 b73 b74 b75 b76 c0 c1 c2 c3 c4 c5 c6 c7 c8').split()

def determinant_bareiss(matrix: list[list[int]]) -> int:
    n = len(matrix)
    require(n > 0 and all(len(r) == n for r in matrix), 'Not a nonempty square matrix')
    a = [r[:] for r in matrix]
    previous, sign = 1, 1
    for k in range(n-1):
        pivot_row = next((i for i in range(k, n) if a[i][k]), None)
        if pivot_row is None: return 0
        if pivot_row != k:
            a[k], a[pivot_row] = a[pivot_row], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                numerator = pivot*a[i][j] - a[i][k]*a[k][j]
                quotient, remainder = divmod(numerator, previous)
                require(remainder == 0, 'Non-exact Bareiss division')
                a[i][j] = quotient
            a[i][k] = 0
        previous = pivot
    return sign*a[-1][-1]

def audit(path: Path) -> dict:
    cert = json.loads(path.read_text())
    require(cert['parameter_names'] == NAMES, 'Unexpected parameter order')
    pars = cert['parameters']
    require(set(pars) == set(NAMES), 'Unexpected parameter set')
    require(all(type(v) is int for v in pars.values()), 'Noninteger parameter')
    require(cert['degree'] == 42 and cert['multiplications'] == 7, 'Unexpected degree or operation count')
    coeff, zero_derivative = polynomial_and_derivative(pars, None)
    require(zero_derivative == [0], 'Invalid zero direction')
    require(len(coeff) == 43, 'Polynomial does not have exact degree 42')
    columns = []
    for name in NAMES:
        value, derivative = polynomial_and_derivative(pars, name)
        require(value == coeff, 'Directional evaluation changed value')
        require(len(derivative) <= 43, 'Derivative degree exceeds 42')
        columns.append(derivative + [0]*(43-len(derivative)))
    selected = cert['minor_column_indices']
    require(len(selected) == 43 and len(set(selected)) == 43, 'Invalid minor size')
    require(all(type(j) is int and 0 <= j < 44 for j in selected), 'Invalid minor index')
    require(cert['minor_parameters'] == [NAMES[j] for j in selected], 'Minor names disagree')
    matrix = [[columns[j][i] for j in selected] for i in range(43)]
    det = determinant_bareiss(matrix)
    p = cert['prime']
    require(type(p) is int and p >= 2 and all(p % d for d in range(2, isqrt(p)+1)), 'Nonprime modulus')
    require([v % p for v in coeff] == cert['coefficient_vector_mod_prime'], 'Coefficient vectors disagree')
    require(det != 0 and det % p == cert['minor_determinant_mod_prime'], 'Determinant checks failed')
    return {'certificate': path.name, 'arithmetic': 'untruncated integer polynomials and fraction-free integer determinant',
            'degree': 42, 'jacobian_shape': [43, 44], 'minor_shape': [43, 43],
            'integer_minor_determinant': str(det), 'prime': p, 'determinant_mod_prime': det % p,
            'exact_coefficient_vector': [str(v) for v in coeff], 'passed': True}

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--verify', action='store_true', help='Compare regenerated audit with --output')
    args = parser.parse_args()
    result = audit(args.certificate)
    if args.verify:
        require(args.output is not None, '--verify needs --output')
        require(json.loads(args.output.read_text()) == result, 'Stored independent audit differs')
    elif args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(f"PASS: exact integer minor is nonzero; its residue is {result['determinant_mod_prime']} modulo {result['prime']}.")
    print('The determinant has', len(result['integer_minor_determinant'].lstrip('-')), 'decimal digits.')

if __name__ == '__main__':
    main()
