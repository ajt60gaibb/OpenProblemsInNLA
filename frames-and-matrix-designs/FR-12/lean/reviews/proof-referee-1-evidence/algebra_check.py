"""Independent exact symbolic diagnostics for the completed growth argument.
No author checker is imported; these checks supplement the universal Lean proof.
"""
from fractions import Fraction
from math import factorial
from pathlib import Path
import json

# Bivariate rational polynomials with coefficient keys (degree_C, degree_d).
def add(*terms):
    out = {}
    for term in terms:
        for powers, coefficient in term.items():
            out[powers] = out.get(powers, Fraction(0)) + coefficient
    return {powers: coefficient for powers, coefficient in out.items() if coefficient}

def scale(a, term):
    return {powers: Fraction(a) * coefficient for powers, coefficient in term.items() if a * coefficient}

def mul(a, b):
    out = {}
    for (ca, da), va in a.items():
        for (cb, db), vb in b.items():
            powers = (ca + cb, da + db)
            out[powers] = out.get(powers, Fraction(0)) + va * vb
    return {powers: coefficient for powers, coefficient in out.items() if coefficient}

one = {(0, 0): Fraction(1)}
C = {(1, 0): Fraction(1)}
d = {(0, 1): Fraction(1)}
k = add(scale(16, C), scale(2, one), d)
gap = add(scale(Fraction(1, 8), mul(k, add(k, one))),
          scale(-1, mul(C, add(k, scale(2, one)))))
expected_gap = {(2, 0): Fraction(16), (1, 0): Fraction(6), (1, 1): Fraction(3),
                (0, 2): Fraction(1, 8), (0, 1): Fraction(5, 8), (0, 0): Fraction(3, 4)}
assert gap == expected_gap
assert all(coefficient > 0 for coefficient in gap.values())

# Divide the induction exponents by the positive q=2^(k+1).
x = d
factorial_exponent = add(x, one)
old_exponent = scale(Fraction(1, 4), mul(x, add(x, one)))
next_exponent = scale(Fraction(1, 2), mul(add(x, one), add(x, scale(2, one))))
assert add(factorial_exponent, scale(2, old_exponent)) == next_exponent
assert next_exponent == {(0, 2): Fraction(1, 2), (0, 1): Fraction(3, 2), (0, 0): Fraction(1)}

factorial_cases = []
for r in range(13):
    assert r ** r <= factorial(2 * r)
    factorial_cases.append({'r': r, 'lhs': r ** r, 'rhs': factorial(2 * r)})

def encoded(poly):
    return [{'degree_C': a, 'degree_d': b, 'coefficient': str(c)}
            for (a, b), c in sorted(poly.items())]

result = {
    'result': 'PASS: exact symbolic coefficient identities and small boundary diagnostics',
    'scope': 'Supplementary independent rational algebra; universal validity is proved by the actual Lean proof',
    'archimedean_substitution': 'k=16*C+2+d, d>0, C>0',
    'strict_gap': 'k*(k+1)/8 - C*(k+2)',
    'strict_gap_coefficients': encoded(gap),
    'constant_positive_term': '3/4',
    'induction_exponents_divided_by_q': 'q=2^(k+1)>0; (k+1) + 2*k*(k+1)/4 = (k+1)*(k+2)/2',
    'induction_coefficients': encoded(next_exponent),
    'half_factorial_boundary_cases': factorial_cases,
    'no_interval_or_large_matrix_enumeration': True,
}
Path(__file__).with_name('algebra-check.json').write_text(json.dumps(result, indent=2) + '\n')
print('PASS: exact induction and all-constant exponent algebra; 13 small factorial boundary cases')
