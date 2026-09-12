#!/usr/bin/env python3
"""Exact supplementary checks; not a replacement for the all-m analytic audit.

The boundary determinant identities are algebraic in a conjugation-invariant
stable-root list and a unit-modulus oscillatory root. Rational test lists avoid
numerical trigonometry. They need not solve the Toeplitz characteristic equation;
the characteristic-root and uniform-error arguments are checked in the report.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations
from math import comb, factorial
from pathlib import Path
import argparse
import hashlib
import json

EXPECTED_SOURCE = '98eb74a858ad3d2bf5fd0055a92d9c96b9a5e4f4f531972cd429462acb2b44f5'


@dataclass(frozen=True)
class QI:
    a: F = F(0)
    b: F = F(0)

    @staticmethod
    def of(x):
        return x if isinstance(x, QI) else QI(F(x))

    def __add__(self, x):
        x = self.of(x)
        return QI(self.a + x.a, self.b + x.b)

    __radd__ = __add__

    def __neg__(self):
        return QI(-self.a, -self.b)

    def __sub__(self, x):
        return self + -self.of(x)

    def __rsub__(self, x):
        return self.of(x) + -self

    def __mul__(self, x):
        x = self.of(x)
        return QI(self.a*x.a - self.b*x.b, self.a*x.b + self.b*x.a)

    __rmul__ = __mul__

    def conjugate(self):
        return QI(self.a, -self.b)

    def inverse(self):
        s = self.a*self.a + self.b*self.b
        assert s
        return QI(self.a/s, -self.b/s)

    def __truediv__(self, x):
        return self*self.of(x).inverse()

    def __pow__(self, k):
        if k < 0:
            return self.inverse()**(-k)
        p, x = QI(F(1)), self
        while k:
            if k % 2:
                p = p*x
            x = x*x
            k //= 2
        return p


ZERO, ONE = QI(), QI(F(1))


def product(xs):
    p = ONE
    for x in xs:
        p = p*x
    return p


def vandermonde(xs):
    return product(xs[j]-xs[i] for i in range(len(xs))
                   for j in range(i+1, len(xs)))


def determinant(a):
    a = [[QI.of(x) for x in row] for row in a]
    d = ONE
    for k in range(len(a)):
        pivot = next((j for j in range(k, len(a)) if a[j][k] != ZERO), None)
        if pivot is None:
            return ZERO
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            d = -d
        p = a[k][k]
        d = d*p
        for j in range(k+1, len(a)):
            t = a[j][k]/p
            for ell in range(k+1, len(a)):
                a[j][ell] = a[j][ell] - t*a[k][ell]
            a[j][k] = ZERO
    return d


def check_boundary(m, n):
    r = [QI(F(j, 2*m+3)) for j in range(1, m)]
    o = [x.inverse() for x in r]
    z = QI(F(3, 5), F(4, 5))
    roots = r + [z, z.inverse()] + o
    q = product(o)
    f = product(ONE - x*z.inverse() for x in r)
    rows = list(range(m)) + list(range(n+m, n+2*m))
    direct = determinant([[w**k for w in roots] for k in rows])
    plus = (m-1,) + tuple(range(m+1, 2*m))
    minus = (m,) + tuple(range(m+1, 2*m))
    row_sum = m*(3*m+1)//2
    terms = {}
    coeff = {}
    for s in combinations(range(2*m), m):
        selected = [roots[i] for i in s]
        complement = [roots[i] for i in range(2*m) if i not in s]
        sign = (-1)**(row_sum+sum(i+1 for i in s))
        coeff[s] = sign*vandermonde(selected)*vandermonde(complement)
        terms[s] = coeff[s]*product(selected)**(n+m)
    assert direct == sum(terms.values(), ZERO)
    sigma = (-1)**(row_sum+sum(i+1 for i in plus))
    v = vandermonde(r)*vandermonde(o)
    assert coeff[plus] == sigma*v*q*z**(-(m-1))*f.conjugate()**2
    assert coeff[minus] == -sigma*v*q*z**(m-1)*f**2
    dominant = sigma*v*q**(n+m+1)*(z**(n+1)*f.conjugate()**2
                                          - z**(-(n+1))*f**2)
    assert terms[plus]+terms[minus] == dominant
    assert direct.conjugate() == -direct
    return {'m': m, 'n': n, 'laplace_sum': True,
            'two_leading_coefficients': True, 'phase_orientation': True,
            'imaginary_determinant': True}


def check_trace_constant(m):
    integral = sum((F((-1)**k*comb(2*m-1, k), 2*m+k)
                    for k in range(2*m)), F(0))
    actual = integral/((2*m-1)*factorial(m-1)**2)
    claimed = F(factorial(2*m-1)**2,
                factorial(4*m-1)*(2*m-1)*factorial(m-1)**2)
    assert actual == claimed
    return {'m': m, 'constant': str(actual), 'beta_integral_identity': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path,
                        default=Path(__file__).with_name('reviewed-candidate.md'))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    data = args.source.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    assert digest == EXPECTED_SOURCE, 'The reviewed source hash changed.'
    result = {
        'verdict': 'PASS',
        'source_sha256': digest,
        'source_bytes': len(data),
        'arithmetic': 'Exact Gaussian rational arithmetic and integer/Fraction sums',
        'boundary_cases': [check_boundary(m, n) for m in range(2, 7) for n in (1, 5)],
        'trace_cases': [check_trace_constant(m) for m in range(1, 13)],
        'limitations': [
            'Finite algebra checks are supplementary and do not prove the all-m theorem.',
            'The test stable-root lists validate algebra, not the Toeplitz root equation.',
            'Uniform analytic estimates, eigenvalue indexing, the external kernel theorem, '
            'and the irrationality contradiction are independently reviewed in the report.'
        ]
    }
    text = json.dumps(result, indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
