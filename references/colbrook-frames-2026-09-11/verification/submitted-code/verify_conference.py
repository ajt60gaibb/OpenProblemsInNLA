#!/usr/bin/env python3
"""Integer-only verification of Hermitian conference existence certificates.

The proof is a contraction mapping on a rational Cayley-coordinate box.
Every interval operation is outward-rounded using Python integer arithmetic.
No floating-point arithmetic is used to decide whether a certificate passes.
Float conversions in the final report are descriptive only.

Usage:
    python verify_conference.py conference_certificate_d77.json
    python verify_conference.py conference_certificate_d*.json --out report.json
"""
from __future__ import annotations
import argparse
import json
import time
from fractions import Fraction
from pathlib import Path
from typing import Tuple

Interval = Tuple[int, int]
ComplexInterval = Tuple[Interval, Interval]


class FixedIntervals:
    def __init__(self, bits: int):
        if not isinstance(bits, int) or not 80 <= bits <= 1024:
            raise ValueError('verification_bits must be an integer in [80,1024].')
        self.S = 1 << bits
        self.zero = (0, 0)
        self.one = (self.S, self.S)
        self.czero = (self.zero, self.zero)

    def rat(self, n: int, d: int = 1) -> Interval:
        if d <= 0:
            raise ValueError('A rational denominator must be positive.')
        v = n*self.S
        return v//d, -((-v)//d)

    @staticmethod
    def add(a: Interval, b: Interval) -> Interval:
        return a[0]+b[0], a[1]+b[1]

    @staticmethod
    def neg(a: Interval) -> Interval:
        return -a[1], -a[0]

    def sub(self, a: Interval, b: Interval) -> Interval:
        return self.add(a, self.neg(b))

    @staticmethod
    def scale(a: Interval, k: int) -> Interval:
        return (k*a[0], k*a[1]) if k >= 0 else (k*a[1], k*a[0])

    def mul(self, a: Interval, b: Interval) -> Interval:
        v = (a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1])
        lo, hi = min(v), max(v)
        return lo//self.S, -((-hi)//self.S)

    def cadd(self, a: ComplexInterval, b: ComplexInterval) -> ComplexInterval:
        return self.add(a[0], b[0]), self.add(a[1], b[1])

    def conj(self, a: ComplexInterval) -> ComplexInterval:
        return a[0], self.neg(a[1])

    def cmul(self, a: ComplexInterval, b: ComplexInterval) -> ComplexInterval:
        return (self.sub(self.mul(a[0], b[0]), self.mul(a[1], b[1])),
                self.add(self.mul(a[0], b[1]), self.mul(a[1], b[0])))

    def derivative(self, z: ComplexInterval) -> ComplexInterval:
        """Derivative at t=0 of z*(1+i*t)/(1-i*t), namely 2*i*z."""
        return self.scale(z[1], -2), self.scale(z[0], 2)


def interval_dot(weights, intervals, denominator: int) -> Interval:
    """Exact dyadic/rational matrix action, rounded to the same interval grid."""
    lo = hi = 0
    for w, (a, b) in zip(weights, intervals):
        if w >= 0:
            lo += w*a
            hi += w*b
        else:
            lo += w*b
            hi += w*a
    return lo//denominator, -((-hi)//denominator)


def maxabs(a: Interval) -> int:
    return max(abs(a[0]), abs(a[1]))


def exact_model(cert: dict):
    d = cert['dimension']
    if not isinstance(d, int) or d < 3:
        raise ValueError('The construction requires dimension >=3.')
    h, n = (d-1)//2, d-1
    ps, D = cert['anchor_half_angle_numerators'], cert['anchor_half_angle_denominator']
    selected = cert['selected_variables']
    M, MD = cert['inverse_numerators'], cert['inverse_denominator']
    if not (len(ps) == h+d-1 and len(selected) == n and len(set(selected)) == n
            and all(isinstance(v, int) and 0 <= v < h+d-1 for v in selected)
            and len(M) == n and all(len(row) == n for row in M)):
        raise ValueError('Malformed certificate dimensions or selected-variable list.')
    if not all(isinstance(v, int) for v in ps) or not isinstance(D, int) or D <= 0:
        raise ValueError('Malformed rational anchors.')
    if not isinstance(MD, int) or MD <= 0 or not all(isinstance(v, int) for row in M for v in row):
        raise ValueError('Malformed rational preconditioner.')
    I = FixedIntervals(cert['verification_bits'])
    anchors = []
    for p in ps:
        den = D*D+p*p
        anchors.append((I.rat(D*D-p*p, den), I.rat(2*p*D, den)))
    a = [I.czero for _ in range(d)]
    for j in range(1, h+1):
        a[j] = anchors[j-1]
        a[d-j] = I.conj(a[j])
    if d % 2 == 0:
        a[d//2] = (I.one, I.zero)
    b = [(I.one, I.zero)] + anchors[h:]
    F = []
    for s in range(1, d//2+1):
        total = I.czero
        for seq in (a, b):
            for j in range(d):
                total = I.cadd(total, I.cmul(seq[j], I.conj(seq[(j+s) % d])))
        F.extend(total if 2*s != d else (total[0],))
    columns = []
    for v in selected:
        if v < h:
            j = v+1
            dz = I.derivative(a[j])
            entries = ((j, dz), (d-j, I.conj(dz)))
            seq = a
        else:
            j = v-h+1
            entries = ((j, I.derivative(b[j])),)
            seq = b
        column = []
        for s in range(1, d//2+1):
            total = I.czero
            for l, dz in entries:
                total = I.cadd(total, I.cmul(dz, I.conj(seq[(l+s) % d])))
                total = I.cadd(total, I.cmul(seq[(l-s) % d], I.conj(dz)))
            column.extend(total if 2*s != d else (total[0],))
        columns.append(column)
    return I, F, columns


def verify(path: Path, pure_python: bool = False) -> dict:
    start = time.monotonic()
    cert = json.loads(path.read_text())
    if cert.get('format') != 'hermitian-conference-cayley-contraction-v1':
        raise ValueError('Unsupported certificate format.')
    I, F, columns = exact_model(cert)
    d, n = cert['dimension'], cert['dimension']-1
    M, MD = cert['inverse_numerators'], cert['inverse_denominator']
    rn, rd = cert['radius_numerator'], cert['radius_denominator']
    if not isinstance(rn, int) or not isinstance(rd, int) or rn <= 0 or rd <= 0:
        raise ValueError('The box radius must be a positive rational.')
    r = Fraction(rn, rd)
    MF = [interval_dot(row, F, MD) for row in M]
    a = Fraction(max(map(maxabs, MF)), I.S)
    K = Fraction(max(sum(abs(v) for v in row) for row in M), MD)
    product_bits = cert.get('jacobian_product_bits')
    if product_bits is not None and not pure_python:
        # Coarsen J to an exact integer matrix, with a rigorous entrywise
        # error bound.  The product is int64, never floating point.  An
        # absolute-sum bound below rules out overflow of every partial sum.
        import numpy as np
        if not isinstance(product_bits, int) or not 1 <= product_bits <= 40:
            raise ValueError('jacobian_product_bits must be in [1,40].')
        SJ = 1 << product_bits
        C = np.empty((n, n), dtype=np.int64)
        epsilon_num = 0
        max_c = 0
        for j, col in enumerate(columns):
            for i, (lo, hi) in enumerate(col):
                center = ((lo+hi)*SJ)//(2*I.S)
                if abs(center) >= (1 << 63):
                    raise ArithmeticError('Coarse Jacobian entry does not fit int64.')
                C[i, j] = center
                max_c = max(max_c, abs(center))
                epsilon_num = max(epsilon_num, abs(lo*SJ-center*I.S),
                                  abs(hi*SJ-center*I.S))
        epsilon = Fraction(epsilon_num, I.S*SJ)
        max_m_row_sum = max(sum(abs(v) for v in row) for row in M)
        scale = MD*SJ
        if max_m_row_sum*max_c+scale >= (1 << 63):
            raise ArithmeticError('The integer-product no-overflow bound failed.')
        if any(abs(v) >= (1 << 63) for row in M for v in row):
            raise ArithmeticError('Preconditioner entry does not fit int64.')
        product = np.asarray(M, dtype=np.int64) @ C
        # Row sums are evaluated as unbounded Python integers.
        max_error = max(sum(abs((scale if i == j else 0)-int(product[i,j]))
                            for j in range(n)) for i in range(n))
        b = Fraction(max_error, scale)+K*n*epsilon
        backend = 'int64 product, proven no overflow, exact coarse-grid error bound'
    else:
        row_sums = []
        for i, row in enumerate(M):
            error_sum = 0
            for j, col in enumerate(columns):
                product = interval_dot(row, col, MD)
                target = I.one if i == j else I.zero
                error_sum += maxabs(I.sub(target, product))
            row_sums.append(error_sum)
        b = Fraction(max(row_sums), I.S)
        backend = 'unbounded Python integer interval products'
    # Sum of absolute second derivatives of each real equation <= 32*d.
    self_map_bound = a+b*r+16*d*K*r*r
    contraction_bound = b+32*d*K*r
    passed = (b < 1 and self_map_bound < r and contraction_bound < 1)
    if not passed:
        raise ArithmeticError('Certificate does not establish a contraction/self-map.')
    def bound_record(x):
        return {'numerator': x.numerator, 'denominator': x.denominator,
                'decimal_display_only': float(x)}
    return {
        'certificate': path.name,
        'dimension': d,
        'conference_order': 2*d,
        'passed': True,
        'verification_method': 'outward-rounded integer intervals and exact rational inequalities',
        'matrix_product_backend': backend,
        'a_bound_for_norm_MF': bound_record(a),
        'b_bound_for_norm_I_minus_MJ': bound_record(b),
        'K_norm_M': bound_record(K),
        'radius': bound_record(r),
        'self_map_bound': bound_record(self_map_bound),
        'contraction_bound': bound_record(contraction_bound),
        'seconds': time.monotonic()-start,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificates', type=Path, nargs='+')
    parser.add_argument('--out', type=Path)
    parser.add_argument('--pure-python', action='store_true', help='Use unbounded integer interval products, even when a fast product is specified.')
    args = parser.parse_args()
    reports = [verify(path, pure_python=args.pure_python) for path in args.certificates]
    output = json.dumps(reports, indent=2)+'\n'
    if args.out:
        args.out.write_text(output)
    print(output)
