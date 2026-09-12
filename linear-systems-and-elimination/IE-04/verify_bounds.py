#!/usr/bin/env python3
"""Finite exact checks accompanying the analytic IE-04 proof.

The manuscript proves the result for every n; these checks are supporting
certificates, not a replacement for that proof.  Interval endpoints are
outward-rounded dyadic rationals, using only integer arithmetic.
Python 3.10+; standard library only.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import json
from pathlib import Path


@dataclass(frozen=True)
class Interval:
    lo: int
    hi: int
    precision: int

    @property
    def scale(self) -> int:
        return 1 << self.precision

    @classmethod
    def point(cls, x: F, precision: int) -> Interval:
        y = x*(1 << precision)
        return cls(y.numerator//y.denominator,
                   -((-y.numerator)//y.denominator), precision)

    def check(self, other: Interval) -> None:
        if self.precision != other.precision:
            raise ValueError('Different interval precisions.')
        if self.lo > self.hi or other.lo > other.hi:
            raise ValueError('Invalid interval endpoints.')

    def __add__(self, other: Interval) -> Interval:
        self.check(other)
        return Interval(self.lo+other.lo, self.hi+other.hi, self.precision)

    def __sub__(self, other: Interval) -> Interval:
        self.check(other)
        return Interval(self.lo-other.hi, self.hi-other.lo, self.precision)

    def __mul__(self, other: Interval) -> Interval:
        self.check(other)
        values = [a*b for a in (self.lo,self.hi) for b in (other.lo,other.hi)]
        return Interval(min(values)//self.scale,
                        -((-max(values))//self.scale), self.precision)

    def __truediv__(self, other: Interval) -> Interval:
        self.check(other)
        if other.lo <= 0 <= other.hi:
            raise ZeroDivisionError('Divisor interval includes zero.')
        values = [F(a*self.scale,b) for a in (self.lo,self.hi)
                  for b in (other.lo,other.hi)]
        low, high = min(values), max(values)
        return Interval(low.numerator//low.denominator,
                        -((-high.numerator)//high.denominator), self.precision)

    def abs_upper(self) -> F:
        return F(max(abs(self.lo),abs(self.hi)),self.scale)


def entry(n: int, i: int, j: int) -> F:
    if j == n-1:
        return F(1)
    return F(1) if i == j else F(-1,2) if i > j else F(0)


def check_interval_box(n: int) -> dict:
    if n < 2:
        raise ValueError('n must be at least 2.')
    assert all(abs(entry(n,i,j)-F(i==j)) <= 1 for i in range(n) for j in range(n))
    precision = 4*n*n+8*n+64
    scale = 1 << precision
    delta = F(1, 1 << (n*n+n+1))
    width = delta*scale
    assert width.denominator == 1
    w = width.numerator
    a = [[Interval.point(entry(n,i,j),precision) for j in range(n)]
         for i in range(n)]
    a = [[Interval(x.lo-w,x.hi+w,precision) for x in row] for row in a]
    stages = []
    growth_base = F(3,2)**(n-1)
    for k in range(n):
        stage_growth = F(3,2)**k
        error = F(0)
        for i in range(k,n):
            for j in range(k,n):
                ideal = stage_growth if j == n-1 else entry(n,i,j)
                error = max(error, abs(F(a[i][j].lo,scale)-ideal),
                            abs(F(a[i][j].hi,scale)-ideal))
        envelope = (1 << ((n+2)*k))*delta
        assert error <= envelope
        assert error <= F(1,8)
        if k == n-1:
            break
        pivot = a[k][k]
        competitor = max(a[i][k].abs_upper() for i in range(k+1,n))
        assert F(pivot.lo,scale) > competitor
        assert pivot.lo > 0
        stages.append({'step':k+1, 'pivot_lower':str(F(pivot.lo,scale)),
                       'competitor_upper':str(competitor)})
        for i in range(k+1,n):
            multiplier = a[i][k]/pivot
            for j in range(k+1,n):
                a[i][j] = a[i][j] - multiplier*a[k][j]
    final_lower = F(a[-1][-1].lo,scale)
    final_upper = F(a[-1][-1].hi,scale)
    guaranteed_growth = final_lower/(1+delta)
    assert final_lower > 0
    assert guaranteed_growth > growth_base/2
    return {'n':n, 'dyadic_precision_bits':precision, 'delta':str(delta),
            'all_pivots_strictly_no_swap':True,
            'final_schur_lower':str(final_lower), 'final_schur_upper':str(final_upper),
            'guaranteed_growth_lower':str(guaranteed_growth),
            'target_growth':str(growth_base/2),
            'negative_log2_probability_lower_bound':n*n*(n*n+n+5)}


def check_scalar_formulas() -> None:
    for n in range(2,257):
        b = 1 << (n+2)
        delta = F(1,1 << (n*n+n+1))
        assert delta*b**(n-1) == F(1,8)
        assert delta <= F(1,8)
        assert 2+2*(1 << n) <= b
        assert F(3,2)**(n-1) <= 1 << n
        assert n*n*(n*n+n+5) <= 3*n**4
        c = F(3,2)**(n-1)
        assert (c-F(1,8))/(1+delta) > c/2
    # Universal algebra used in the proof, evaluated at its maximal e.
    e = F(1,8)
    assert (F(1,2)+e)/(1-e) == F(5,7)
    assert (F(3,2)*e)/(1-e) <= 2*e
    # Euler's number e < 3 and pi < 4 imply
    # exp(-2)/sqrt(2*pi) > 1/27 > 1/32; no floating point is needed.
    assert F(1,27) > F(1,32)


def illustrative_threshold(c1: int, c2: F) -> dict:
    if c1 <= 0 or c2 <= 0:
        raise ValueError('Positive constants are required.')
    for n in range(2,10001):
        x = F(3,2)**(n-1)/(2*n**c1)
        k = n*n*(n*n+n+5)
        if x >= 1 and c2*x > k:
            return {'c1':c1, 'c2':str(c2), 'n':n,
                    'x':str(x), 'K_n':k, 'c2_x_greater_than_K_n':True}
    raise RuntimeError('Increase the illustrative search limit.')


def main() -> None:
    if not __debug__:
        raise RuntimeError('Run without -O: assertions are part of the checks.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n',type=int,default=16)
    parser.add_argument('--write-certificate',type=Path)
    args = parser.parse_args()
    if not 2 <= args.max_n <= 64:
        parser.error('--max-n must be between 2 and 64.')
    check_scalar_formulas()
    boxes = []
    for n in range(2,args.max_n+1):
        boxes.append(check_interval_box(n))
        print(f'n={n:2d}: PASS -- full interval box, strict pivots, growth > (3/2)^(n-1)/2')
    examples = [illustrative_threshold(1,F(1)), illustrative_threshold(10,F(1)),
                illustrative_threshold(1,F(1,1000))]
    for example in examples:
        print('Illustrative exact contradiction:', {k:v for k,v in example.items() if k != 'x'})
    print('PASS: scalar formulas checked for n=2,...,256.')
    print('The universal result and Gaussian probability bound are proved in solution.pdf;')
    print('finite checks are supplementary, not a proof for untested dimensions.')
    if args.write_certificate:
        payload = {'problem':'IE-04','arithmetic':'exact integers and rational dyadic intervals',
                   'interval_boxes':boxes,'illustrative_thresholds':examples,
                   'smoothed_center':'I_n: nonsingular, spectral norm one', 'sigma':1,
                   'scope':'Finite computational supplements to the universal analytic proof.'}
        args.write_certificate.write_text(json.dumps(payload,indent=2)+'\n',encoding='utf-8')
        print('Certificate written:',args.write_certificate.name)


if __name__ == '__main__':
    main()
