#!/usr/bin/env python3
"""Exact rational implementation of the KE-02 subclass algorithms.

The mathematical proof uses the repository's unit-cost exact-arithmetic model.
This Python implementation does not assert a bit-complexity bound. A complex
rational input is (real_part, imaginary_part). No floating point is accepted.
The promised operator-norm normalization is not tested by an eigensolver.
"""
from __future__ import annotations
from fractions import Fraction
from typing import Sequence

Rational = int | Fraction
ComplexRational = tuple[Rational, Rational]

def rational(x: Rational) -> Fraction:
    if isinstance(x, bool) or not isinstance(x, (int, Fraction)):
        raise TypeError('Use int or Fraction, not floating-point input.')
    return Fraction(x)

def diagonal_ramp(diagonal: Sequence[Rational], delta: Rational) -> tuple[Fraction, ...]:
    t = tuple(rational(x) for x in diagonal)
    d = rational(delta)
    n = len(t)
    if n < 2 or not 0 < d < Fraction(1, 2):
        raise ValueError('Require n >= 2 and 0 < delta < 1/2.')
    order = sorted(range(n), key=lambda i: (t[i], i))
    gamma = 2*d/(n-1)
    result = [Fraction(0)]*n
    for j, i in enumerate(order):
        result[i] = -d + j*gamma
    return tuple(result)

def phase_toeplitz_perturbation(
    diagonal: Sequence[Rational],
    upper: Sequence[ComplexRational],
    delta: Rational,
) -> tuple[tuple[Fraction, ...], str]:
    """Theorem B. The lower diagonal is the conjugate of the supplied upper.

    Checks the constant diagonal and equal-magnitude assumptions exactly.
    Returns D as a tuple and the branch name. The input norm <= 1 is a promise.
    The exact proof gives gap(T+D) >= delta/n^3 for the promised inputs.
    """
    t = tuple(rational(x) for x in diagonal)
    d = rational(delta)
    n = len(t)
    if n < 2 or len(upper) != n-1 or not 0 < d < Fraction(1, 2):
        raise ValueError('Invalid shape or delta.')
    if any(x != t[0] for x in t):
        raise ValueError('Theorem B requires a constant diagonal.')
    norms_squared = []
    for z in upper:
        if len(z) != 2:
            raise ValueError('Represent a complex rational as (real, imaginary).')
        re, im = map(rational, z)
        norms_squared.append(re*re + im*im)
    if any(x != norms_squared[0] for x in norms_squared):
        raise ValueError('Theorem B requires equal off-diagonal magnitudes.')
    if norms_squared[0] <= d*d/(16*n*n):
        # Because the diagonal is constant, no sort is needed in this branch.
        gamma = 2*d/(n-1)
        return tuple(-d+j*gamma for j in range(n)), 'weak'
    return (Fraction(0),)*n, 'strong'
