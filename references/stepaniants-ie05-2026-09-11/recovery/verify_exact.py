#!/usr/bin/env python3
"""Exact certificate for the IE-05 order-eight counterexample.

Python 3.10+; standard library only.  No floating-point computation is used
in any mathematical assertion.  Decimal displays are explicitly nonproof.
Run: python verify_exact.py [--write-certificate certificate.json]
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from functools import reduce
import json
from math import gcd, lcm, sqrt
from pathlib import Path
from typing import Any

Matrix = list[list[F]]


def lower_matrix(modified: bool) -> Matrix:
    a = [[F(1 if i == j else -1 if i > j else 0)
          for j in range(8)] for i in range(8)]
    if modified:
        a[6][1] = F(0)  # One-based entry (7, 2): -1 becomes 0.
    return a


def transpose(a: Matrix) -> Matrix:
    return [list(row) for row in zip(*a)]


def multiply(a: Matrix, b: Matrix) -> Matrix:
    return [[sum((x*y for x, y in zip(row, col)), F(0))
             for col in transpose(b)] for row in a]


def rational_gram_schmidt(a: Matrix) -> tuple[Matrix, list[F]]:
    n = len(a)
    v = [[F(0) for _ in range(n)] for _ in range(n)]
    d: list[F] = []
    for j in range(n):
        col = [a[i][j] for i in range(n)]
        for k in range(j):
            alpha = sum((v[i][k]*a[i][j] for i in range(n)), F(0))/d[k]
            col = [col[i] - alpha*v[i][k] for i in range(n)]
        dj = sum((x*x for x in col), F(0))
        assert dj > 0, 'Singular input.'
        d.append(dj)
        for i in range(n):
            v[i][j] = col[i]
    return v, d


def integer_columns(v: Matrix) -> tuple[Matrix, list[F]]:
    n = len(v)
    m = [[F(0) for _ in range(n)] for _ in range(n)]
    scales: list[F] = []
    for j in range(n):
        denom = lcm(*(v[i][j].denominator for i in range(n)))
        raw = [int(v[i][j]*denom) for i in range(n)]
        common = reduce(gcd, (abs(x) for x in raw))
        scale = F(denom, common)
        scales.append(scale)
        for i in range(n):
            m[i][j] = v[i][j]*scale
            assert m[i][j].denominator == 1
    return m, scales


def solve_lower(a: Matrix, b: Matrix) -> Matrix:
    n = len(a)
    x = [[F(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        assert a[i][i] != 0
        for j in range(n):
            x[i][j] = (b[i][j] - sum(
                (a[i][k]*x[k][j] for k in range(i)), F(0)))/a[i][i]
    return x


def exact_ge(m: Matrix, norms: list[F]) -> dict[str, Any]:
    n = len(m)
    a = [row[:] for row in m]
    maxima: list[F] = []
    positions: list[list[list[int]]] = []
    multipliers: list[list[F]] = []
    for k in range(n):
        vals = [(a[i][j]*a[i][j]/norms[j], i+1, j+1)
                for i in range(k, n) for j in range(k, n)]
        maximum = max(x[0] for x in vals)
        maxima.append(maximum)
        positions.append([[i, j] for value, i, j in vals if value == maximum])
        assert a[k][k] > 0
        assert all(abs(a[i][k]) <= a[k][k] for i in range(k, n))
        # Thus first-available-row tie breaking chooses row k, without a swap.
        stage_multipliers = [a[i][k]/a[k][k] for i in range(k+1, n)]
        multipliers.append(stage_multipliers)
        for i, mult in zip(range(k+1, n), stage_multipliers):
            for j in range(k+1, n):
                a[i][j] -= mult*a[k][j]
            a[i][k] = F(0)
    return {'stage_maximum_squares': maxima,
            'stage_maximum_positions_one_based': positions,
            'multipliers': multipliers,
            'eliminated_integer_column_matrix': a,
            'input_maximum_square': maxima[0],
            'largest_active_entry_square': max(maxima),
            'growth_factor_square': max(maxima)/maxima[0]}


def case(modified: bool) -> dict[str, Any]:
    a = lower_matrix(modified)
    v, d = rational_gram_schmidt(a)
    m, scales = integer_columns(v)
    gram = multiply(transpose(m), m)
    norms = [gram[j][j] for j in range(8)]
    assert all(gram[i][j] == (norms[i] if i == j else 0)
               for i in range(8) for j in range(8))
    assert all(norms[j] == d[j]*scales[j]**2 for j in range(8))
    upper = solve_lower(a, m)
    assert all(upper[i][j] == 0 for i in range(8) for j in range(i))
    assert all(upper[i][i] > 0 for i in range(8))
    assert multiply(a, upper) == m
    ge = exact_ge(m, norms)
    assert ge['eliminated_integer_column_matrix'] == upper
    assert all(ge['multipliers'][k] == [a[i][k] for i in range(k+1, 8)]
               for k in range(8))
    return {'modified': modified, 'lower_matrix': a,
            'orthogonal_integer_columns': m, 'column_norm_squares': norms,
            'positive_upper_factor': upper,
            'positive_upper_diagonal': [upper[i][i] for i in range(8)],
            'normalization': 'Q = M diag(s_j^(-1/2)), taking positive square roots',
            **ge}


def encode(value: Any) -> Any:
    if isinstance(value, F):
        return str(value)
    if isinstance(value, list):
        return [encode(x) for x in value]
    if isinstance(value, dict):
        return {k: encode(v) for k, v in value.items()}
    return value


def verify() -> dict[str, Any]:
    base, modified = case(False), case(True)
    assert base['input_maximum_square'] == F(2601, 3286)
    assert modified['input_maximum_square'] == F(3969, 5272)
    assert base['largest_active_entry_square'] == 5462
    assert modified['largest_active_entry_square'] == 5272
    assert base['growth_factor_square'] == F(17948132, 2601)
    assert modified['growth_factor_square'] == F(27793984, 3969)
    assert modified['growth_factor_square'] == F(5272, 63)**2
    expected_base = [F(2601,3286), F(4608,2731), F(15488,2731),
                     F(59168,2731), F(233928,2731), F(932978,2731),
                     F(2731,2), F(5462)]
    expected_modified = [F(3969,5272), F(2209,1318), F(29929,5272),
                         F(28561,1318), F(56448,659), F(450241,1318),
                         F(7198489,5272), F(5272)]
    assert base['stage_maximum_squares'] == expected_base
    assert modified['stage_maximum_squares'] == expected_modified
    delta = modified['growth_factor_square'] - base['growth_factor_square']
    assert delta > 0
    cross = 27793984*2601 - 17948132*3969
    assert cross > 0
    return {'problem': 'IE-05', 'arithmetic': 'exact Python fractions.Fraction',
            'dimension': 8, 'baseline': base, 'counterexample': modified,
            'squared_growth_difference': delta, 'cross_product_difference': cross}


def main() -> None:
    if not __debug__:
        raise RuntimeError('Run without -O: assertions are part of the checks.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-certificate', type=Path)
    args = parser.parse_args()
    certificate = verify()
    for label in ['baseline', 'counterexample']:
        c = certificate[label]
        print(label.upper())
        print('  column norm squares:', ', '.join(map(str,c['column_norm_squares'])))
        print('  input max squared:', c['input_maximum_square'])
        print('  maximum active entry squared:', c['largest_active_entry_square'])
        print('  growth squared:', c['growth_factor_square'])
        print('  growth (approximate display only):', sqrt(c['growth_factor_square']))
        print('  all eight squared stage maxima:', ', '.join(map(str,c['stage_maximum_squares'])))
    print('Exact positive cross-product difference:', certificate['cross_product_difference'])
    print('PASS: orthogonality, positive QR convention, admissible first-tie GEPP,')
    print('      every stage maximum, and the strict growth comparison.')
    if args.write_certificate:
        args.write_certificate.write_text(json.dumps(encode(certificate), indent=2)+'\n', encoding='utf-8')
        print('Certificate written:', args.write_certificate.name)


if __name__ == '__main__':
    main()
