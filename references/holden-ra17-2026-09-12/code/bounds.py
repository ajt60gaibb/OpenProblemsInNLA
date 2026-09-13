#!/usr/bin/env python3
"""Proved RA-17 bounds; NOT an all-dimension exact solver.

Enumerating Schur partitions can be exponential. The Stiefel-Whitney bound is
skipped when the rectangle has more than --partition-limit partitions; every
reported bound remains valid. Degree parity, Pontryagin/Euler bounds, and
Clifford bounds do not use this enumeration.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from functools import lru_cache
import json
from math import comb, factorial, isqrt
from pathlib import Path
from typing import Iterator

ROOT = Path(__file__).resolve().parents[1]

def v2(n: int) -> int:
    if n < 1: raise ValueError('v2 requires a positive integer')
    return (n & -n).bit_length() - 1

def rho(d: int) -> int:
    periods, residue = divmod(v2(d), 4)
    return 8 * periods + 2 ** residue

def degree_valuation(d: int, r: int) -> int:
    k, c = 2*r, d-2*r
    return sum((k+i).bit_count() + (c+i).bit_count()
               - (d+i).bit_count() - i.bit_count() for i in range(c))

def degree(d: int, r: int) -> int:
    k, c = 2*r, d-2*r
    result = Fraction(1)
    for i in range(c):
        result *= Fraction(factorial(d+i)*factorial(i), factorial(k+i)*factorial(c+i))
    if result.denominator != 1: raise ArithmeticError('nonintegral determinantal degree')
    return result.numerator

def partitions(height: int, width: int) -> Iterator[tuple[int, ...]]:
    if height == 0:
        yield (); return
    for first in range(width, -1, -1):
        for tail in partitions(height-1, first):
            yield (first,) + tail

def schur_dimension_valuation(partition: tuple[int, ...], d: int) -> int:
    result = 0
    for i, row in enumerate(partition):
        for j in range(row):
            hook = row-j + sum(other > j for other in partition[i+1:])
            result += v2(d+j-i)-v2(hook)
    if result < 0: raise ArithmeticError('negative representation-dimension valuation')
    return result

def rectangle_dimension(d: int, r: int, s: int) -> int:
    value = Fraction(1)
    for i in range(1, r+1):
        for j in range(1, s+1):
            value *= Fraction(d+j-i, r+s-i-j+1)
    if value.denominator != 1: raise ArithmeticError('nonintegral Schur dimension')
    return value.numerator

@lru_cache(maxsize=None)
def bounds(d: int, r: int, partition_limit: int = 200000) -> dict:
    if not isinstance(d, int) or not isinstance(r, int) or d < 2 or not 1 <= r <= d//2:
        raise ValueError('require d >= 2 and 1 <= r <= floor(d/2)')
    k, c = 2*r, d-2*r
    m0 = d*d-c*c
    if c == 0:
        return {'d':d, 'r':r, 'lower':d*d, 'upper':d*d, 'exact':True,
                'generic_count':m0, 'reason':'full-rank difference set'}
    if c == 1:
        return {'d':d, 'r':r, 'lower':d*d-1, 'upper':d*d-1, 'exact':True,
                'generic_count':m0, 'reason':'odd determinant boundary'}
    eps, s = d % 2, d//2-r
    base = 2*d*r+2*r*s
    extra = int((eps == 0 and r*s % 2 == 1)
                or (eps == 1 and r*(s+1) % 2 == 1))
    lower_candidates = {'evaluation dimension':2*d*r,
                        'Pontryagin/Euler':base+extra}
    if r == 1:
        if eps:
            lower_candidates['rank-one Euler square'] = 3*d-2
        else:
            coefficient = comb(d+s-1, s)
            square_obstruction = s % 2 == 1 or isqrt(coefficient)**2 != coefficient
            lower_candidates['rank-one Euler square'] = 3*d-2+int(square_obstruction)
    upper_candidates = {'anti-diagonal construction':m0,
                        'Hurwitz nonsingular construction':d*d-rho(d)}
    if d % 8 == 4:
        upper_candidates['Xu-octonion construction'] = d*d-5
    valuation = degree_valuation(d,r)
    if valuation == 0:
        lower_candidates['odd determinantal degree'] = m0
    if c == 2:
        lower_candidates['cofactor complex K-theory'] = d*d-(2*v2(d)+2)
    if d == 4 and r == 1:
        lower_candidates['four-dimensional Grassmannian obstruction'] = 11
        upper_candidates['exactly certified Xu construction'] = 11
    witness = None
    count = comb(d,k)
    if partition_limit >= count:
        best = 0
        for partition in partitions(k,c):
            weight = sum(partition)
            if weight > best and schur_dimension_valuation(partition,d) == 0:
                best, witness = weight, partition
        lower_candidates['Stiefel-Whitney/Schur'] = 2*d*r+best
    low, high = max(lower_candidates.values()), min(upper_candidates.values())
    if low > high:
        raise ArithmeticError(f'inconsistent proved bounds for {(d,r)}: {low}>{high}')
    return {'d':d, 'r':r, 'lower':low, 'upper':high, 'exact':low==high,
            'generic_count':m0, 'degree_v2':valuation,
            'lower_candidates':lower_candidates, 'upper_candidates':upper_candidates,
            'schur_partition_count':count, 'schur_enumerated':partition_limit>=count,
            'schur_witness':witness}

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-d',type=int,default=16)
    parser.add_argument('--partition-limit',type=int,default=200000)
    parser.add_argument('--output',type=Path,default=ROOT/'results'/'bounds_table.json')
    args=parser.parse_args()
    if args.max_d < 2: parser.error('--max-d must be at least 2')
    data = [bounds(d,r,args.partition_limit) for d in range(2,args.max_d+1)
            for r in range(1,d//2+1)]
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(' d  r   lower   upper   exact')
    for item in data:
        print(f"{item['d']:2d} {item['r']:2d} {item['lower']:7d} {item['upper']:7d}   "
              f"{'yes' if item['exact'] else 'NO'}")
    print('Intervals are only the bounds proved in the accompanying paper.')

if __name__=='__main__': main()
