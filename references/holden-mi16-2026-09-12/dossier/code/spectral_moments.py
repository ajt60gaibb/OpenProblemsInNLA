#!/usr/bin/env python3
"""Exact unitary-orbit permanent moments; factorial-cost reference code.

Inputs are exact nonnegative rational numbers. The character formula is valid
for arbitrary order and moment, but enumeration is deliberately budget-limited.
No numerical integration is used. See the accompanying proof for the formula.
"""
from __future__ import annotations
from collections import Counter
from functools import lru_cache
from itertools import permutations, product
from math import factorial
from typing import Iterable
import sympy as sp

@lru_cache(None)
def partitions(total: int, cap: int | None = None) -> tuple[tuple[int, ...], ...]:
    if total < 0:
        return ()
    if total == 0:
        return ((),)
    cap = min(total, total if cap is None else cap)
    return tuple((first,) + rest for first in range(cap, 0, -1)
                 for rest in partitions(total-first, first))

def cycle_type(perm: tuple[int, ...]) -> tuple[int, ...]:
    seen: set[int] = set()
    lengths = []
    for i in range(len(perm)):
        if i in seen:
            continue
        j, length = i, 0
        while j not in seen:
            seen.add(j)
            length += 1
            j = perm[j]
        lengths.append(length)
    return tuple(sorted(lengths, reverse=True))

@lru_cache(None)
def border_strip_removals(shape: tuple[int, ...], size: int):
    """Return (remaining partition, strip height) for each legal rim removal."""
    answer = []
    for mu in partitions(sum(shape)-size):
        if len(mu) > len(shape) or any(mu[i] > shape[i] for i in range(len(mu))):
            continue
        cells = {(i,j) for i,row in enumerate(shape)
                 for j in range(mu[i] if i < len(mu) else 0, row)}
        if len(cells) != size or not cells:
            continue
        # A border strip is connected and contains no 2-by-2 square.
        if any({(i+1,j),(i,j+1),(i+1,j+1)} <= cells for i,j in cells):
            continue
        reached = {next(iter(cells))}
        stack = list(reached)
        while stack:
            i,j = stack.pop()
            for neighbor in ((i-1,j),(i+1,j),(i,j-1),(i,j+1)):
                if neighbor in cells and neighbor not in reached:
                    reached.add(neighbor)
                    stack.append(neighbor)
        if reached == cells:
            answer.append((mu, len({i for i,j in cells})-1))
    return tuple(answer)

@lru_cache(None)
def character(shape: tuple[int, ...], cycles: tuple[int, ...]) -> int:
    """Irreducible symmetric-group character, Murnaghan--Nakayama rule."""
    if sum(shape) != sum(cycles):
        return 0
    if not cycles:
        return int(not shape)
    return sum((-1)**height * character(mu, cycles[1:])
               for mu,height in border_strip_removals(shape, cycles[0]))

def specht_dimension(shape: tuple[int, ...]) -> int:
    hooks = 1
    for i,row in enumerate(shape):
        for j in range(row):
            hooks *= row-j + sum(other > j for other in shape[i+1:])
    return factorial(sum(shape)) // hooks

def schur_at_ones(shape: tuple[int, ...], n: int) -> sp.Rational:
    result = sp.S.One
    for i,row in enumerate(shape):
        for j in range(row):
            hook = row-j + sum(other > j for other in shape[i+1:])
            result *= sp.Rational(n+j-i, hook)
    return sp.Rational(result)

def schur_value(shape: tuple[int, ...], spectrum: tuple[sp.Rational, ...]):
    if not shape:
        return sp.S.One
    degree = shape[0] + len(shape)-1
    h = [sp.S.One] + [sp.S.Zero]*degree
    for value in spectrum:
        for j in range(1, degree+1):
            h[j] += value*h[j-1]
    ell = len(shape)
    def entry(i,j):
        index = shape[i]-i+j
        return h[index] if index >= 0 else sp.S.Zero
    return sp.det(sp.Matrix(ell, ell, entry))

@lru_cache(None)
def rectangle_cycle_counts(n: int, p: int, max_terms: int = 2_000_000):
    """Cycle types of kh, h in row group (S_n)^p, k in (S_p)^n."""
    if n < 1 or p < 1:
        raise ValueError('n and p must be positive integers')
    terms = factorial(n)**p * factorial(p)**n
    if terms > max_terms:
        raise ValueError(f'Enumeration needs {terms} terms; budget is {max_terms}. '
                         'Raise max_terms explicitly only for a feasible run.')
    row_perms = tuple(permutations(range(n)))
    col_perms = tuple(permutations(range(p)))
    hs = [tuple(a*n+rows[a][i] for a in range(p) for i in range(n))
          for rows in product(row_perms, repeat=p)]
    ks = [tuple(cols[i][a]*n+i for a in range(p) for i in range(n))
          for cols in product(col_perms, repeat=n)]
    counts: Counter = Counter()
    for h in hs:
        for k in ks:
            counts[cycle_type(tuple(k[h[j]] for j in range(n*p)))] += 1
    assert sum(counts.values()) == terms
    return tuple(sorted(counts.items()))

@lru_cache(None)
def moment_weights(n: int, p: int, max_terms: int = 2_000_000):
    counts = rectangle_cycle_counts(n,p,max_terms)
    m = n*p
    result = []
    for shape in partitions(m):
        if len(shape) > n:
            continue
        total = sum(count*character(shape,cycles) for cycles,count in counts)
        weight = sp.Rational(specht_dimension(shape)*total, factorial(m))
        if weight < 0:
            raise AssertionError('Negative central-projector weight')
        if weight:
            result.append((shape,weight))
    if sum(weight for shape,weight in result) != 1:
        raise AssertionError('Weights do not sum to one')
    return tuple(result)

def exact_moment(spectrum: Iterable, p: int, max_terms: int = 2_000_000):
    lam = tuple(sp.Rational(x) for x in spectrum)
    if not lam or any(x < 0 for x in lam):
        raise ValueError('Provide a nonempty nonnegative rational spectrum')
    n = len(lam)
    return sum(weight*schur_value(shape,lam)/schur_at_ones(shape,n)
               for shape,weight in moment_weights(n,p,max_terms))

if __name__ == '__main__':
    import argparse, json
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('spectrum', nargs='+', help='Exact rationals, for example 0 1 2')
    ap.add_argument('--moment', type=int, default=1)
    ap.add_argument('--max-terms', type=int, default=2_000_000)
    args = ap.parse_args()
    result = exact_moment(args.spectrum,args.moment,args.max_terms)
    print(json.dumps({'spectrum': args.spectrum, 'moment_order': args.moment,
                      'exact_moment': str(result)}, indent=2))
