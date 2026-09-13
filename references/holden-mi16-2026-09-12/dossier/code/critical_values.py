#!/usr/bin/env python3
"""Critical-value elimination for the exact algebraic prescription.

This is a small-order reference implementation, not an efficient solver.
It accepts rational spectra only; the paper works over Q(lambda_1,...,lambda_n).
General lexicographic elimination can be extremely expensive. The default
command-line guard permits only n<=2. --allow-expensive overrides that guard.
"""
from __future__ import annotations
from itertools import permutations
from typing import Iterable
import sympy as sp

def permanent(matrix: sp.Matrix):
    n,m = matrix.shape
    if n != m:
        raise ValueError('The permanent requires a square matrix')
    return sp.expand(sum(sp.prod(matrix[i,perm[i]] for i in range(n))
                         for perm in permutations(range(n))))

def orbit_critical_ideal(spectrum: Iterable):
    lam = tuple(sp.Rational(x) for x in spectrum)
    if not lam or any(x < 0 for x in lam):
        raise ValueError('Provide nonnegative rational eigenvalues')
    n = len(lam)
    variables = sp.symbols('a0:'+str(n*n))
    a = sp.Matrix(n,n,variables)
    z = sp.Symbol('z')
    identity = sp.eye(n)
    q_of_a = identity
    for theta in sorted(set(lam)):
        q_of_a = q_of_a*(a-theta*identity)
    constraints = [sp.trace(a**j)-sum(v**j for v in lam)
                   for j in range(1,n+1)]
    constraints += list(q_of_a)
    adj = sp.Matrix(n,n, lambda i,j: permanent(a.minor_submatrix(j,i)))
    constraints += list(a*adj-adj*a)
    constraints += [z-permanent(a)]
    constraints = list(dict.fromkeys(sp.expand(g) for g in constraints if g != 0))
    return constraints, variables, z

def critical_polynomial(spectrum: Iterable):
    constraints, variables, z = orbit_critical_ideal(spectrum)
    basis = sp.groebner(constraints, *variables, z, order='lex', domain=sp.QQ)
    univariate = [sp.Poly(g.as_expr(),z,domain=sp.QQ) for g in basis.polys
                  if g.as_expr().free_symbols <= {z}]
    if not univariate:
        raise AssertionError('A nonzero elimination polynomial must exist')
    generator = univariate[0]
    for other in univariate[1:]:
        generator = sp.gcd(generator,other)
    if generator.degree() < 1:
        raise AssertionError('The critical locus must have at least one value')
    return generator.sqf_part().monic()

if __name__ == '__main__':
    import argparse,json
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('spectrum',nargs='+')
    ap.add_argument('--allow-expensive',action='store_true')
    args=ap.parse_args()
    if len(args.spectrum)>2 and not args.allow_expensive:
        ap.error('n>2 elimination is expensive; use --allow-expensive deliberately')
    polynomial=critical_polynomial(args.spectrum)
    print(json.dumps({'spectrum':args.spectrum,
                      'critical_value_polynomial':str(polynomial.as_expr()),
                      'factorization':str(sp.factor(polynomial.as_expr()))},indent=2))
