#!/usr/bin/env python3
"""Sharp formula for spectrum (alpha,beta,...,beta), with exact rationals."""
from __future__ import annotations
from math import factorial, comb
from fractions import Fraction
import sympy as sp

def support_value(n: int, k: int, alpha, beta) -> Fraction:
    if n < 1 or not 1 <= k <= n:
        raise ValueError('Require n>=1 and 1<=k<=n')
    alpha,beta = Fraction(alpha),Fraction(beta)
    if min(alpha,beta)<0:
        raise ValueError('Eigenvalues must be nonnegative')
    delta=alpha-beta
    return sum((Fraction(comb(k,j)*factorial(j))*beta**(n-j)*(delta/k)**j
                for j in range(k+1)), Fraction())

def exceptional_maximum(n: int, alpha, beta) -> dict:
    if n < 1:
        raise ValueError('n must be positive')
    alpha,beta=Fraction(alpha),Fraction(beta)
    if min(alpha,beta)<0:
        raise ValueError('Eigenvalues must be nonnegative')
    if n==1:
        return {'maximum':alpha,'supports':[1],'kind':'one-dimensional'}
    if alpha==beta:
        return {'maximum':beta**n,'supports':None,'kind':'scalar orbit'}
    values={k:support_value(n,k,alpha,beta) for k in sorted({2,n})}
    value=max(values.values())
    return {'maximum':value,'supports':[k for k,v in values.items() if v==value],
            'kind':'equal-support optimizer'}

def normalized_support(k: int, x) -> Fraction:
    return support_value(k,k,1-Fraction(x),1)

def transition_polynomial(n: int) -> sp.Poly:
    if n<3:
        raise ValueError('The nontrivial transition starts at n=3')
    x=sp.Symbol('x')
    fn=sum(sp.Rational(factorial(n),factorial(n-j))*(-x/n)**j
           for j in range(n+1))
    return sp.Poly(sp.cancel((fn-(1-x+x*x/2))/x**2),x)

def transition_interval(n: int, digits: int=20):
    poly=transition_polynomial(n)
    roots=poly.intervals(eps=sp.Rational(1,10**digits), inf=0, sup=1)
    if len(roots)!=1 or roots[0][1]!=1:
        raise AssertionError('Expected exactly one simple root in (0,1)')
    return roots[0][0]

if __name__=='__main__':
    import argparse,json
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('n',type=int)
    ap.add_argument('alpha')
    ap.add_argument('beta')
    ap.add_argument('--transition',action='store_true')
    args=ap.parse_args()
    result=exceptional_maximum(args.n,args.alpha,args.beta)
    result['maximum']=str(result['maximum'])
    if args.transition:
        result['transition_polynomial']=str(transition_polynomial(args.n).as_expr())
        result['transition_interval']=[str(v) for v in transition_interval(args.n)]
    print(json.dumps(result,indent=2))
