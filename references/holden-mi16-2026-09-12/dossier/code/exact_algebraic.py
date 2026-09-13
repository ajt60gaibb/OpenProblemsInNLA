#!/usr/bin/env python3
"""Budgeted reference implementation of the all-spectrum algebraic prescription.

No floating-point optimizer is used. Rational inputs only. Generic elimination
is expensive and the character-moment enumeration is factorial-cost. A budget
error is NOT a mathematical answer. n=1, n=2, and scalar n=3 are tested.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable
import sympy as sp
from critical_values import critical_polynomial
from spectral_moments import exact_moment,schur_value,schur_at_ones

class ResourceBudgetExceeded(RuntimeError):
    pass

def moment_order(n: int, upper_bound, gap_lower_bound) -> int:
    B,delta=sp.Rational(upper_bound),sp.Rational(gap_lower_bound)
    if not (n>=1 and B>0 and 0<delta<=B):
        raise ValueError('Require n>=1 and 0<gap<=upper_bound')
    base=1+16*n*n*B/delta
    bits=0
    while 2**bits<base:
        bits+=1
    block=int(sp.ceiling(4*B/delta))
    return 2*n*n*bits*block

def decide_ge(left,right) -> bool:
    relation=sp.Ge(left,right)
    if relation is sp.S.true:return True
    if relation is sp.S.false:return False
    raise NotImplementedError('The installed algebra system did not certify this comparison')

def solve(spectrum: Iterable, *, max_order: int=2, max_moment: int=8,
          max_terms: int=2_000_000) -> dict:
    lam=tuple(sp.Rational(x) for x in spectrum)
    if not lam or any(x<0 for x in lam):
        raise ValueError('Provide a nonempty nonnegative rational spectrum')
    n=len(lam)
    B=max(lam)**n
    if B==0:
        return {'value':sp.S.Zero,'certificate':'zero spectrum'}
    if len(set(lam))==1:
        return {'value':lam[0]**n,'certificate':'scalar spectrum'}
    if n>max_order:
        raise ResourceBudgetExceeded(f'n={n} exceeds the elimination guard {max_order}')
    poly=critical_polynomial(lam)
    all_roots=poly.real_roots(radicals=False)
    roots=[r for r in all_roots if decide_ge(r,0) and decide_ge(B,r)]
    if not roots:raise AssertionError('The true maximum must be a candidate')
    if len(roots)==1:
        return {'value':roots[0],'polynomial':poly.as_expr(),'certificate':'sole candidate'}
    # A rigorously sufficient early exit, often much cheaper than the worst-case p.
    mu1=schur_value((n,),lam)/schur_at_ones((n,),n)
    candidates=[r for r in roots if decide_ge(r,mu1)]
    if len(candidates)==1:
        return {'value':candidates[0],'polynomial':poly.as_expr(),
                'moment_order':1,'moment':mu1,'certificate':'sole candidate above first moment'}
    indices=[i for i,r in enumerate(all_roots) if r in candidates]
    bits=8
    while True:
        intervals=poly.intervals(eps=sp.Rational(1,2**bits))
        brackets=[intervals[i][0] for i in indices]
        delta=min(brackets[i+1][0]-brackets[i][1] for i in range(len(brackets)-1))
        if delta>0:break
        bits*=2
    p=moment_order(n,B,delta)
    if p>max_moment:
        raise ResourceBudgetExceeded(f'Certified moment order {p} exceeds budget {max_moment}; '
                                     'no value returned. Increase budgets only deliberately.')
    mu=exact_moment(lam,p,max_terms)
    qualifying=[r for r in candidates if decide_ge(r**p,mu)]
    if not qualifying:raise AssertionError('Moment selection lost the true maximum')
    return {'value':qualifying[0],'polynomial':poly.as_expr(),'moment_order':p,
            'moment':mu,'gap_lower_bound':delta,'certificate':'finite moment selector'}

if __name__=='__main__':
    import argparse,json
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('spectrum',nargs='+')
    ap.add_argument('--max-order',type=int,default=2)
    ap.add_argument('--max-moment',type=int,default=8)
    ap.add_argument('--max-terms',type=int,default=2_000_000)
    args=ap.parse_args()
    result=solve(args.spectrum,max_order=args.max_order,max_moment=args.max_moment,
                 max_terms=args.max_terms)
    print(json.dumps({k:str(v) for k,v in result.items()},indent=2))
