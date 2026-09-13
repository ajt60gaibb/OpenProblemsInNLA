#!/usr/bin/env python3
"""Exact projective value-to-factor reduction and exponential test oracle.

The recovery routine uses polynomially many exact value queries. The included
FacetValueOracle is exponential and is NOT a polynomial-time NM-01 solver.
A safe probe scale is required. Tests validate every probe under strong SSC.
SymPy is used for exact polynomial interpolation and factorization.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import combinations
from math import comb, isqrt, prod
from pathlib import Path
from typing import Callable
import json
import sympy as s
from exact_baseline import matrix, matmul, transpose, inverse, determinant, facets, rank
from sos_obstruction import dot, rational_json


def rational_square_root(q: F) -> F:
    if q<0: raise ValueError('Negative square.')
    a=isqrt(q.numerator); b=isqrt(q.denominator)
    if a*a!=q.numerator or b*b!=q.denominator:
        raise ValueError('Oracle ratio is not a rational square.')
    return F(a,b)


def reconstruct_value(decide: Callable[[F],bool], bits: int) -> F:
    """Recover 0<=mu<=2^bits with reduced denominator <=2^bits."""
    if not isinstance(bits,int) or isinstance(bits,bool) or bits<1:
        raise ValueError('A positive integer bit bound is required.')
    lo=F(0); hi=F(2**bits)
    for _ in range(3*bits+4):
        mid=(lo+hi)/2
        if decide(mid): hi=mid
        else: lo=mid
    return ((lo+hi)/2).limit_denominator(2**bits)


class FacetValueOracle:
    """Exponential reference oracle for projective probes of one data matrix.

    Its values are justified only on promised probes. 'observer' is an optional
    test-harness callback, never needed by or passed to the recovery algorithm.
    """
    def __init__(self, Y, delta: F, observer=None):
        self.Y=matrix(Y); self.r=len(Y); self.delta=F(delta)
        self.normals=list(facets(self.Y)); self.candidates=[]
        self.observer=observer; self.cache={}; self.records=[]
        for ids in combinations(range(len(self.normals)),self.r):
            C=[[F(v) for v in self.normals[i]] for i in ids]
            dc=determinant(C)
            if dc:
                self.candidates.append((dc,inverse(transpose(C))))

    def __call__(self, v):
        v=tuple(F(x) for x in v)
        if len(v)!=self.r: raise ValueError('Wrong probe dimension.')
        if v in self.cache: return self.cache[v]
        ell=[1+self.delta*x for x in v]
        if min(dot(ell,y) for y in transpose(self.Y))<=0:
            raise ValueError('Projective denominator is nonpositive.')
        if self.observer: self.observer(ell,self.normals)
        best=None
        for dc,invct in self.candidates:
            scales=[dot(row,ell) for row in invct]
            if min(scales)<=0: continue
            value=1/(dc*prod(scales))**2
            if best is None or value<best: best=value
        if best is None: raise ValueError('No feasible facet candidate.')
        self.records.append({'v':list(v),'value':best})
        self.cache[v]=best
        return best


def recover_from_values(Y, delta: F, value_oracle):
    """Recover T,H from Y=T H, using only exact projective optimal values.

    Correctness requires stronger SSC and a scale preserving it for all probes.
    No hidden factor, support pattern, or facet list is received here.
    """
    Y=matrix(Y); r=len(Y); delta=F(delta)
    if delta<=0 or rank(Y)!=r or any(sum(y)!=1 for y in transpose(Y)):
        raise ValueError('Invalid normalized full-rank input or scale.')
    zero=[F(0)]*r; mu0=value_oracle(zero)
    if mu0<=0: raise ValueError('Nonpositive optimum.')
    def product_value(v):
        return rational_square_root(mu0/value_oracle(v))
    t,z,sv=s.symbols('t z s')
    bound=(r-1)*comb(r,2)
    isolated=None
    for k in range(bound+1):
        b=[F(k**j) for j in range(r)]
        vals=[(j,s.Rational(product_value([j*x for x in b]))) for j in range(r+1)]
        P=s.Poly(s.interpolate(vals,t),t)
        Q=s.Poly(sum(P.nth(j)*z**(r-j) for j in range(r+1)),z)
        _,factors=s.factor_list(Q)
        if any(f.degree()!=1 for f,m in factors):
            raise ValueError('Oracle polynomial does not split over the rationals.')
        roots=[]
        for f,m in factors:
            roots += [-f.nth(0)/f.nth(1)]*m
        if len(roots)==r and len(set(roots))==r:
            isolated=(b,P,Q,roots,k); break
    if isolated is None: raise ValueError('No isolating direction found.')
    b,P,Q,roots,k=isolated
    T=[]
    for coord in range(r):
        Rvals=[]
        for j in range(r):
            vals=[]
            for u in range(r+1):
                v=[j*x+F(u if a==coord else 0) for a,x in enumerate(b)]
                vals.append((u,s.Rational(product_value(v))))
            polynomial=s.Poly(s.interpolate(vals,sv),sv)
            Rvals.append((j,polynomial.nth(1)))
        R=s.Poly(s.interpolate(Rvals,t),t)
        S=s.Poly(sum(R.nth(j)*z**(r-1-j) for j in range(r)),z)
        row=[F(S.eval(root)/(s.Rational(delta)*Q.diff().eval(root))) for root in roots]
        T.append(row)
    if determinant(T)==0 or any(sum(col)!=1 for col in transpose(T)):
        raise ValueError('Recovered factor is singular or unnormalized.')
    H=matmul(inverse(T),Y)
    if min(v for row in H for v in row)<0 or any(sum(col)!=1 for col in transpose(H)):
        raise ValueError('Recovered coefficients are not simplex-valued.')
    if matmul(T,H)!=Y or determinant(T)**2!=mu0:
        raise ValueError('Reconstruction/value identity failed.')
    return {'T':T,'H':H,'optimum':mu0,'isolating_k':k,
            'projection_polynomial':[str(Q.nth(j)) for j in range(r+1)]}


def capped(r: int, u=F(3,4)):
    columns=[]
    for i in range(r):
        for j in range(r):
            if i!=j:
                columns.append([u*F(a==i)+(1-u)*F(a==j) for a in range(r)])
    return transpose(columns)


def strong_probe_observer(T):
    T=matrix(T)
    def check(ell, normals):
        scales=[dot(ell,col) for col in transpose(T)]
        if min(scales)<=0: raise ValueError('Hidden projective scale is nonpositive.')
        for c in normals:
            q=[dot(col,c)/d for col,d in zip(transpose(T),scales)]
            sm=sum(q); gap=sm*sm-dot(q,q)
            if sm<=0 or gap<0:
                raise ValueError('Probe violates SSC1.')
            if gap==0 and not (sum(x!=0 for x in q)==1 and max(q)>0):
                raise ValueError('Probe violates stronger SSC.')
    return check


def demo(r: int=3):
    if r==3:
        T=matrix([[2,0,-1],[0,2,0],[-1,-1,2]])
    elif r==4:
        T=matrix([[2,0,-1,0],[0,2,0,-1],[0,0,2,0],[-1,-1,0,2]])
    else: raise ValueError('Demonstrations are supplied for ranks three and four.')
    H=capped(r); Y=matmul(T,H); delta=F(1,2**24)
    observer=strong_probe_observer(T)
    oracle=FacetValueOracle(Y,delta,observer)
    result=recover_from_values(Y,delta,oracle)
    if sorted(map(tuple,transpose(result['T'])))!=sorted(map(tuple,transpose(T))):
        raise ValueError('Recovered columns differ from generating factor.')
    result.update(schema='nm01-projective-demo-v1',rank=r,delta=delta,Y=Y,
                  generating_T=T,exact_value_queries=len(oracle.records),
                  facet_count=len(oracle.normals),
                  oracle='exponential facet-subset enumeration; not a polynomial solver',
                  each_probe_strong_ssc_checked=True,queries=oracle.records)
    return result


def main():
    import argparse
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--rank',type=int,choices=[3,4],default=3)
    p.add_argument('--output',type=Path)
    p.add_argument('--verify',type=Path)
    args=p.parse_args(); result=demo(args.rank)
    encoded=rational_json(result)
    if args.verify and json.loads(args.verify.read_text())!=encoded:
        raise ValueError('Frozen demonstration differs from regenerated results.')
    if args.output: args.output.write_text(json.dumps(encoded,indent=2)+'\n')
    print(json.dumps({k:v for k,v in encoded.items() if k not in ('Y','H','queries','projection_polynomial')},indent=2))

if __name__=='__main__':main()
