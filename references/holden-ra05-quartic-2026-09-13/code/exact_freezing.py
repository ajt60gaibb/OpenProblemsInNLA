"""Exact demonstration of frozen fractional exceptions.

This small example preserves ALL quartic moments by nullspace elimination.
It is not the low-codimension, small-discrepancy oracle in the size theorem.
"""
from __future__ import annotations
from fractions import Fraction as F
import sympy as sp


def exponents(d: int, degree: int):
    if d==1:
        yield (degree,)
    else:
        for j in range(degree+1):
            for rest in exponents(d-1,degree-j):
                yield (j,)+rest


def feature(row):
    out=[1]
    for powers in exponents(len(row),4):
        value=1
        for x,p in zip(row,powers): value*=x**p
        out.append(value)
    return out


def one_coloring(columns):
    n=len(columns); x=[F(0)]*n; active=list(range(n)); moves=0
    while active:
        matrix=sp.Matrix.hstack(*[sp.Matrix(columns[i]) for i in active])
        kernel=matrix.nullspace()
        if not kernel: break
        v=[F(int(z.p),int(z.q)) for z in kernel[0]]
        choices=[]
        for i,vi in zip(active,v):
            if vi>0: choices.append((1-x[i])/vi)
            elif vi<0: choices.append((-1-x[i])/vi)
        step=min(choices)
        assert step>0
        for i,vi in zip(active,v):
            x[i]+=step*vi
            assert -1<=x[i]<=1
        new=[i for i in active if abs(x[i])!=1]
        assert len(new)<len(active)
        active=new; moves+=1
    m=len(columns[0])
    assert all(sum(x[i]*columns[i][j] for i in range(n))==0 for j in range(m))
    assert len(active)<=m
    return x,moves


def run(rows):
    fs=[feature(row) for row in rows]
    n=len(rows); target=len(fs[0]); active=list(range(n)); eta=F(1,n)
    frozen={}; stages=[]
    while len(active)>target:
        old=list(active)
        x,moves=one_coloring([fs[i] for i in old])
        active=[]; fractional=[]
        for i,xi in zip(old,x):
            if xi==1: active.append(i)
            elif xi==-1: pass
            else:
                mass=eta*(1+xi)
                frozen[i]=frozen.get(i,F(0))+mass
                fractional.append(i)
        assert len(active)<=len(old)//2
        assert len(fractional)<=target
        stages.append({'copies_before':len(old),'full_positive':len(active),
                       'fractional_frozen':len(fractional),'nullspace_moves':moves,'common_mass':str(eta)})
        eta*=2
    final=dict(frozen)
    for i in active: final[i]=final.get(i,F(0))+eta
    weights=[final.get(i,F(0))*n for i in range(n)]
    assert all(w>=0 for w in weights)
    for j in range(target):
        assert sum(weights[i]*fs[i][j] for i in range(n))==sum(fs[i][j] for i in range(n))
    return {'rows':rows,'weights':[str(w) for w in weights], 'dimension':len(rows[0]),
            'moment_count_including_mass':target,'original_rows':n,
            'retained_rows':sum(w!=0 for w in weights),'stages':stages,
            'exact_all_quartic_moments':True,
            'scope':'Exact bookkeeping example with full moment constraints, not an implementation of the asymptotic partial-coloring oracle.'}
