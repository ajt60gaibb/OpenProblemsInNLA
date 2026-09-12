#!/usr/bin/env python3
"""Exact rational solver for regular LOWER-HESSENBERG AVEs.

Structured subclass only, NOT an unrestricted solver for AV-03. The caller
promises nonsingularity of A-diag(d) for every d in [-1,1]^n. The algorithm
neither requests a certificate nor enumerates selectors. See result.md.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import factorial, lcm, ceil
from typing import Sequence
Matrix=list[list[Q]]
Vector=list[Q]

def rational_data(A: Sequence[Sequence[object]],b: Sequence[object])->tuple[Matrix,Vector]:
    n=len(A)
    if n<1 or len(b)!=n or any(len(r)!=n for r in A):
        raise ValueError('A must be nonempty and square and len(b)=n')
    if any(isinstance(v,float) for row in A for v in row) or any(isinstance(v,float) for v in b):
        raise TypeError('Use integers, Fraction, or rational strings, not floats')
    return [[Q(v) for v in r] for r in A],[Q(v) for v in b]

def solve_linear(A: Matrix,b: Vector)->Vector:
    """Gaussian elimination with exact fractions and row pivoting."""
    n=len(A);T=[r[:]+[b[i]] for i,r in enumerate(A)]
    for k in range(n):
        p=next((i for i in range(k,n) if T[i][k]),None)
        if p is None:raise ValueError('Singular selector: regularity promise may fail')
        T[k],T[p]=T[p],T[k]
        for i in range(k+1,n):
            if not T[i][k]:continue
            r=T[i][k]/T[k][k];T[i][k]=Q(0)
            for j in range(k+1,n+1):T[i][j]-=r*T[k][j]
    x=[Q(0)]*n
    for i in range(n-1,-1,-1):
        x[i]=(T[i][n]-sum(T[i][j]*x[j] for j in range(i+1,n)))/T[i][i]
    return x

def height_bound(A: Matrix,b: Vector)->int:
    vals=[v for r in A for v in r]+b
    q=lcm(*(v.denominator for v in vals))
    h=max([1,q]+[abs(int(q*v))+q for r in A for v in r]+[abs(int(q*v)) for v in b])
    return factorial(len(A))*h**len(A)

def evaluate_shooting(A: Matrix,b: Vector,t: Q)->tuple[Vector,Q]:
    n=len(A);x=[t]
    for i in range(n-1):
        if not A[i][i+1]:raise ValueError('Split at zero superdiagonal entries first')
        x.append((b[i]-sum(A[i][j]*x[j] for j in range(i+1))+abs(x[i]))/A[i][i+1])
    return x,sum(A[-1][j]*x[j] for j in range(n))-abs(x[-1])-b[-1]

def verify_solution(A: Matrix,b: Vector,x: Vector)->bool:
    return all(sum(A[i][j]*x[j] for j in range(len(A)))-abs(x[i])==b[i] for i in range(len(A)))

def solve_irreducible(A: Matrix,b: Vector)->tuple[Vector,dict]:
    n=len(A);D=height_bound(A,b)
    C=max([2]+[ceil(abs(v)) for r in A for v in r]+[ceil(1/abs(A[i][i+1])) for i in range(n-1)])
    K=((n+1)*C*C)**max(0,n-1)
    lo=Q(-D-1);hi=Q(D+1)
    xl,gl=evaluate_shooting(A,b,lo);xh,gh=evaluate_shooting(A,b,hi)
    if gl==0:return xl,{'iterations':0,'direct_root':True}
    if gh==0:return xh,{'iterations':0,'direct_root':True}
    if gl*gh>=0:raise ValueError('No bracket: regularity promise may fail')
    steps=0;target=Q(1,2*D*K)
    while hi-lo>target:
        mid=(lo+hi)/2;xm,gm=evaluate_shooting(A,b,mid);steps+=1
        if gm==0:
            assert verify_solution(A,b,xm)
            return xm,{'iterations':steps,'direct_root':True,'D_bits':D.bit_length(),'K_bits':K.bit_length()}
        if (gm>0)==(gl>0):lo=mid;gl=gm
        else:hi=mid;gh=gm
    approx,_=evaluate_shooting(A,b,(lo+hi)/2)
    signs=[1 if v>=0 else -1 for v in approx]
    B=[r[:] for r in A]
    for i,s in enumerate(signs):B[i][i]-=s
    x=solve_linear(B,b)
    if not verify_solution(A,b,x):raise ArithmeticError('Final exact residual check failed')
    return x,{'iterations':steps,'direct_root':False,'D_bits':D.bit_length(),'K_bits':K.bit_length(),'selector':signs}

def solve_ave(A: Sequence[Sequence[object]],b: Sequence[object])->tuple[Vector,dict]:
    A,b=rational_data(A,b);n=len(A)
    if any(A[i][j] for i in range(n) for j in range(i+2,n)):
        raise ValueError('A is not lower Hessenberg')
    ends=[i+1 for i in range(n-1) if not A[i][i+1]]+[n]
    x=[];logs=[];start=0
    for end in ends:
        block=[r[start:end] for r in A[start:end]]
        rhs=[b[i]-sum(A[i][j]*x[j] for j in range(start)) for i in range(start,end)]
        xb,log=solve_irreducible(block,rhs);x.extend(xb)
        logs.append({'range_0based':[start,end],**log});start=end
    assert verify_solution(A,b,x)
    return x,{'dimension':n,'blocks':logs,'exact_verification':True}

if __name__=='__main__':
    A=[[1,Q(1,2),0],[0,1,Q(1,2)],[Q(1,2),0,1]]
    x,log=solve_ave(A,[-2,-2,-2]);print([str(v) for v in x]);print(log)
