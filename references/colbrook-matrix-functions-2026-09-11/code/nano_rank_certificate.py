#!/usr/bin/env python3
"""Exact Q(i) audit of the MF-18 defective example; standard library only.

The certificate checks the Riccati identity, limiting Stein identity, imaginary
rank and the two size-three Jordan blocks of the unregularized pencil.
It does not replace the analytic limiting-graph argument in the manuscript.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import json
from pathlib import Path
from typing import Any

@dataclass(frozen=True)
class QI:
    re: F = F(0)
    im: F = F(0)
    def __post_init__(self):
        object.__setattr__(self, 're', F(self.re))
        object.__setattr__(self, 'im', F(self.im))
    @staticmethod
    def of(x: Any) -> 'QI':
        return x if isinstance(x, QI) else QI(F(x))
    def __add__(self, other):
        b = self.of(other); return QI(self.re+b.re, self.im+b.im)
    __radd__ = __add__
    def __neg__(self): return QI(-self.re, -self.im)
    def __sub__(self, other): return self + (-self.of(other))
    def __rsub__(self, other): return self.of(other) + (-self)
    def __mul__(self, other):
        b=self.of(other)
        return QI(self.re*b.re-self.im*b.im, self.re*b.im+self.im*b.re)
    __rmul__=__mul__
    def __truediv__(self, other):
        b=self.of(other); d=b.re*b.re+b.im*b.im
        if not d: raise ZeroDivisionError('zero Gaussian rational')
        return QI((self.re*b.re+self.im*b.im)/d,
                  (self.im*b.re-self.re*b.im)/d)
    def __rtruediv__(self, other): return self.of(other)/self
    def conj(self): return QI(self.re, -self.im)
    def __bool__(self): return bool(self.re or self.im)
    def pair(self): return [str(self.re), str(self.im)]

def require(test: bool, message: str) -> None:
    if not test: raise ValueError(message)

def matrix(rows): return [[QI.of(x) for x in row] for row in rows]
def eye(n): return matrix([[int(i==j) for j in range(n)] for i in range(n)])
def zeros(m,n): return matrix([[0]*n for _ in range(m)])
def add(a,b): return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def neg(a): return [[-x for x in row] for row in a]
def sub(a,b): return add(a,neg(b))
def trans(a): return [list(row) for row in zip(*a)]
def star(a): return [[x.conj() for x in row] for row in trans(a)]
def mul(a,b):
    bt=trans(b)
    return [[sum((x*y for x,y in zip(row,col)),QI()) for col in bt] for row in a]
def block(a,b,c,d): return [ar+br for ar,br in zip(a,b)]+[cr+dr for cr,dr in zip(c,d)]
def iszero(a): return not any(bool(x) for row in a for x in row)
def equal(a,b): return len(a)==len(b) and all(len(x)==len(y) for x,y in zip(a,b)) and iszero(sub(a,b))
def rank(a):
    x=[row[:] for row in a]; m=len(x); n=len(x[0]); r=0
    for j in range(n):
        pivot=next((i for i in range(r,m) if x[i][j]),None)
        if pivot is None: continue
        x[r],x[pivot]=x[pivot],x[r]
        p=x[r][j]; x[r]=[v/p for v in x[r]]
        for i in range(r+1,m):
            if x[i][j]:
                c=x[i][j]; x[i]=[u-c*v for u,v in zip(x[i],x[r])]
        r+=1
        if r==m: break
    return r

def inv(a):
    n=len(a); x=[ar+br for ar,br in zip(a,eye(n))]
    for j in range(n):
        p=next((i for i in range(j,n) if x[i][j]),None)
        if p is None: raise ValueError('singular matrix')
        x[j],x[p]=x[p],x[j]; z=x[j][j]; x[j]=[u/z for u in x[j]]
        for i in range(n):
            if i!=j and x[i][j]:
                z=x[i][j]; x[i]=[u-z*v for u,v in zip(x[i],x[j])]
    return [r[n:] for r in x]

def det(a):
    x=[r[:] for r in a]; n=len(x); d=QI(1)
    for j in range(n):
        p=next((i for i in range(j,n) if x[i][j]),None)
        if p is None:return QI()
        if p!=j:x[j],x[p]=x[p],x[j];d=-d
        z=x[j][j];d=d*z
        for i in range(j+1,n):
            c=x[i][j]/z
            for k in range(j+1,n):x[i][k]=x[i][k]-c*x[j][k]
    return d

def serialize(a):return [[v.pair() for v in row] for row in a]

def compute():
    h=F(1,2); ii=QI(0,1)
    A=matrix([[-1,0,-h],[0,0,-h],[h,-h,0]])
    Q=matrix([[-2,0,0],[0,0,-1],[0,-1,-1]])
    X=matrix([[-1,0,h],[0,0,-h],[h,-h,QI(-h,h)]])
    H=matrix([[0,0,0],[0,0,0],[0,0,h]])
    S=mul(inv(X),A)
    require(equal(X,trans(X)), 'X is not symmetric')
    require(equal(add(X,mul(trans(A),mul(inv(X),A))),Q), 'Riccati residual nonzero')
    require(equal(S,matrix([[1,0,1],[0,1,ii],[0,0,1]])), 'incorrect S')
    require(equal(sub(X,star(X)),[[2*ii*v for v in row] for row in H]), 'incorrect imaginary part')
    require(equal(mul(star(S),mul(H,S)),H), 'limiting Stein identity fails')
    require(rank(H)==1, 'wrong imaginary rank')
    require(det(X)==QI(F(1,4)), 'wrong determinant X')
    require(det(A)==QI(F(1,4)), 'wrong determinant A')
    O=zeros(3,3); I=eye(3)
    M=block(A,O,Q,neg(I)); L=block(O,I,trans(A),O)
    J=mul(inv(L),M); N=sub(J,eye(6))
    N2=mul(N,N); N3=mul(N2,N)
    ranks=[rank(N),rank(N2),rank(N3)]
    require(ranks==[4,2,0], 'pencil does not have two size-three Jordan blocks')
    # N^3=0 plus ranks 4,2,0 means precisely two blocks, both of size three.
    # det(A^T)=1/4 then gives det P(lambda)=(lambda-1)^6/4.
    vplus=matrix([[1],[ii],[0]]); vminus=matrix([[1],[-ii],[0]])
    vprime=matrix([[0],[0],[ii]])
    upper=[ [vplus[k][0],vprime[k][0],vminus[k][0]] for k in range(3)]
    C0=sub(Q,trans(A))
    lowerplus=mul(C0,vplus); lowerminus=mul(C0,vminus)
    lowerprime=sub(mul(C0,vprime),[[ii*v for v in row] for row in mul(trans(A),vplus)])
    lower=[[lowerplus[k][0],lowerprime[k][0],lowerminus[k][0]] for k in range(3)]
    require(bool(det(upper)), 'limiting graph upper block singular')
    require(equal(mul(lower,inv(upper)),X), 'limiting graph gives a different X')
    return {
      'problem':'MF-18', 'arithmetic':'exact Gaussian rational; Python standard library',
      'A':serialize(A),'Q':serialize(Q),'X':serialize(X),'S':serialize(S),
      'H_rank':rank(H),'det_X':det(X).pair(),'det_A':det(A).pair(),
      'linearization_nilpotent_power_ranks':ranks,
      'unit_circle_eigenvalue':'1','Jordan_block_sizes':[3,3],
      'predicted_rank':1,'actual_rank':1,
      'limiting_graph_upper_determinant':det(upper).pair(),
      'Riccati_residual':'exactly zero','limiting_Stein_residual':'exactly zero',
      'note':'The general rank theorem and convergence to this graph require the analytic proof.'
    }

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=Path('nano_rank_certificate.json'))
    p.add_argument('--verify',action='store_true')
    args=p.parse_args(); result=compute()
    if args.verify:
        old=json.loads(args.output.read_text())
        require(old==result,'stored certificate differs from exact recomputation')
        print('PASS: exact Riccati, Stein, rank, Jordan structure and limiting graph checks')
    else:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
        print(f'Wrote {args.output}')
if __name__=='__main__':main()
