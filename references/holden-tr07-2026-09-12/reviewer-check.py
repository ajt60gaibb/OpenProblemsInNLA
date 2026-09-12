"""Independent exact checks for TR-07; finite diagnostics, not a proof."""
from fractions import Fraction as F
from collections import defaultdict
from itertools import product
U=[(1,1,0),(1,-1,0),(0,1,1),(1,0,-1)]
mu=[F(1,2),F(1,6),F(1,4),F(1,12)]
k=3;s=2
p=[sum(q for u,q in zip(U,mu) if u[i]) for i in range(k)]
Sigma=[[sum(q*u[i]*u[j] for u,q in zip(U,mu)) for j in range(k)] for i in range(k)]
T=[[Sigma[i][j]/p[j] for j in range(k)] for i in range(k)]
def mv(A,x):return tuple(sum(a*b for a,b in zip(row,x)) for row in A)
def norm2(x):return sum(t*t for t in x)
def ideal(v):
    d=defaultdict(F)
    for i in range(k):
        if v[i]:
            for w,q in zip(U,mu):
                if w[i]:d[tuple(v[i]*w[i]*z for z in w)]+=F(1,s)*q/p[i]
    return dict(d)
for v in U+ [tuple(-z for z in u) for u in U]:
    law=ideal(v)
    assert sum(law.values())==1
    assert tuple(sum(q*w[i] for w,q in law.items()) for i in range(k))==tuple(t/s for t in mv(T,v))
B=[[F(i==j)-T[i][j]/s for j in range(k)] for i in range(k)]
for L in range(1,9):
    err=F(0)
    for u,q in zip(U,mu):
        v=u
        for _ in range(L):v=mv(B,v)
        err+=q*norm2(v)
    assert err<=F(s*s,2*L+1)
# Independently enumerate actual length-two chunk first hits, keeping paths.
ell=2
a=min(1-(1-pi)**ell for pi in p)
def actual(v):
    d=defaultdict(F)
    for i in range(k):
        if not v[i]:continue
        for inds in product(range(len(U)),repeat=ell):
            prob=F(1,s)
            for ind in inds:prob*=mu[ind]
            w=next((U[ind] for ind in inds if U[ind][i]),None)
            if w is not None:d[tuple(v[i]*w[i]*z for z in w)]+=prob
    return dict(d)
strict_conditioning_difference=False
for u in U:
    paths_i={};paths_a={}
    for v,q in ideal(u).items():
        for w,t in ideal(v).items():paths_i[v,w]=q*t
    for v,q in actual(u).items():
        for w,t in actual(v).items():paths_a[v,w]=q*t
    assert all(paths_a.get(path,0)>=a*a*q for path,q in paths_i.items())
    mass=sum(paths_a.values())
    if any(paths_a.get(path,0)/mass!=q for path,q in paths_i.items()):strict_conditioning_difference=True
assert strict_conditioning_difference
# Exact one-step collision replacement marginal and collision expectation.
for n in range(1,11):
    for r in range(1,n+1):
        expected=F(0)
        for t in range(1,r+1):
            assert F(1,n)+F(t-1,n)*F(1,n-t+1)==F(1,n-t+1)
            expected+=F(t-1,n)
        assert expected==F(r*(r-1),2*n)
print('PASS: signed transition, covariance filter L=1..8, adaptive path domination, conditional-law mismatch, collision marginals n<=10.')
