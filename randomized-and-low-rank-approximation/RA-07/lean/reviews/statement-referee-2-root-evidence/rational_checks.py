"""Independent exact statement diagnostics; no inference of universal truth."""
from fractions import Fraction as F
from itertools import combinations
from math import prod,factorial
from pathlib import Path
import json

def esym(xs,j):return sum((prod(s,start=F(1)) for s in combinations(xs,j)),start=F(0))
def poly(xs):
    out=[F(1)]
    for x in xs:
        nxt=[F(0)]*(len(out)+1)
        for i,c in enumerate(out):nxt[i]+=c;nxt[i+1]+=x*c
        out=nxt
    return out
def diff(cs):return [F(i)*c for i,c in enumerate(cs) if i] or [F(0)]
def iterate(cs,d):
    for _ in range(d):cs=diff(cs)
    return cs
def seq(xs,j):return F(j+1)*esym(xs,j+1)/esym(xs,j)
rows=[]
for n in range(8):
    samples=[[F(3,7)]*n,[F(i+1,i+2) for i in range(n)],[F((-1)**i*i,3) for i in range(n)]]
    for xs in samples:
        cs=poly(xs)
        for j in range(n+3):
            assert (cs[j] if j<len(cs) else F(0))==esym(xs,j)
            assert iterate(cs,j)[0]==factorial(j)*esym(xs,j)
        if all(x>0 for x in xs):
            for d in range(n+1):
                q=iterate(cs,d)
                assert len(q)-1==n-d and q[-1]>0 and q[0]>0
            for j in range(2,n):assert seq(xs,j-1)-2*seq(xs,j)+seq(xs,j+1)>=0
            if len(set(xs))<=1:
                for d in range(n+1):
                    q=iterate(cs,d)
                    mus=[F(3,7)]*(n-d) if not xs else [xs[0]]*(n-d)
                    assert q==[q[0]*x for x in poly(mus)]
        rows.append({'n':n,'tuple':list(map(str,xs)),'coefficient_derivative_checks':n+3,'positive_tuple':all(x>0 for x in xs)})
pairrows=[]
for m in range(2,9):
    for mu in [[F(2,5)]*m,[F(a+1,a+3) for a in range(m)]]:
        s1,s2,s3=[sum((x**r for x in mu),start=F(0)) for r in [1,2,3]]
        gap=sum((a*b*(a-b)**2 for a,b in combinations(mu,2)),start=F(0))
        den=s1*(s1*s1-s2)
        assert den>0 and gap>=0 and s1*s3-s2*s2==gap
        q=poly(mu)
        q0,q1,q2,q3=[iterate(q,d)[0] for d in range(4)]
        assert (q1/q0,q2/q0,q3/q0)==(s1,s1*s1-s2,s1**3-3*s1*s2+2*s3)
        assert q1/q0-2*q2/q1+q3/q2==2*gap/den
        if m==2:assert q3==0
        pairrows.append({'m':m,'mu':list(map(str,mu)),'denominator':str(den),'pair_gap':str(gap),'second_difference':str(2*gap/den)})
result={'status':'PASS','scope':'Finite exact diagnostic checks only; derivative real-rootedness/factorization in general and universal convexity remain proof obligations','subset_polynomial_cases':rows,'power_sum_cases':pairrows,'empty_dimension_and_constant_derivative_included':True,'degree_two_endpoint_included':True}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','tuple_cases':len(rows),'pair_cases':len(pairrows),'scope':result['scope']}))
