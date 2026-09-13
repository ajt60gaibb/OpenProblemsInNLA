"""Exact arithmetic supporting the RA-17 continuation. No numerical claims."""
from __future__ import annotations
from fractions import Fraction as F
from math import factorial,comb
from pathlib import Path
import json
import sympy as s
ROOT=Path(__file__).resolve().parents[1]

def degree(d:int,r:int)->int:
    if not (isinstance(d,int) and isinstance(r,int) and 1<=r and 2*r<d):
        raise ValueError('Require integer d,r with 1 <= r and 2r < d')
    c=d-2*r;out=F(1)
    for i in range(c):out*=F(factorial(d+i)*factorial(i),factorial(2*r+i)*factorial(c+i))
    assert out.denominator==1
    return out.numerator

def v2(n:int)->int:
    if n<=0:raise ValueError('valuation requires a positive integer')
    return (n&-n).bit_length()-1

def multiply(a,b,N):
    z=[F(0)]*(N+1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            if i+j<=N:z[i+j]+=x*y
    return z

def sinh_index_coefficient(n):
    # Variable u=z^2: z/sinh(z) is the reciprocal of sum u^j/(2j+1)!.
    N=n-1;f=[F(1,factorial(2*j+1)) for j in range(N+1)];g=[F(1)]+[F(0)]*N
    for k in range(1,N+1):g[k]=-sum(f[j]*g[k-j] for j in range(1,k+1))
    ans=[F(1)]+[F(0)]*N
    for _ in range(2*n-1):ans=multiply(ans,g,N)
    return ans[N]

def measurements(d,r):
    """Integer anti-diagonal moment measurements, flattened in row-major order."""
    if not (1<=r and 2*r<d):raise ValueError('Require 1<=r and 2r<d')
    rows=[];metadata=[]
    for diagonal in range(2*d-1):
        positions=[(i,diagonal-i) for i in range(d) if 0<=diagonal-i<d]
        L=len(positions)
        for power in range(min(2*r,L)):
            row=[0]*(d*d)
            for j,(a,b) in enumerate(positions,1):row[a*d+b]=j**power
            rows.append(row);metadata.append({'anti_diagonal':diagonal,'power':power})
    assert len(rows)==4*r*(d-r)
    return rows,metadata

def main():
    checks=[]
    for d in range(3,65):
        D=degree(d,1)
        formula=F(factorial(2*d-3)*factorial(2*d-4),factorial(d-1)**2*factorial(d-2)**2)
        assert formula==D
        assert v2(D)==2*((d-1).bit_count()-1)
        checks.append({'kind':'rank_two_degree','d':d,'degree':D,'v2':v2(D)})
    for n in range(2,14):
        got=sinh_index_coefficient(n);want=F((-1)**(n-1)*comb(2*n-2,n-1),2**(2*n-2))
        assert got==want
        checks.append({'kind':'index_coefficient','n':n,'value':str(got)})
    for d in range(3,17):
        for r in range(1,(d-1)//2+1):
            D=degree(d,r)
            checks.append({'kind':'degree_parity','d':d,'r':r,'degree':D,
              'critical_continuous_relaxation_exists':D%2==0})
    for d,r in ((3,1),(4,1),(6,1),(6,2),(10,1)):
        W,md=measurements(d,r);M=s.Matrix(W);assert M.rank()==len(W)
        K=M.nullspace();assert len(K)==(d-2*r)**2
        out={'d':d,'r':r,'measurements':W,'metadata':md,
          'kernel_basis':[[str(v) for v in b] for b in K],
          'certificate':'The anti-diagonal Vandermonde proof in the manuscript applies.'}
        (ROOT/f'data/antidiagonal_{d}_{r}.json').write_text(json.dumps(out,indent=2))
        checks.append({'kind':'measurement_rank','d':d,'r':r,'rank':M.rank(),'kernel_dimension':len(K)})
    a,b=s.symbols('a b');h=[s.Integer(1),a]
    for i in range(2,7):h.append(s.Poly(a*h[-1]+b*h[-2],a,b,modulus=2).as_expr())
    G=s.groebner([h[5],h[6]],a,b,modulus=2)
    assert G.reduce(a**8)[1]==0
    q2=a*a+b;q4=a**4+a*a*b+b*b
    w8=s.Poly(q4**2+q2**2*a**4+q2**4,a,b,modulus=2).as_expr()
    assert G.reduce(w8)[1]==0
    checks.append({'kind':'Gr2_R6_top_SW','class_before_reduction':str(w8),'remainder':'0'})
    B=comb(4,2);assert F(B,4)==F(3,2);assert F(B,2)==3
    checks.append({'kind':'six_by_six_indices','kappa_18_half_index':'3/2','kappa_17_total_index':'3'})
    out={'status':'PASS','check_count':len(checks),'checks':checks,
      'scope':'Arithmetic and exported-matrix checks only. Topological proofs are written mathematics, not formalized proofs.'}
    (ROOT/'data/exact_checks.json').write_text(json.dumps(out,indent=2))
    print(json.dumps({'status':out['status'],'check_count':len(checks)},indent=2))
if __name__=='__main__':main()
