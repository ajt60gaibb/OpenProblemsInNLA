"""Exact AV-01 regression tests using Fourier--Motzkin LP feasibility.

Fourier--Motzkin elimination is used ONLY as a small-instance checker.
It is not polynomial time in general. The theorem uses a polynomial-time
rational LP algorithm instead.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse, datetime, json, random, time, traceback
import sympy as sp


def feasible(inequalities, n):
    rows=[(tuple(F(x) for x in a),F(b)) for a,b in inequalities]
    def simplify(rows):
        out={}
        for a,b in rows:
            p=next((abs(x) for x in a if x),None)
            if p is None:
                if b<0:return None
                continue
            aa=tuple(x/p for x in a);bb=b/p
            out[aa]=min(out.get(aa,bb),bb)
        return [(a,b) for a,b in out.items()]
    rows=simplify(rows)
    if rows is None:return False
    for dimension in range(n,0,-1):
        positive=[r for r in rows if r[0][-1]>0]
        negative=[r for r in rows if r[0][-1]<0]
        new=[(a[:-1],b) for a,b in rows if a[-1]==0]
        for a,b in positive:
            for c,d in negative:
                p,q=a[-1],c[-1]
                new.append((tuple(-q*x+p*y for x,y in zip(a[:-1],c[:-1])), -q*b+p*d))
        rows=simplify(new)
        if rows is None:return False
    return True


def recognition(A,b):
    n=len(b)
    if any(v<=0 for v in b):return False
    G=[[F(A[i][j])+s*(i==j) for j in range(n)]
       for s in [1,-1] for i in range(n)]
    recession=[(g,F(0)) for g in G]
    eq=[-sum(A[i][j] for i in range(n)) for j in range(n)]
    recession += [(eq,F(1)),([-x for x in eq],F(-1))]
    if feasible(recession,n):return False
    base=[(G[k],b[k%n]) for k in range(2*n)]
    for i in range(n):
        rows=base+[(A[i],b[i]),([-x for x in A[i]],-b[i])]
        if feasible(rows,n):return False
    return True


def orthant_truth(A,b):
    n=len(b);M=sp.Matrix(A);rhs=sp.Matrix(b)
    for ss in product([-1,1],repeat=n):
        N=M+sp.diag(*ss)
        if N.det()==0:return False
        x=N.inv()*rhs
        if any(ss[i]*x[i]<=0 for i in range(n)):return False
    return True


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--full',action='store_true')
    args=parser.parse_args();rng=random.Random(202609110101)
    result={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'arithmetic':'exact Fraction and SymPy rational',
            'checker':'Fourier--Motzkin feasibility versus all orthants',
            'checker_is_not_a_polynomial_LP_implementation':True}
    out=Path(__file__).resolve().parents[1]/'verification'/'AV-01_exact_results.json'
    start=time.monotonic();counts={};accepted=0
    try:
        cases=[]
        for a in [F(-3),F(-2),F(-1),F(-1,2),F(0),F(1,2),F(1),F(2),F(3)]:
            for b in range(-2,3):cases.append(([[a]],[F(b)]))
        cases.append(([[F(3,5),F(3,5)],[F(-3,5),F(3,5)]],[F(1),F(2)]))
        for n, trials in [(2,700 if args.full else 80),(3,300 if args.full else 30)]:
            for _ in range(trials):
                scale=rng.choice([1,2,4,8,16])
                A=[[F(rng.randrange(-5,6),scale) for j in range(n)] for i in range(n)]
                b=[F(rng.randrange(-1,7)) for i in range(n)]
                cases.append((A,b))
        for A,b in cases:
            got=recognition(A,b);truth=orthant_truth(A,b)
            assert got==truth,(A,b,got,truth)
            n=len(b);counts[str(n)]=counts.get(str(n),0)+1;accepted+=int(got)
        result.update(status='passed',instances=len(cases),dimensions=counts,accepted=accepted)
    except Exception:
        result['status']='failed';result['traceback']=traceback.format_exc();raise
    finally:
        result['elapsed_seconds']=time.monotonic()-start
        result['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
        out.write_text(json.dumps(result,indent=2))
        print(json.dumps(result,indent=2))

if __name__=='__main__':main()
