#!/usr/bin/env python3
"""Exact rational verification of the displayed obstruction certificates."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import sys,json
from hessenberg_solver import solve_linear
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'IV-01'))
from minor_tools import det

def selected(A,s,b):
    B=[r[:] for r in A]
    for i in range(len(A)):B[i][i]-=s[i]
    return solve_linear(B,b)

def main():
    A=[[Q(1),Q(1,2),Q(0)],[Q(0),Q(1),Q(1,2)],[Q(1,2),Q(0),Q(1)]];b=[Q(-2)]*3
    cycle=[(-1,-1,1),(-1,1,-1),(1,-1,-1)];points=[]
    for i,s in enumerate(cycle):
        x=selected(A,s,b);points.append(x)
        assert tuple(1 if v>0 else -1 for v in x)==cycle[(i+1)%3]
        assert all(v!=0 for v in x)
    ss=[(-1,-1,-1),(-1,1,1),(1,-1,1),(1,1,-1)]
    weights=[Q(5,8),Q(1,8),Q(1,8),Q(1,8)]
    ys=[selected(A,s,b) for s in ss]
    assert sum(weights)==1
    assert all(sum(w*y[j] for w,y in zip(weights,ys))==0 for j in range(3))
    ds=[]
    for s in product((-1,1),repeat=3):
        B=[r[:] for r in A]
        for i in range(3):B[i][i]-=s[i]
        ds.append(det(B))
    assert all(d>0 for d in ds)
    tents=[]
    for n in range(2,11):
        seen=set();params=[]
        for s in product((-1,1),repeat=n):
            x=[Q(0)]*n;x[-1]=Q(s[-1],2)
            for i in range(n-2,-1,-1):x[i]=s[i]*(1-x[i+1])/2
            assert tuple(1 if v>0 else -1 for v in x)==s
            assert all(1-2*abs(x[i])==x[i+1] for i in range(n-1))
            assert -1<x[0]<1
            seen.add(x[0]);params.append(2**n*x[0]-abs(x[-1]))
        assert len(seen)==2**n and len(set(params))==2**n
        tents.append({'n':n,'exact_itineraries_verified':2**n})
    out={'passed':True,'newton_cycle':[[str(v) for v in x] for x in points],
         'hull_points':[[str(v) for v in x] for x in ys],'weights':[str(v) for v in weights],
         'selector_determinants':[str(v) for v in ds],'tent_tests':tents}
    Path(__file__).with_name('obstruction_certificates.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
