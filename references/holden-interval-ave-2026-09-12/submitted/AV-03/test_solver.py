#!/usr/bin/env python3
"""Exact adversarial and randomized tests. Tests are not the general proof."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
from math import factorial
import json,random,time,sys
from hessenberg_solver import solve_ave,solve_linear,verify_solution
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'IV-01'))
from minor_tools import det

def rhs(A,x):return [sum(A[i][j]*x[j] for j in range(len(x)))-abs(x[i]) for i in range(len(x))]
def promised_by_vertices(A):
    n=len(A);sign=None
    for s in product((-1,1),repeat=n):
        B=[r[:] for r in A]
        for i in range(n):B[i][i]-=s[i]
        d=det(B)
        if not d:return False
        if sign is None:sign=d>0
        if (d>0)!=sign:return False
    return True

def main():
    start=time.monotonic();rng=random.Random(20260912);logs=[]
    def check(A,x,label,enumerate_promise=False):
        A=[[Q(v) for v in r] for r in A];x=[Q(v) for v in x]
        if enumerate_promise:assert promised_by_vertices(A)
        b=rhs(A,x);got,log=solve_ave(A,b);assert got==x;assert verify_solution(A,b,got)
        logs.append({'label':label,'n':len(A),'iterations':sum(v['iterations'] for v in log['blocks']),
                     'blocks':len(log['blocks']),'vertex_promise_checked':enumerate_promise})
    for a in [-5,-2,Q(-1001,1000),Q(1001,1000),2,5]:
        for x in [0,Q(1,7),Q(-3,11)]:check([[a]],[x],'scalar',True)
    for n in range(2,9):
        for trial in range(8):
            A=[[Q(rng.randrange(-4,5),rng.randrange(1,5)) if j<=i+1 else Q(0) for j in range(n)] for i in range(n)]
            for i in range(n):
                A[i][i]=rng.choice((-1,1))*(2+sum(abs(A[i][j]) for j in range(n) if j!=i))
            x=[Q(rng.randrange(-3,4),rng.randrange(1,8)) for i in range(n)]
            check(A,x,'strict row diagonal dominance',n<=5)
    A=[[1,Q(1,2),0],[0,1,Q(1,2)],[Q(1,2),0,1]]
    check(A,[Q(-4,5)]*3,'Newton-cycle family',True)
    check(A,[0,Q(1,10**20),Q(-1,10**21)],'tiny nonzero coordinates and a zero',True)
    check([[2,0,0,0],[3,-2,1,0],[4,2,5,0],[7,1,0,-3]],[0,Q(2,3),-1,0],'reducible Hessenberg blocks',True)
    for n in [2,3,5,8,12,20]:
        A=[[Q(0) for j in range(n)] for i in range(n)]
        for i in range(n-1):A[i][i+1]=Q(-1,2)
        A[n-1][0]=2**n
        x=[Q(3,17)]
        for i in range(n-1):x.append(1-2*abs(x[-1]))
        check(A,x,'exponential-sign-region family',n<=5)
    # Non-diagonally-dominant random promised Hessenberg matrices.
    found=0
    for trial in range(1000):
        n=4
        A=[[Q(rng.randrange(-4,5)) if j<=i+1 else Q(0) for j in range(n)] for i in range(n)]
        if not promised_by_vertices(A):continue
        x=[Q(rng.randrange(-2,3),rng.randrange(1,6)) for _ in range(n)]
        check(A,x,'arbitrary promised random Hessenberg',True);found+=1
        if found==25:break
    assert found==25
    for A,b in [([],[]),([[1,0,1],[0,2,0],[0,0,2]],[0,0,0]),([[2.0]],[0])]:
        try:solve_ave(A,b)
        except (ValueError,TypeError):pass
        else:raise AssertionError('Invalid input was not rejected')
    out={'passed':True,'exact_tests':len(logs),'elapsed_seconds':time.monotonic()-start,'tests':logs}
    Path(__file__).with_name('test_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='tests'},indent=2))
if __name__=='__main__':main()
