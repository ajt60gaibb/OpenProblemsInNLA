#!/usr/bin/env python3
from fractions import Fraction as Q
from pathlib import Path
import random,json,time
from feedback_solver import solve_feedback
from test_solver import promised_by_vertices,rhs

def main():
    start=time.monotonic();rng=random.Random(81937);logs=[]
    def test(A,x,label):
        A=[[Q(v) for v in r] for r in A];x=[Q(v) for v in x]
        if len(A)<=5:assert promised_by_vertices(A)
        got,log=solve_feedback(A,rhs(A,x));assert got==x
        logs.append({'n':len(A),'label':label,'iterations':log['iterations']})
    for a in [-3,3,Q(100001,100000),Q(-100001,100000)]:
        for x in [0,Q(1,11),Q(-1,13)]:test([[a]],[x],'scalar')
    for n in range(2,13):
        for rep in range(4):
            A=[[Q(0) for j in range(n)] for i in range(n)]
            for i in range(n-1):
                A[i][i]=2;A[i][-1]=2;A[-1][i]=2
                for j in range(i):A[i][j]=-rng.randrange(4)
            x=[Q(rng.randrange(-2,3),rng.randrange(1,8)) for _ in range(n)]
            test(A,x,'nonnegative-inverse triangular Schur family')
    for n in range(2,9):
        for rep in range(4):
            A=[[Q(rng.randrange(-3,4)) if (i==n-1 or j==n-1 or j<=i) else Q(0) for j in range(n)] for i in range(n)]
            for i in range(n):A[i][i]=rng.choice((-1,1))*(2+sum(abs(A[i][j]) for j in range(n) if j!=i))
            x=[Q(rng.randrange(-3,4),rng.randrange(1,8)) for _ in range(n)]
            test(A,x,'mixed-sign triangular diagonal pivots')
    out={'passed':True,'exact_tests':len(logs),'elapsed_seconds':time.monotonic()-start,'tests':logs}
    Path(__file__).with_name('feedback_test_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='tests'},indent=2))
if __name__=='__main__':main()
