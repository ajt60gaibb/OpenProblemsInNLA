#!/usr/bin/env python3
"""Exact solver for the second scalar-shooting class in general_reductions.md.

The leading (n-1)-square block must be lower triangular with |a_ii|>1.
The whole diagonal family is promised regular. The last row/column are free.
"""
from fractions import Fraction as Q
from math import ceil
from hessenberg_solver import rational_data,height_bound,solve_linear,verify_solution

def evaluate_feedback(A,b,t):
    n=len(A);x=[]
    for i in range(n-1):
        c=b[i]-A[i][-1]*t-sum(A[i][j]*x[j] for j in range(i))
        if c==0:x.append(Q(0))
        else:
            s=1 if c*A[i][i]>0 else -1
            x.append(c/(A[i][i]-s))
    x.append(t)
    return x,sum(A[-1][j]*x[j] for j in range(n))-abs(t)-b[-1]

def solve_feedback(A,b):
    A,b=rational_data(A,b);n=len(A)
    if any(A[i][j] for i in range(n-1) for j in range(i+1,n-1)):
        raise ValueError('Leading block is not lower triangular')
    if any(abs(A[i][i])<=1 for i in range(n-1)):
        raise ValueError('Leading scalar equations are not individually invertible')
    D=height_bound(A,b)
    C=max([2]+[ceil(abs(v)) for r in A for v in r]+[ceil(1/(abs(A[i][i])-1)) for i in range(n-1)])
    K=((n+1)*C*C)**max(0,n-1)
    lo=Q(-D-1);hi=Q(D+1)
    xl,gl=evaluate_feedback(A,b,lo);xh,gh=evaluate_feedback(A,b,hi)
    if gl==0:return xl,{'iterations':0,'direct_root':True}
    if gh==0:return xh,{'iterations':0,'direct_root':True}
    if gl*gh>=0:raise ValueError('No bracket: regularity promise may fail')
    count=0
    while hi-lo>Q(1,2*D*K):
        mid=(lo+hi)/2;x,gm=evaluate_feedback(A,b,mid);count+=1
        if gm==0:
            assert verify_solution(A,b,x)
            return x,{'iterations':count,'direct_root':True}
        if (gm>0)==(gl>0):lo=mid;gl=gm
        else:hi=mid;gh=gm
    approx,_=evaluate_feedback(A,b,(lo+hi)/2)
    signs=[1 if v>=0 else -1 for v in approx]
    B=[r[:] for r in A]
    for i,s in enumerate(signs):B[i][i]-=s
    x=solve_linear(B,b)
    if not verify_solution(A,b,x):raise ArithmeticError('Final exact residual failed')
    return x,{'iterations':count,'direct_root':False,'D_bits':D.bit_length(),'K_bits':K.bit_length(),'selector':signs}

if __name__=='__main__':
    A=[[2,0,0,2],[0,2,0,2],[0,0,2,2],[2,2,2,0]]
    print(solve_feedback(A,[1,2,3,4]))
