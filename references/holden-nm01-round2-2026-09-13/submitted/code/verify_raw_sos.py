#!/usr/bin/env python3
"""Second SOS check in the full monomial basis, with no conic reduction.

This rechecks the localizing matrices directly as rational PSD matrices. It is
computational cross-checking, not an independent mathematical audit.
"""
from fractions import Fraction as F
from itertools import combinations
from math import prod
from pathlib import Path
import argparse,json,time
from exact_baseline import matrix,transpose,rational


def psd_rank(A):
    B=[row[:] for row in A]; n=len(B); rank=0
    if any(len(row)!=n for row in B) or any(B[i][j]!=B[j][i] for i in range(n) for j in range(n)):
        raise ValueError('A symmetric square matrix is required.')
    for i in range(n):
        p=B[i][i]
        if p<0: raise ValueError('Negative pivot.')
        if p==0:
            if any(B[i][j] for j in range(i+1,n)):
                raise ValueError('Zero diagonal with nonzero residual row.')
            continue
        rank+=1
        for j in range(i+1,n):
            for k in range(j,n):
                B[j][k]-=B[j][i]*B[i][k]/p
                B[k][j]=B[j][k]
    return rank


def verify(data):
    D=data['degree']; H=matrix(data['H']); Y=matrix(data['evaluation_points'])
    weights=[rational(v) for v in data['weights']]; n=len(H[0]); M=len(Y)
    if not isinstance(D,int) or isinstance(D,bool) or not 2<=D<=8:
        raise ValueError('Degree must be between two and eight.')
    if len(H)!=3 or any(len(y)!=3 or sum(y)!=1 for y in Y) or len(weights)!=M or min(weights)<=0 or sum(weights)!=1:
        raise ValueError('Malformed certificate.')
    cols=transpose(H)
    slacks=[[sum((a*b for a,b in zip(h,y)),F(0)) for h in cols] for y in Y]
    bases={}
    for k in range(D//2+1):
        monomials=[(a,d-a) for d in range(k+1) for a in range(d+1)]
        bases[k]=[[y[0]**a*y[1]**b for a,b in monomials] for y in Y]
    count=0; by_degree={}
    for t in range(min(n,D)+1):
        k=(D-t)//2; basis=bases[k]; dim=len(basis[0])
        for ids in combinations(range(n),t):
            w=[weights[i]*prod(slacks[i][j] for j in ids) for i in range(M)]
            A=[[sum((w[l]*basis[l][i]*basis[l][j] for l in range(M)),F(0))
                for j in range(dim)] for i in range(dim)]
            rk=psd_rank(A)
            if rk!=2*k+1:
                raise ValueError(f'Unexpected rank at subset {ids}: {rk}.')
            count+=1; by_degree[str(k)]={'full_basis_dimension':dim,'matrix_rank':rk}
    lf=sum((w*(1-sum(q*q for q in y)) for w,y in zip(weights,Y)),F(0))
    if lf>=0: raise ValueError('Functional target must be negative.')
    return {'accepted':True,'degree':D,'full_monomial_matrices_checked':count,
            'basis_details':by_degree,'functional_target_value':str(lf),
            'scope':'Direct raw-basis localizing PSD check. Use sos_obstruction.py additionally for family and strong-SSC checks.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',type=Path)
    parser.add_argument('--report',type=Path)
    args=parser.parse_args(); start=time.monotonic()
    result=verify(json.loads(args.certificate.read_text()))
    result['elapsed_seconds']=round(time.monotonic()-start,3)
    if args.report:args.report.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
