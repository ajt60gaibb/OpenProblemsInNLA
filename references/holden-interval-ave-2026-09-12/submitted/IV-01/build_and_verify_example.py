#!/usr/bin/env python3
"""Construct and exactly audit a mixed-parity, n=5 interval.

The lower checker vertex has a zero order-three minor. Its signature (+++-+)
is outside the 16 periodic/final-flip signatures listed in the canonical
survey. Only two entries are fixed, one of each parity. This is an example
covered by our graph criterion, NOT a counterexample to IV-01.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
import json,random,time
from minor_tools import *
from graph_criterion import fixed_graph_certificate
ROOT=Path(__file__).resolve().parent

def encode(A):return [[str(v) for v in r] for r in A]

def main():
    start=time.monotonic();n=5;e=[1,1,1,-1,1]
    base=vandermonde_sr(n,e,Q(1,10))
    lo,hi,low,up=coordinate_bounds(base,e,0,0)
    if lo is None:raise AssertionError('Expected finite lower boundary')
    A=[r[:] for r in base];A[0][0]+=lo
    acheck=check_sr(A,e);assert acheck['valid']
    fixed={(0,0),(0,1)}
    E=[[Q(0) if (i,j) in fixed else Q((-1)**(i+j)) for j in range(n)] for i in range(n)]
    zeros=[(I,J) for I,J,d in all_minors(A) if not d]
    assert zeros and any(len(I)==3 for I,J in zeros)
    for power in range(4,60,2):
        step=Q(1,10**power)
        B=[[A[i][j]+step*E[i][j] for j in range(n)] for i in range(n)]
        bcheck=check_sr(B,e)
        if bcheck['valid'] and not any(v['zero'] for v in bcheck['minor_counts'].values()):break
    else:raise AssertionError('No positive perturbation found')
    cert=fixed_graph_certificate(A,B,e[0]);assert cert['criterion_applies']
    assert {(i,j) for i in range(n) for j in range(n) if A[i][j]==B[i][j]}==fixed
    assert all(v>0 for row in A for v in row)
    r,c=cert['row_potentials'],cert['column_potentials']
    for p in range(2,70,2):
        t=Q(1,10**p)
        Bt=[[(1+t)**(r[i]+c[j])*B[i][j] for j in range(n)] for i in range(n)]
        if all((-1)**(i+j)*(Bt[i][j]-A[i][j])>0 for i in range(n) for j in range(n)):break
    else:raise AssertionError('Scaling did not open the fixed entries')
    assert check_sr(Bt,e)['valid']
    out={'signature':e,'A_minus':encode(A),'A_plus':encode(B),'base_shave':str(lo),
         'base_formula':'x_i=(i+1)/6; lambda=(1,1/10,1/100,-1/1000,-1/10000); base_ij=sum_k lambda_k*(x_i*x_j)^k',
         'step':str(step),'fixed_entries_0based':sorted(fixed),'zero_minors_A':zeros,
         'A_check':acheck,'B_check':bcheck,'graph_certificate':cert,
         'scaling_t':str(t),'scaled_B':encode(Bt),'strict_checker_order_after_scaling':True}
    # Additional samples are tests, not the proof of the universal interval claim.
    rng=random.Random(20260912);sample_checks=[]
    for z in range(24):
        M=[[A[i][j]+Q(rng.randrange(5),4)*(B[i][j]-A[i][j]) for j in range(n)] for i in range(n)]
        chk=check_sr(M,e);assert chk['valid'];sample_checks.append(chk['minor_counts'])
    out['sample_tests_count']=len(sample_checks)
    out['elapsed_seconds']=time.monotonic()-start
    (ROOT/'mixed_parity_example.json').write_text(json.dumps(out,indent=2)+'\n')
    # Every minor is an independently inspectable exact rational certificate.
    for name,C in [('A_minus',A),('A_plus',B)]:
        data=[{'rows_0based':I,'cols_0based':J,'determinant':str(v),
               'signed_determinant':str(e[len(I)-1]*v)} for I,J,v in all_minors(C)]
        (ROOT/(name+'_all_minors.json')).write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'signature':e,'step':str(step),'zero_minors_A':zeros,
                      'A_check':acheck,'B_check':bcheck,'graph_certificate':cert,
                      'scaling_t':str(t),'sample_tests':24,'elapsed_seconds':out['elapsed_seconds']},indent=2))
if __name__=='__main__':main()
