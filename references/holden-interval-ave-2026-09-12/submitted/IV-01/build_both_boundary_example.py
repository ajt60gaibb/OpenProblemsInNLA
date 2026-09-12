#!/usr/bin/env python3
"""Reconstruct a mixed-parity interval with BOTH endpoints non-strict SR.
The signature is (++-+-); the endpoint zero minors have orders two and three.
No numerical tolerances are used. The result is positive, not a counterexample.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,time
from minor_tools import all_minors,coordinate_bounds,check_sr,det,vandermonde_sr
from graph_criterion import fixed_graph_certificate
ROOT=Path(__file__).resolve().parent

def main():
    start=time.monotonic();e=[1,1,-1,1,-1];n=5;fixed={(0,0),(0,1)}
    H=vandermonde_sr(n,e,Q(1,10))
    lo,_,_,_=coordinate_bounds(H,e,0,0)
    assert lo is not None
    A=[r[:] for r in H];A[0][0]+=lo
    assert check_sr(A,e)['valid']
    step=Q(1,10**8)
    B=[[A[i][j]+(Q(0) if (i,j) in fixed else step*(-1)**(i+j)) for j in range(n)] for i in range(n)]
    midcheck=check_sr(B,e)
    assert midcheck['valid'] and not any(v['zero'] for v in midcheck['minor_counts'].values())
    _,shift,_,_=coordinate_bounds(B,e,0,2)
    assert shift is not None and shift>0
    C=[r[:] for r in B];C[0][2]+=shift
    ac,bc=check_sr(A,e),check_sr(C,e)
    assert ac['valid'] and bc['valid']
    za=[(I,J) for I,J,v in all_minors(A) if v==0]
    zb=[(I,J) for I,J,v in all_minors(C) if v==0]
    assert za and zb and any(len(I)==2 for I,J in za) and any(len(I)==3 for I,J in zb)
    assert all(v>0 for M in [A,C] for row in M for v in row)
    cert=fixed_graph_certificate(A,C,1);assert cert['criterion_applies']
    assert {(i,j) for i in range(n) for j in range(n) if A[i][j]==C[i][j]}==fixed
    r,c=cert['row_potentials'],cert['column_potentials']
    for power in range(2,70,2):
        t=Q(1,10**power)
        Ct=[[(1+t)**(r[i]+c[j])*C[i][j] for j in range(n)] for i in range(n)]
        if all((-1)**(i+j)*(Ct[i][j]-A[i][j])>0 for i in range(n) for j in range(n)):break
    else:raise AssertionError('No small scaling parameter found')
    assert check_sr(Ct,e)['valid']
    out={'signature':e,'A_minus':[[str(v) for v in row] for row in A],
         'A_plus':[[str(v) for v in row] for row in C],
         'base_formula':'z_i=(i+1)/6; lambda=(1,1/10,-1/100,-1/1000,-1/10000); H_ij=sum_k lambda_k*(z_i*z_j)^k',
         'lower_boundary_entry_0based':[0,0],'lower_boundary_shift':str(lo),
         'checker_step':str(step),'upper_boundary_entry_0based':[0,2],
         'upper_boundary_shift':str(shift),'fixed_entries_0based':sorted(fixed),
         'zero_minors_A':za,'zero_minors_B':zb,'A_check':ac,'B_check':bc,
         'graph_certificate':cert,'scaling_t':str(t),'strict_checker_order_after_scaling':True,
         'elapsed_seconds':time.monotonic()-start}
    (ROOT/'both_boundary_example.json').write_text(json.dumps(out,indent=2)+'\n')
    for name,M in [('A_both_boundary',A),('B_both_boundary',C)]:
        data=[{'rows_0based':I,'cols_0based':J,'determinant':str(v),
               'signed_determinant':str(e[len(I)-1]*v)} for I,J,v in all_minors(M)]
        (ROOT/(name+'_all_minors.json')).write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:out[k] for k in ['signature','lower_boundary_shift','upper_boundary_shift',
           'zero_minors_A','zero_minors_B','A_check','B_check','elapsed_seconds']},indent=2))
if __name__=='__main__':main()
