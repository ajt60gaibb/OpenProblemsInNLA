#!/usr/bin/env python3
"""Exact exploratory search in a remaining n=5 boundary configuration.
The leading singular 2x2 block is fixed, so neither Theorem G nor V applies.
Random choices select rational data/vertices only; every sign test is exact.
Absence of a counterexample is NOT an exhaustive or universal certificate.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import lcm
from pathlib import Path
import argparse,json,random,time
from minor_tools import coordinate_bounds,check_sr,det
ROOT=Path(__file__).resolve().parent
IX=list(combinations(range(5),3))

def det3(A,I,J):
    a,b,c=(A[I[0]][j] for j in J);d,e,f=(A[I[1]][j] for j in J);g,h,i=(A[I[2]][j] for j in J)
    return a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

def main(restarts,steps,vertices,seed):
    rng=random.Random(seed);start=time.monotonic()
    data=json.loads((ROOT/'both_boundary_example.json').read_text());e=data['signature']
    A=[[Q(v) for v in r] for r in data['A_minus']]
    fixed={(i,j) for i in (0,1) for j in (0,1)}
    free=[(i,j) for i in range(5) for j in range(5) if (i,j) not in fixed]
    for power in range(8,40,2):
        eps=Q(1,10**power)
        base=[[A[i][j]+(0 if (i,j) in fixed else eps*(-1)**(i+j)) for j in range(5)] for i in range(5)]
        if check_sr(base,e)['valid']:break
    else:raise AssertionError('Could not obtain promised initial endpoint')
    assert det([[A[i][j] for j in (0,1)] for i in (0,1)])==0
    endpoint_checks=corner_checks=minor_checks=0;trajectory=[];found=None
    for restart in range(restarts):
        B=[r[:] for r in base]
        for step in range(steps):
            i,j=rng.choice(free);lo,hi,_,_=coordinate_bounds(B,e,i,j)
            shift=hi if (i+j)%2==0 else lo
            if shift==0:continue
            if shift is None:shift=Q((-1)**(i+j),1000000)
            C=[r[:] for r in B];C[i][j]+=shift
            if det(C)==0 or rng.randrange(3)==0:
                shift/=2;C=[r[:] for r in B];C[i][j]+=shift
            assert check_sr(C,e)['valid'];endpoint_checks+=1;B=C
            trajectory.append({'restart':restart,'step':step,'entry':[i,j],'shift':str(shift)})
            q=lcm(*(v.denominator for M in (A,B) for row in M for v in row))
            Ai=[[int(q*v) for v in row] for row in A];Bi=[[int(q*v) for v in row] for row in B]
            for _ in range(vertices):
                bits=[rng.randrange(2) for z in free];M=[r[:] for r in Ai]
                for (r,c),bit in zip(free,bits):
                    if bit:M[r][c]=Bi[r][c]
                corner_checks+=1
                for I in IX:
                    for J in IX:
                        d=det3(M,I,J);minor_checks+=1
                        if e[2]*d<0:
                            found={'signature':e,'A_minus':[[str(v) for v in r] for r in A],
                                   'A_plus':[[str(v) for v in r] for r in B],
                                   'witness':[[str(Q(v,q)) for v in r] for r in M],
                                   'bad_rows_0based':I,'bad_cols_0based':J,'bad_determinant':str(Q(d,q**3))}
                            break
                    if found:break
                if found:break
            if found:break
        if found:break
    out={'seed':seed,'requested_restarts':restarts,'requested_steps':steps,'vertices_per_endpoint':vertices,
         'initial_epsilon':str(eps),'exact_endpoint_checks':endpoint_checks,'exact_vertex_checks':corner_checks,
         'exact_order_three_minor_checks':minor_checks,'counterexample':found,'trajectory':trajectory,
         'elapsed_seconds':time.monotonic()-start,
         'scope':'Exploratory finite search; absence of a witness does not prove the conjecture'}
    name=f'fixed_singular_block_search_{seed}.json'
    (ROOT/name).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='trajectory'},indent=2))
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--restarts',type=int,default=8);p.add_argument('--steps',type=int,default=6)
    p.add_argument('--vertices',type=int,default=128);p.add_argument('--seed',type=int,default=20260912)
    a=p.parse_args();main(a.restarts,a.steps,a.vertices,a.seed)
