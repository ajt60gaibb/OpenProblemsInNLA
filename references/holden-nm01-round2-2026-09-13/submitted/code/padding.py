#!/usr/bin/env python3
"""Lift a rank-three SOS obstruction by a direct sum with an identity block."""
from fractions import Fraction as F
from pathlib import Path
from math import comb
import json
from exact_baseline import matrix, transpose, rank
from sos_obstruction import rational_json


def padded_instance(data):
    H=matrix(data['H']); D=data['degree']; r=len(H[0]); n=2*r-3
    if len(H)!=3 or r!=2*D+1:
        raise ValueError('Expected the standard rank-three obstruction family.')
    out=[[F(0)]*n for _ in range(r)]
    for i in range(3):
        out[i][:r]=H[i]
    for i in range(3,r):
        out[i][r+i-3]=F(1)
    if rank(out)!=r or any(sum(col)!=1 for col in transpose(out)):
        raise ValueError('Padding rank/normalization check failed.')
    order=D//2+1
    return {'schema':'nm01-padded-obstruction-v1','degree_excluded':D,
            'rank':r,'columns':n,'H':out,'known_optimum':1,
            'first_dense_order_not_excluded':order,
            'dense_monomial_count_at_that_order':comb(r-1+order,order),
            'proof_obligation':'Base certificate must pass sos_obstruction.py; restriction to coordinates q4=...=qr=0 transfers the degree exclusion.',
            'claim':'A dense hierarchy size obstruction, not computational hardness of these inputs.'}

if __name__=='__main__':
    root=Path(__file__).resolve().parents[1]
    rows=[]
    for D in (4,6,8):
        src=root/'certificates'/f'sos_degree{D}_strong.json'
        data=padded_instance(json.loads(src.read_text()))
        out=root/'certificates'/f'padded_degree{D}.json'
        out.write_text(json.dumps(rational_json(data),indent=2)+'\n')
        rows.append({k:v for k,v in data.items() if k not in ('H','proof_obligation','claim','schema')})
    print(json.dumps(rows,indent=2))
