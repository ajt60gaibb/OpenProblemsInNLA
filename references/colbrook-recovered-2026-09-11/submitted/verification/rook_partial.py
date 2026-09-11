#!/usr/bin/env python3
"""Exact check of a recovered 5x5 rook-pivoting family at t=1/6.

This is a lower-bound example only, not a proof of a sharp general bound.
"""
from __future__ import annotations
import json
from pathlib import Path
from exact import Q, mat, eye, mm, serial

def verify():
    t=Q(1,6)
    a=mat([[1,0,-Q(1,3),1,1],[0,1,1,-1,1],
           [1,-Q(1,3),1,t,-1],[-1,1,t,1,-1],[-1,-1,1,1,1]])
    u=mat(a); lower=eye(5); pivots=[]; growth=Q(1)
    for k in range(5):
        pivot=u[k][k]
        assert pivot != 0
        assert abs(pivot)==max(abs(v) for v in u[k][k:])
        assert abs(pivot)==max(abs(u[i][k]) for i in range(k,5))
        pivots.append(pivot)
        for i in range(k+1,5):
            ell=u[i][k]/pivot; lower[i][k]=ell;u[i][k]=Q(0)
            for j in range(k+1,5):
                u[i][j]-=ell*u[k][j];growth=max(growth,abs(u[i][j]))
    assert mm(lower,u)==a
    assert growth==Q(893,131)
    assert pivots==[Q(1),Q(1),Q(5,3),Q(131,60),Q(893,131)]
    return {'status':'PASS','scope':'A finite rook-pivoting lower-bound example, not a sharp upper-bound theorem.',
            'parameter_t':t,'A':a,'L':lower,'U':u,'pivots':pivots,'growth':growth,
            'pivot_path':'Diagonal pivots in the displayed original order; ties allowed.'}

if __name__=='__main__':
    if not __debug__: raise RuntimeError('Run without -O: checks use assertions.')
    output=Path(__file__).with_name('rook_results.json')
    output.write_text(json.dumps(serial(verify()),indent=2)+'\n',encoding='utf-8')
    print('Rook partial lower-bound example: PASS')
    print('Saved',output)
