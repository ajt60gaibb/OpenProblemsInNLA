#!/usr/bin/env python3
"""Exact tests of construction identities and combinatorial formula consistency."""
from __future__ import annotations
import json
from math import comb
from pathlib import Path
import sympy as sp
from constructions import (antidiagonal_measurements, hurwitz_basis,
                           xu_octonion_lift, annihilating_measurements)
from bounds import (bounds, rho, degree, degree_valuation, v2,
                    schur_dimension_valuation, rectangle_dimension)

ROOT=Path(__file__).resolve().parents[1]

def require(condition, message):
    if not condition: raise AssertionError(message)

def main():
    cases=0
    for d in range(2,11):
        for r in range(1,d//2+1):
            W,B=antidiagonal_measurements(d,r)
            c=d-2*r
            require(W.shape==(d*d-c*c,d*d),'measurement dimensions')
            require(B.shape==(d*d,c*c),'kernel dimensions')
            require(W*B==sp.zeros(W.rows,B.cols),'annihilation identity')
            require(W.rank()==W.rows and B.rank()==B.cols,'basis independence')
            cases+=1
    print(f'PASS: {cases} anti-diagonal constructions, exact dimensions/ranks/annihilation')
    for d in (1,2,4,8,16,24,32):
        basis=hurwitz_basis(d)
        require(len(basis)==rho(d),'Hurwitz dimension')
        for i,A in enumerate(basis):
            for j,B in enumerate(basis):
                require(A.T*B+B.T*A==(2*sp.eye(d) if i==j else sp.zeros(d)),
                        f'Hurwitz coefficient identity {d},{i},{j}')
        print(f'PASS: Hurwitz space d={d}, dimension={len(basis)}; every norm coefficient exact')
    for d in (4,12,20):
        kernel=xu_octonion_lift(d)
        W=annihilating_measurements(kernel)
        require(W.shape==(d*d-5,d*d), 'lift measurement dimension')
        for B in kernel: require(W*B.reshape(d*d,1)==sp.zeros(W.rows,1),'lift annihilation')
        print(f'PASS: Xu-octonion lift d={d}; five independent kernel matrices')
    parity_cases=0
    for d in range(2,33):
        for r in range(1,d//2+1):
            delta=degree(d,r)
            require(v2(delta)==degree_valuation(d,r),'binary degree formula')
            k,c=2*r,d-2*r
            if c:
                require(schur_dimension_valuation((c,)*k,d)==v2(delta),
                        'top Schur coefficient equals degree parity')
            data=bounds(d,r,partition_limit=0)
            require(data['lower']<=data['upper'],'bound consistency')
            parity_cases+=1
    print(f'PASS: {parity_cases} degree/parity/bound consistency checks through d=32')
    expected={(4,1):11,(5,1):16,(6,2):32,(8,3):56,(10,2):64,(24,11):568,(128,63):16368}
    for pair,value in expected.items():
        item=bounds(*pair,partition_limit=0)
        require(item['lower']==value==item['upper'],f'exact value {pair}')
    require(bounds(6,1,0)['lower']==17,'rank-one Euler-square refinement')
    require((bounds(12,5,0)['lower'],bounds(12,5,0)['upper'])==(138,139),'unresolved d=12 gap')
    require((bounds(16,7,0)['lower'],bounds(16,7,0)['upper'])==(246,247),'unresolved d=16 gap')
    print('PASS: exact cases, Euler-square refinement, and explicitly unresolved intervals')
    print('These tests check algebraic identities, not the characteristic-class theorems themselves.')

if __name__=='__main__':main()
