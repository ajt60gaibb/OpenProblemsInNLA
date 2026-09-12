#!/usr/bin/env python3
"""Exhaustive n=3 binary regression for order_two_reduction.md.
Finite validation only; the written proof applies to arbitrary real data/n.
"""
from itertools import product,combinations,permutations
from pathlib import Path
import json

def det_int(A):
    n=len(A);out=0
    for p in permutations(range(n)):
        t=(-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
        for i in range(n):t*=A[i][p[i]]
        out+=t
    return out

def tn2(A):
    return all(A[i][j]*A[k][l]>=A[i][l]*A[k][j]
               for i,k in combinations(range(len(A)),2)
               for j,l in combinations(range(len(A)),2))

def main():
    n=3;ends=[]
    for v in product((0,1),repeat=n*n):
        A=[list(v[i*n:(i+1)*n]) for i in range(n)]
        if det_int(A)!=0 and tn2(A):ends.append(A)
    pairs=vertices=0
    for A in ends:
        for B in ends:
            if any((-1)**(i+j)*(B[i][j]-A[i][j])<0 for i in range(n) for j in range(n)):continue
            pairs+=1;free=[(i,j) for i in range(n) for j in range(n) if A[i][j]!=B[i][j]]
            for bits in product((0,1),repeat=len(free)):
                M=[r[:] for r in A]
                for (i,j),b in zip(free,bits):M[i][j]=B[i][j] if b else A[i][j]
                assert tn2(M);vertices+=1
    out={'binary_matrices_enumerated':2**(n*n),'nonsingular_TN2_endpoints':len(ends),
         'checker_ordered_pairs':pairs,'interval_vertices_checked':vertices,
         'all_passed':True,'scope':'Finite regression, not proof of the real-matrix theorem'}
    Path(__file__).with_name('order_two_test_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
