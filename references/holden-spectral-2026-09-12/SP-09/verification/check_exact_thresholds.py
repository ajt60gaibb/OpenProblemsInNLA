#!/usr/bin/env python3
"""Exact squared-distance checks of the two-point assignment formula.
Does not discretize the unitary orbit or purport to prove the all-unitary bound.
"""
from __future__ import annotations
from itertools import combinations, product

def d2(z,w):return (z[0]-w[0])**2+(z[1]-w[1])**2

def formula(a,b,beta,p):
    aa=[d2(z,a) for z in beta];bb=[d2(z,b) for z in beta];n=len(beta)
    return max(max(min(x,y) for x,y in zip(aa,bb)),sorted(aa)[p-1],sorted(bb)[n-p-1])

def exhaustive(a,b,beta,p):
    aa=[d2(z,a) for z in beta];bb=[d2(z,b) for z in beta];n=len(beta)
    return min(max(aa[j] if j in subset else bb[j] for j in range(n))
               for subset in map(set,combinations(range(n),p)))

def main():
    grid=((0,0),(1,0),(0,1),(2,-1))
    anchors=(((0,0),(2,0)),((1,1),(-1,2)),((0,0),(0,1)))
    count=rep=0
    for n in range(2,6):
        for beta in product(grid,repeat=n):
            for a,b in anchors:
                for p in range(1,n):
                    f=formula(a,b,beta,p)
                    if f!=exhaustive(a,b,beta,p):raise ArithmeticError('assignment mismatch')
                    for k in (2,3):
                        if formula(a,b,beta*k,p*k)!=f:raise ArithmeticError('amplification mismatch')
                        rep+=1
                    count+=1
    print(f'PASS: {count} exact squared-distance formula comparisons against every capacity assignment, n=2..5; {rep} exact multiplicity-repetition checks, k=2,3.')
    print('The norm lower bound for all unitaries is established in proof.md, not by this finite combinatorial check.')
if __name__=='__main__':main()
