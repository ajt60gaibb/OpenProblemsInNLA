#!/usr/bin/env python3
"""Exhaustive exact verification of the restricted-fooling-set certificate for C_3."""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp


def main() -> None:
    labels=list(range(8))
    C=sp.Matrix([[(1-(a&b).bit_count())**2 for b in labels] for a in labels])
    z=sp.Matrix([(-1)**a.bit_count() for a in labels])
    assert C*z==sp.zeros(8,1) and z.T*C==sp.zeros(1,8)
    minor=C[:7,:7].det()
    assert minor!=0
    assert C.rank()==7
    odd={a for a in labels if a.bit_count()%2}
    even=set(labels)-odd
    pairs=[]
    for i in range(3):
        singleton=1<<i
        doubleton=7^singleton
        pairs.extend([(singleton,doubleton),(doubleton,singleton),(doubleton,doubleton)])
    assert len(set(pairs))==9 and all(C[a,b]==1 for a,b in pairs)
    valid=0
    max_covered=0
    for rmask in range(1,1<<8):
        R=[a for a in labels if rmask>>a&1]
        if not(set(R)&odd and set(R)&even):
            continue
        common=[b for b in labels if all(C[a,b]>0 for a in R)]
        for cmask in range(1,1<<len(common)):
            J=[b for j,b in enumerate(common) if cmask>>j&1]
            if not(set(J)&odd and set(J)&even):
                continue
            valid+=1
            covered=sum(a in R and b in J for a,b in pairs)
            max_covered=max(max_covered,covered)
            assert covered<=1,(R,J,covered)
    results={
        'ordinary_rank':7,
        'nonzero_7_by_7_minor':int(minor),
        'null_vector':[int(x) for x in z],
        'distinguished_entries':pairs,
        'balanced_positive_rectangles_checked':valid,
        'maximum_distinguished_entries_in_one_rectangle':max_covered,
        'certificate_conclusion':'Nonnegative rank 7 is impossible; ordinary rank gives >=7 and identity factorization gives <=8, hence rank_+(C_3)=8.',
        'scope':'Only n=3. No proof of the full NR-03 family is asserted.'
    }
    out=Path(__file__).resolve().parents[1]/'results'/'nr03_n3_verification.json'
    out.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__=='__main__':main()
