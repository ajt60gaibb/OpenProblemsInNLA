#!/usr/bin/env python3
"""Optional second characteristic-polynomial check, using only Python integers.

Checks a representative matrix for EVERY polynomial listed in a certificate.
This does not replace full family coverage regeneration. Large cases may take
considerably longer than the NumPy verifier.
"""
from __future__ import annotations
import argparse,json,time
from pathlib import Path


def matrix_from_id(n:int, low:int, high:int, pid:int)->list[list[int]]:
    epscode=pid//(2**(n-1))
    eps=[1 if (epscode//(2**i))%2==0 else -1 for i in range(n)]
    d=[1]+[1 if (pid//(2**i))%2==0 else -1 for i in range(n-1)]
    return [[high if d[i]*d[j]*eps[min(i,j)]==1 else low for j in range(n)] for i in range(n)]


def charpoly(a:list[list[int]])->tuple[int,...]:
    n=len(a);b=[[int(i==j) for j in range(n)] for i in range(n)];c=[1]
    for k in range(1,n+1):
        ab=[[sum(a[i][r]*b[r][j] for r in range(n)) for j in range(n)] for i in range(n)]
        tr=sum(ab[i][i] for i in range(n))
        if tr%k:raise ArithmeticError('coefficient not integral')
        ck=-(tr//k);c.append(ck)
        for i in range(n):ab[i][i]+=ck
        b=ab
    return tuple(c)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate');args=ap.parse_args()
    p=json.loads(Path(args.certificate).read_text());start=time.monotonic()
    for j,item in enumerate(p['certificates']):
        a=matrix_from_id(p['n'],p['low'],p['high'],item['pattern'])
        if charpoly(a)!=tuple(item['coefficients']):raise ArithmeticError(f'mismatch at {j}')
    print(f'PASS: Python-integer second-algorithm check of all {len(p["certificates"])} representative polynomials for n={p["n"]}; {time.monotonic()-start:.3f}s. Full family coverage is a separate check.')

if __name__=='__main__':main()
