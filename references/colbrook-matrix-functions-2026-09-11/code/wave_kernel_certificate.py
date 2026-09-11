"""Exact verification of the finite base cases for the all-order disk theorem.

This file uses only Python's standard library. It verifies [m/m] Pade identities
for f(z)=cosh(sqrt(z)) and an absolute-coefficient bound on |z| <= 3.
No floating-point arithmetic is used in the proof checks.
"""
from __future__ import annotations
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import argparse
import json


def require(condition: bool, message: str = "Certificate check failed") -> None:
    if not condition:
        raise ArithmeticError(message)


def solve_exact(matrix:list[list[F]], rhs:list[F]) -> list[F]:
    n=len(rhs)
    if len(matrix)!=n or any(len(row)!=n for row in matrix):
        raise ValueError('Expected a square system')
    a=[list(row)+[b] for row,b in zip(matrix,rhs)]
    for j in range(n):
        pivot=next((i for i in range(j,n) if a[i][j]),None)
        if pivot is None: raise ArithmeticError('Singular Pade system')
        a[j],a[pivot]=a[pivot],a[j]
        t=a[j][j];a[j]=[v/t for v in a[j]]
        for i in range(j+1,n):
            t=a[i][j]
            if t:a[i]=[v-t*w for v,w in zip(a[i],a[j])]
    x=[F(0)]*n
    for i in range(n-1,-1,-1):
        x[i]=a[i][-1]-sum((a[i][j]*x[j] for j in range(i+1,n)),F(0))
    return x


def pade(m:int) -> tuple[list[F],list[F]]:
    if m<0:raise ValueError('Nonnegative degree required')
    a=[F(1,factorial(2*k)) for k in range(2*m+1)]
    T=[[a[m+i-j] for j in range(1,m+1)] for i in range(1,m+1)]
    q=[F(1)]+solve_exact(T,[-a[m+i] for i in range(1,m+1)])
    p=[sum((q[j]*a[k-j] for j in range(k+1)),F(0)) for k in range(m+1)]
    return p,q


def check(m:int,p:list[F],q:list[F]):
    require(len(p)==len(q)==m+1 and q[0]==1, "Invalid Pade degree or normalization")
    a=[F(1,factorial(2*k)) for k in range(2*m+1)]
    for k in range(2*m+1):
        coefficient=sum((q[j]*a[k-j] for j in range(min(m,k)+1)),F(0))
        require(coefficient==(p[k] if k<=m else 0), f'Pade identity failed at m={m}, k={k}')
    B=sum((abs(q[j])*3**j for j in range(m+1)),F(0))
    N=sum((abs(p[j]-q[j])*3**j for j in range(m+1)),F(0))
    require(B<2, f'Denominator lower bound failed at m={m}')
    require(N<=2*(2-B), f'Disk bound failed at m={m}')
    if m>=2:require(20*N<39*(2-B), f'Stronger finite bound failed at m={m}')
    return B,N,N/(2-B)


def generate(path:Path,last:int=15):
    records=[]
    for m in range(1,last+1):
        p,q=pade(m);B,N,bound=check(m,p,q)
        records.append({'m':m,'p':[str(x) for x in p],'q':[str(x) for x in q],
                        'B_at_3':str(B),'N_at_3':str(N),'bound':str(bound),
                        'slack_for_2':str(2*(2-B)-N)})
        print(f'm={m:2}: verified, bound={float(bound):.12f}')
    # An entirely rational bound used in the analytic tail argument:
    # for k>=3 successive terms 3^k/(2k)! have ratio at most 3/56.
    cosh_upper=F(1)+F(3,2)+F(3,8)+F(3,80)/(1-F(3,56))
    require(cosh_upper==F(6179,2120) and cosh_upper<F(35,12), "Analytic rational bound failed")
    result={'statement':'|1-r_m(z)| <= 2 on |z| <= 3, base cases m=1,...,15',
        'arithmetic':'exact fractions; no floating point in verification',
        'records':records,'cosh_sqrt3_upper_bound':str(cosh_upper)}
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(result,indent=2))


def verify(path:Path):
    data=json.loads(path.read_text())
    require([r['m'] for r in data['records']]==list(range(1,16)), 'Incomplete base cases')
    for r in data['records']:
        B,N,bound=check(r['m'],list(map(F,r['p'])),list(map(F,r['q'])))
        require(str(B)==r['B_at_3'] and str(N)==r['N_at_3'] and str(bound)==r['bound'], 'Stored bound differs')
        require(str(2*(2-B)-N)==r['slack_for_2'], 'Stored slack differs')
    require(F(1)+F(3,2)+F(3,8)+F(3,80)/(1-F(3,56))==F(data['cosh_sqrt3_upper_bound'])<F(35,12), 'Rational cosh bound differs')
    print('PASS: all 15 finite Pade certificates and the rational cosh bound.')

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('certificate',type=Path)
    parser.add_argument('--verify',action='store_true');args=parser.parse_args()
    if args.verify:verify(args.certificate)
    else:generate(args.certificate)
