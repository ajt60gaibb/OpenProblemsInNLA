"""Rebuild the exact seed from two small integer matrices and seven rationals.

Uses only Python's standard library.  This is a deterministic construction;
no numerical optimization, random seed, or pre-existing numerical candidate
is needed.  JSON coefficient order is (1, alpha, alpha**2).
"""
from pathlib import Path
import json,time
from fractions import Fraction as F
from field3 import *

HERE=Path(__file__).resolve().parent.parent/'data'
S=[
 [0,-1,0,-6,-2,-6,-4],
 [1,0,3,4,-1,5,-1],
 [0,-3,0,-4,1,-2,-5],
 [6,-4,4,0,1,3,-3],
 [2,1,-1,-1,0,-1,-1],
 [6,-5,2,-3,1,0,-3],
 [4,1,5,3,1,3,0]]
T=[
 [0,0,-3,0,-2,2,5],
 [0,0,-4,2,2,-2,2],
 [3,4,0,1,1,-3,0],
 [0,-2,-1,0,4,3,0],
 [2,-2,-1,-4,0,-2,-5],
 [-2,2,3,-3,2,0,4],
 [-5,-2,0,0,5,-4,0]]
FREE_NUMERATORS=[63,1007,18,402,151,1522,1640]

def build_seed(check_existing=True):
    start=time.monotonic();n=7;I=identity(n)
    C=[[ALPHA*S[i][j]+ALPHA**2*T[i][j] for j in range(n)] for i in range(n)]
    O=multiply(field_inverse(add(I,C)),subtract(I,C))
    assert multiply(O,transpose(O))==I
    Bs=[]
    for k in range(3):
        Bs.append([[E((x.c0,x.c1,x.c2)[k]) for x in row] for row in O])
    edge=[(i,j) for i in range(n) for j in range(i+1,n)]
    equations=[]
    for Bk in Bs[:2]:
        M=multiply(transpose(O),Bk)
        for i in range(n):
            equations.append([M[j][i] if h==i else M[h][i] if j==i else ZERO for h,j in edge])
    rr,pivots=field_rref(equations)
    assert pivots==list(range(14))
    free=list(range(14,21))
    values=[ZERO]*14+[E(F(x,1000)) for x in FREE_NUMERATORS]
    for i,p in enumerate(pivots):
        values[p]=-sum((rr[i][j]*values[j] for j in free),ZERO)
    assert multiply(equations,[[x] for x in values])==[[ZERO] for _ in range(14)]
    Qp=[[ZERO for _ in range(n)] for _ in range(n)]
    for value,(i,j) in zip(values,edge):
        Qp[i][j]=Qp[j][i]=value
    Q=multiply(multiply(O,Qp),transpose(O))
    Hs=[]
    for j in range(n):
        U=[[Bs[k][i][j] for k in range(3)] for i in range(n)]
        Hs.append(multiply(multiply(transpose(U),Q),U))
    cert={'field_polynomial':'t^3-2','embedding':'real positive cube root of 2','rank':n,
          'S':S,'T':T,'orthogonal_matrix':mat_encode(O),
          'coefficient_matrices':[mat_encode(U) for U in Bs],
          'Qprime':mat_encode(Qp),'Q':mat_encode(Q),'restricted_gram':[mat_encode(H) for H in Hs],
          'linear_pivots':pivots,'linear_free':free}
    path=HERE/'exact_algebraic_certificate.json'
    if check_existing and path.exists():
        assert cert==json.loads(path.read_text()),'Rebuilt seed differs from stored exact certificate'
        print('PASS: deterministic reconstruction matches every stored field element.')
    else:
        path.write_text(json.dumps(cert,indent=2))
        print('Wrote',path.name)
    print('Seed reconstruction seconds:',round(time.monotonic()-start,3))
    return cert

if __name__=='__main__':
    build_seed()
