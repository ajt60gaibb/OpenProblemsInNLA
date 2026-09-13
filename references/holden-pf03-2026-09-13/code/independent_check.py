import json
from fractions import Fraction as F
from pathlib import Path
import argparse
parser=argparse.ArgumentParser(description='Independent exact checks; pass the submission data directory.')
parser.add_argument('data_directory', type=Path)
p=parser.parse_args().data_directory
d=json.loads((p/'exact_algebraic_certificate.json').read_text()); c=json.loads((p/'rational_cone_certificate.json').read_text())
z=(F(0),)*3; one=(F(1),F(0),F(0)); a=(F(0),F(1),F(0)); a2=(F(0),F(0),F(1))
def add(x,y): return tuple(u+v for u,v in zip(x,y))
def mul(x,y):
    t=[F(0)]*5
    for i in range(3):
        for j in range(3):t[i+j]+=x[i]*y[j]
    for k in (4,3):t[k-3]+=2*t[k]
    return tuple(t[:3])
def summ(xs):
    s=z
    for x in xs:s=add(s,x)
    return s
def tr(M):return list(map(list,zip(*M)))
def mm(A,B):return [[summ(mul(x,y) for x,y in zip(r,s)) for s in zip(*B)] for r in A]
def decode(A):return [[tuple(map(F,x)) for x in r] for r in A]
def rat(x):return (F(x),F(0),F(0))
l=F(12599210498948731647672106072782283505702,10**40);u=l+F(1,10**40)
assert l**3<2<u**3
def lower(x): return x[0]+min(x[1]*l,x[1]*u)+min(x[2]*l*l,x[2]*u*u)
O=decode(d['orthogonal_matrix']);Q=decode(d['Q']);B=[decode(x) for x in d['coefficient_matrices']]
I=[[one if i==j else z for j in range(7)] for i in range(7)]
assert mm(O,tr(O))==I and summ(Q[i][i] for i in range(7))==z
for j in range(7):
    C=[[B[k][i][j] for k in range(3)] for i in range(7)]
    H=mm(mm(tr(C),Q),C)
    assert H==tr(H) and mm(H,[[one],[a],[a2]])==[[z],[z],[z]]
    assert lower(H[0][0])>0
    assert lower(add(mul(H[0][0],H[1][1]),tuple(-x for x in mul(H[0][1],H[1][0]))))>0
V=[[rat(x) for x in row] for row in c['generators']]
D=mm(mm(tr(V),Q),V)
assert all(lower(D[i][j])>F(17,1000) for i in range(21) for j in range(i+1,21) if i//3!=j//3)
W=[[rat(x) for x in r] for r in c['coefficient_triangle']];lam=[tuple(map(F,x)) for x in c['barycentric_coefficients']]
assert mm(W,[[x] for x in lam])==[[one],[a],[a2]] and summ(lam)==one and min(map(lower,lam))>F(33,100)
print('PASS: reviewer-written polynomial-convolution arithmetic independently confirms orthogonality, trace zero, all seven PSD kernel predicates, all 189 cross-pairings, and barycentric identity/positivity. No submitted code imported.')
