from itertools import combinations
from math import comb
import sympy as s
from pathlib import Path
import json
R=s.Rational
q=[s.eye(3)[:,i] for i in range(3)]+[s.Matrix([-1,2,2])/3,s.Matrix([15,-6,10])/19,s.Matrix([6,3,-2])/7]
one=s.ones(3,1)
assert all(sum(v)==1 and v.dot(v)==1 for v in q)
b=[v-v.multiply_elementwise(v) for v in q[3:]]
assert 243*b[0]+361*b[1]+392*b[2]==s.zeros(3,1)
vertices=set()
for i,j in combinations(range(6),2):
    C=s.Matrix.vstack(one.T,q[i].T,q[j].T)
    if not C.det(): continue
    h=C.inv()*s.Matrix([1,0,0])
    if all(v.dot(h)>=0 for v in q): vertices.add(tuple(h))
expected={(R(0),R(5,8),R(3,8)),(R(0),R(2,5),R(3,5)),(R(2,3),R(0),R(1,3)),(R(1,4),R(0),R(3,4)),(R(2,3),R(1,3),R(0)),(R(2,7),R(5,7),R(0))}
assert vertices==expected
for v in q[3:]:
    assert all(v.dot(w)!=0 for w in q if w!=v)
t,x=s.symbols('t x'); accepted=[]; rejected=[]
for ids in combinations(range(6),3):
    C=s.Matrix.vstack(*(q[i].T for i in ids)); assert C.det()!=0
    scales=C.T.inv()*s.Matrix([1+t,1,1])
    ends=[tuple(v.subs(t,z) for v in scales) for z in [-R(1,1000),R(1,1000)]]
    if all(v>0 for end in ends for v in end):
        p=s.expand(C.det()*s.prod(scales)); accepted.append(ids)
        if ids!=(0,1,2):
            gap=s.Poly(s.expand(((1+t)**2-p**2).subs(t,-R(1,1000)+x/500)),x)
            degree=gap.degree()
            bern=[sum(gap.nth(k)*R(comb(j,k),comb(degree,k)) for k in range(j+1)) for j in range(degree+1)]
            assert min(bern)>0
    else:
        assert any(v==0 or all(v.subs(t,z)<0 for z in [-R(1,1000),R(1,1000)]) for v in scales)
        rejected.append(ids)
assert len(accepted)==6 and len(rejected)==14
print('PASS independent exact reconstruction: 6 primal vertices, weighted tangent balance, no extra orthogonal pairs, all 20 facet triples, 6 feasible candidates, 5 strictly positive Bernstein gap certificates on entire closed interval.')
