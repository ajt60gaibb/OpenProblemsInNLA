#!/usr/bin/env python3
"""Independent exact comparison with Rowland--Wu (2025), Example 32.

Computes the complete degree-20 polynomial from the arbitrary-margin formula,
compares the four coefficients printed in the source, and checks irreducibility.
A high-precision numerical root check is supplementary, not a proof.
"""
from pathlib import Path
import json
import sympy as s
from verify_nm04_margins import indices,margin_matrix
ROOT=Path(__file__).resolve().parents[1]
A=s.Matrix([[2000,1030,650,320],[1080,1110,555,255],
            [720,580,500,200],[350,280,210,160]])
rows=[6000,4000,2500,1000]; cols=[6225,4000,2340,935]
inds=indices(4,4); G=margin_matrix(rows,cols)
delta=s.diag(*[A.extract((0,)+r,(0,)+c).det() for r,c in inds])
gamma=s.diag(*[A[0,0]*A.extract(r,c).det() for r,c in inds])
# K(z) differs from z*I - T by a fixed invertible rational left factor.
T=-rows[0]*cols[0]*delta.inv()*G.inv()*gamma
z=s.symbols('z')
char=T.charpoly(z).as_poly()
_,intpoly=char.clear_denoms(convert=True)
_,p=intpoly.primitive()
if p.LC()<0:p=-p
assert p.degree()==20
expected={20:int('62'+'11170485642866385308015185014605806684592592997303612'),
19:-1911288675240357642608985257264441863326549355081446688219995,
1:-980316295756763597938629190043558577216660563425441394040234375*10**72,
0:60077293526471262201893650291744622440239260152893558984375*10**79}
for degree,value in expected.items():
    assert p.nth(degree)==value,(degree,p.nth(degree),value)
factors=s.factor_list(p)[1]
assert len(factors)==1 and factors[0][0].degree()==20 and factors[0][1]==1
# Exact determinant evaluations independently test the characteristic conversion.
scale=(G*delta).det()
for t in [0,1,6000]:
    lhs=(rows[0]*cols[0]*gamma+t*G*delta).det(method='domain-ge')
    rhs=scale*char.eval(t)
    assert lhs==rhs
out={'status':'all exact checks passed','degree':20,'irreducible_over_Q':True,
     'printed_coefficients_matched':list(expected),
     'independent_determinant_evaluations':3,
     'coefficients_high_to_low':[str(c) for c in p.all_coeffs()],
     'source':'Rowland and Wu, arXiv:2409.02789v2, Example 32'}
(ROOT/'results'/'nm04_kruithof_verification.json').write_text(json.dumps(out,indent=2)+'\n')
(ROOT/'results'/'kruithof_degree20_polynomial.txt').write_text(str(p.as_expr())+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='coefficients_high_to_low'},indent=2))
