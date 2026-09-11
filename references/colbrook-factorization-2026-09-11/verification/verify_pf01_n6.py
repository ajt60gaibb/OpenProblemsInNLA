#!/usr/bin/env python3
"""Exact order-six subset-intersection factors, no numerical acceptance."""
from __future__ import annotations
import itertools,json
from pathlib import Path
import sympy as sp
root=Path(__file__).resolve().parents[1]
pairs=list(itertools.combinations(range(5),2))
one=sp.ones(5,1)
H=sp.Matrix.hstack(*[(sum((sp.eye(5)[:,i] for i in range(r)),sp.zeros(5,1))-r*sp.eye(5)[:,r])/sp.sqrt(r*(r+1)) for r in range(1,5)])
Z=[]
for pair in pairs:
 v=sum((sp.eye(5)[:,i] for i in pair),sp.zeros(5,1))
 y=H.T*v/sp.sqrt(2)
 Z.append(sp.Matrix(2,2,list(y)))
t=(3+sp.sqrt(5))/2
A=[];B=[]
for z in Z:
 F=z.col_join(sp.eye(2));G=sp.eye(2).col_join(-z.T)
 A.append(F*F.T);B.append(G*G.T)
for z in Z:
 F=(-z).col_join(t*sp.eye(2));G=sp.eye(2).col_join(z.T/t)
 A.append((F*F.T/t).applyfunc(sp.simplify));B.append((t*G*G.T).applyfunc(sp.simplify))
triples=[tuple(sorted(p+(5,))) for p in pairs]+[tuple(i for i in range(5) if i not in p) for p in pairs]
checks={'t_positive':bool(t>0),'t_inverse_identity':sp.simplify(t+1/t-3)==0,'all_Z_norms_3_over_5':all(sp.simplify(sp.trace(z.T*z)-sp.Rational(3,5))==0 for z in Z),'all_20_triples_distinct':len(set(triples))==20}
for i in range(20):
 for j in range(20):
  target=3-len(set(triples[i])&set(triples[j]))
  checks[f'entry_{i}_{j}']=sp.simplify(sp.trace(A[i]*B[j])-target)==0
out={'description':'Exact size-four factors for n=6. PSD follows directly from displayed Gram products with positive scalar t or 1/t; all 400 trace entries checked symbolically.','checks':checks,'passed':sum(checks.values()),'total':len(checks),'t':str(t),'row_triples_zero_based':triples,'row_factors':[[[str(x) for x in row] for row in m.tolist()] for m in A],'column_factors_for_complemented_index':[[[str(x) for x in row] for row in m.tolist()] for m in B]}
(root/'results'/'pf01_n6_verification.json').write_text(json.dumps(out,indent=2))
print(f'PF-01 n=6 exact checks: {out["passed"]}/{out["total"]}')
if not all(checks.values()):
 print([k for k,v in checks.items() if not v]);raise SystemExit(1)
