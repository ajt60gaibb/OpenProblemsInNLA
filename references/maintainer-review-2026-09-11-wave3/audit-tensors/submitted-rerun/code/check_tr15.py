"""Exact integer audit of every contraction coefficient in the TR-15 example."""
import itertools,json
from pathlib import Path
h=[2,0,1,0,2,0,-1]
coeff=[]
for i in range(3):
 d={}
 for j,k in itertools.product(range(3),repeat=2):
  powers=tuple(int(a==j)+int(a==k) for a in range(3))
  d[powers]=d.get(powers,0)+h[i+j+k]
 coeff.append(d)
expected=[{(2,0,0):2,(0,2,0):1,(0,0,2):2,(1,0,1):2},
 {(1,1,0):2,(0,1,1):4},
 {(2,0,0):1,(0,2,0):2,(0,0,2):-1,(1,0,1):4}]
for got,want in zip(coeff,expected):assert {p:c for p,c in got.items() if c}==want
# First slice = identity + (1,0,1)(1,0,1)^T, a strict sum-of-squares certificate.
slice0=[[h[j+k] for k in range(3)] for j in range(3)]
v=[1,0,1];assert slice0==[[int(j==k)+v[j]*v[k] for k in range(3)] for j in range(3)]
e=[0,1];result=[]
for i in range(2):
 result.append(sum(h[i+sum(indices)]*__import__('math').prod(e[j] for j in indices) for indices in itertools.product(range(2),repeat=5)))
assert result==[0,-1]
P=lambda t:2*t**4+2*t**3+3*t*t-4*t-1
assert P(0)==-1 and P(1)==2
report={'status':'PASS','generating_vector':h,'first_slice':slice0,'positive_definiteness':'identity plus rank-one positive-semidefinite matrix','B_e2_contraction':result,'B_eigenvalue':-1,'A_eigenpair_polynomial_endpoint_values':[P(0),P(1)],'scope':'Exact algebra supports the complete analytic counterexample; no floating-point eigenpair enumeration.'}
path=Path(__file__).with_name('TR-15-exact-checks.json');path.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
