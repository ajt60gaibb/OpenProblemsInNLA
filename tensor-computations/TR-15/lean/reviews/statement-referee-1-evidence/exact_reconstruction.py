"""Independent exact diagnostics for the TR-15 statement boundary.
Uses sparse integer coefficients and exhaustive ordered index tuples, not the
submitted numerical checker or a tensor-eigenvalue approximation. These are
statement checks, not Lean proof certificates or evidence of a proved theorem.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import product
from pathlib import Path
import json
OUT=Path(__file__).resolve().parent
h=[2,0,1,0,2,0,-1]
m,q,n=3,2,2
assert m%2==1 and m>=3 and q>=2 and n>=2
assert len(h)==q*m*(n-1)+1==m*((q*(n-1)+1)-1)+1==7

def sparse_contraction(order,dimension,component):
    c=defaultdict(int)
    terms=[]
    for indices in product(range(dimension),repeat=order-1):
        full=(component,)+indices
        assert sum(full)==sum(i+1 for i in full)-order
        assert 0<=sum(full)<=order*(dimension-1)
        exponent=tuple(indices.count(j) for j in range(dimension))
        c[exponent]+=h[sum(full)]
        terms.append({'indices':list(indices),'generator_index':sum(full),'coefficient':h[sum(full)]})
    return {k:v for k,v in c.items() if v},terms
lower=[sparse_contraction(3,3,i) for i in range(3)]
expected=[{(2,0,0):2,(0,2,0):1,(1,0,1):2,(0,0,2):2},
          {(1,1,0):2,(0,1,1):4},
          {(2,0,0):1,(0,2,0):2,(1,0,1):4,(0,0,2):-1}]
assert [c for c,_ in lower]==expected
assert sum(len(t) for _,t in lower)==27
# Independently multiply the four linear forms in the claimed SOS.
sos=defaultdict(int)
for linear in [(1,0,1),(1,0,0),(0,1,0),(0,0,1)]:
    for i in range(3):
        for j in range(3):
            exponent=tuple((k==i)+(k==j) for k in range(3))
            sos[exponent]+=linear[i]*linear[j]
assert {k:v for k,v in sos.items() if v}==expected[0]
# The three coordinate forms appear individually, so the sum of their squares
# is strictly positive for every nonzero real vector; this is an analytic
# observation about the exact SOS, not an inference from sampling vectors.
upper=[]
for i in range(2):
    coefficients,terms=sparse_contraction(6,2,i)
    surviving=[]
    total=Fraction(0)
    for t in terms:
        vprod=1
        for j in t['indices']:vprod*=([0,1][j])
        if vprod:surviving.append(t)
        total+=t['coefficient']*vprod
    assert len(terms)==32 and len(surviving)==1
    assert surviving[0]['indices']==[1]*5
    assert total==[0,-1][i]==-1*([0,1][i]**5)
    upper.append({'component':i,'ordered_terms':len(terms),'nonzero_vector_products':surviving,'value':str(total)})
# Substitute x=(1,0,t) into the independently enumerated lower coefficients.
substituted=[]
for poly in expected:
    c=defaultdict(int)
    for (a,b,cdeg),value in poly.items():
        if b==0:c[cdeg]+=value
    substituted.append({k:v for k,v in c.items() if v})
assert substituted==[{0:2,1:2,2:2},{},{0:1,1:4,2:-1}]
lam=substituted[0]
residual=defaultdict(int)
for degree,value in lam.items():residual[degree+2]+=value
for degree,value in substituted[2].items():residual[degree]-=value
residual={k:v for k,v in residual.items() if v}
assert residual=={0:-1,1:-4,2:3,3:2,4:2}
def evaluate(poly,t):return sum(Fraction(c)*t**e for e,c in poly.items())
assert evaluate(residual,Fraction(0))==-1
assert evaluate(residual,Fraction(1))==2
record={'verdict':'PASS','scope':'Exact independent statement diagnostics; not Lean verification. Continuity, IVT and universal square positivity remain proof obligations.',
 'parameters':{'m':m,'q':q,'n':n,'generator':h,'lower_order_dimension':[3,3],'upper_order_dimension':[6,2]},
 'lower_contraction_terms':[{'component':i,'terms':t,'collected_coefficients':[{'exponents':list(k),'coefficient':v} for k,v in sorted(c.items())]} for i,(c,t) in enumerate(lower)],
 'lower_sos_coefficient_identity':True,'individual_coordinate_squares_present':True,
 'upper_contractions':upper,'upper_eigenvalue':-1,'upper_vector_nonzero':True,
 'eigenvalue_polynomial':[lam.get(i,0) for i in range(3)],
 'third_equation_residual_coefficients_ascending':[residual.get(i,0) for i in range(5)],
 'root_polynomial_endpoint_values':{'0':-1,'1':2},'interval_open':[0,1],
 'no_approximate_root_or_spectral_solver_used':True}
(OUT/'exact-reconstruction.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS: 27 lower entries, 64 upper entries, exact SOS, eigenpair residual and strict IVT endpoint signs')
