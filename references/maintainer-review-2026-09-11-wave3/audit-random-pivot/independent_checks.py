"""Independent exact checks; imports no submitted module or supplied result."""
from pathlib import Path
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations, permutations
import json, math, sys
import sympy as sp

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)
OUT=Path(__file__).resolve().parent

def frozen(a):
    return tuple(tuple(Q(x) for x in row) for row in a.tolist())

def norm(a, method):
    if method=='chol':return sum(a[i][i] for i in range(len(a)))
    return sum(x*x for row in a for x in row)

@lru_cache(None)
def expectation(a,k,method):
    z=norm(a,method)
    if k==0 or z==0:return z
    value=Q(0)
    choices=((i,i) for i in range(len(a))) if method=='chol' else ((i,j) for i in range(len(a)) for j in range(len(a)))
    for i,j in choices:
        if not a[i][j]:continue
        probability=(a[i][j] if method=='chol' else a[i][j]**2)/z
        assert probability>0
        nxt=tuple(tuple(a[u][v]-a[u][j]*a[i][v]/a[i][j] for v in range(len(a)) if v!=j) for u in range(len(a)) if u!=i)
        value+=probability*expectation(nxt,k-1,method)
    return value

def family(r,t):
    n=r+1;eps=t**(n*n)
    L=sp.eye(n)
    for i in range(n):
        for j in range(i):L[i,j]=t**(j+1)/sp.Integer(i+j+2)
    A=L*sp.diag(*[eps**j for j in range(n)])*L.T
    return A,L,eps

def ratio_bounds(A,L,eps,r):
    C=eps**r*A.inv();v=L.T.inv()[:,r]
    lo=Q(eps**r/sp.trace(C));hi=Q(eps**r/(v.dot(v)))
    ec=expectation(frozen(A),r,'chol');el=expectation(frozen(A),r,'lu')
    return {'r':r,'chol_lower':str(ec/hi),'chol_upper':str(ec/lo),'lu_lower':str(el/hi**2),'lu_upper':str(el/lo**2),'chol_lower_display':float(ec/hi),'lu_lower_display':float(el/hi**2)}

result={}
A=sp.Matrix([[2,1],[1,2]])
assert A.eigenvals()=={3:1,1:1}
assert expectation(frozen(A),1,'lu')==Q(18,5)
result['RA03_exact_2x2']={'expected_squared_error':'18/5','optimal_squared_error':'1'}
result['independent_complete_pivot_enumerations']=[]
for r in [1,2,3]:
    A,L,eps=family(r,sp.Rational(1,100))
    assert A.det()==eps**(r*(r+1)//2)
    assert all(x>0 for x in A)
    record=ratio_bounds(A,L,eps,r)
    assert Q(record['chol_lower'])>Q(99,100)*2**r
    assert Q(record['lu_lower'])>Q(99,100)*4**r
    result['independent_complete_pivot_enumerations'].append(record)

# Every leading prefix-minor coefficient and exponent, independently expanded.
t=sp.Symbol('t');prefix_count=0
for n in range(2,7):
    _,L,_=family(n-1,t)
    for s in range(n+1):
        for S in combinations(range(n),s):
            poly=sp.Poly(L.extract(S,range(s)).det(method='domain-ge'),t)
            degree=min(monom[0] for monom,coefficient in poly.terms() if coefficient)
            expected=sum(j+1 for j in range(s) if j not in S)
            assert degree==expected
            prefix_count+=1
result['symbolic_prefix_minors']={'checked':prefix_count,'dimensions':'2 through 6','all_predicted_leading_exponents_and_nonzero_coefficients':True}

# Exhaustive count checks use the normalizer condition directly.
counts={}
for r in range(1,8):
    count=sum(all(s+1 not in h[:s] for s in range(r)) for h in permutations(range(1,r+2),r))
    assert count==2**r
    counts[str(r)]=count
result['surviving_history_counts']=counts

# Verify cancellation independently of the special asymptotic family.
A=sp.Matrix([[4,1,2],[1,3,1],[2,1,5]])
def residual(A,I,J):
    if not I:return A
    return A-A[:,J]*A.extract(I,J).inv()*A[I,:]
orders=list(permutations(range(3),2));dc=Q(A.det());chol=Q(0);lu=Q(0)
for h in orders:
    weight=dc
    for s in range(2):weight/=Q(sp.trace(residual(A,list(h[:s]),list(h[:s]))))
    chol+=weight
for rows in orders:
    for cols in orders:
        weight=dc**2
        for s in range(2):
            R=residual(A,list(rows[:s]),list(cols[:s]));weight/=Q(sum(x*x for x in R))
        lu+=weight
assert chol==expectation(frozen(A),2,'chol')
assert lu==expectation(frozen(A),2,'lu')
result['history_cancellation']={'matrix':A.tolist(),'chol':str(chol),'lu':str(lu)}

# An independent replication example, with rational isometry and nontrivial c.
A=sp.Matrix([[8,2,2],[2,2,1],[2,1,2]])
P=sp.Matrix([[sp.Rational(1,2),0,0]]*4+[[0,1,0],[0,0,1]])
c=sp.Integer(2);C=P*A*P.T/c
assert P.T*P==sp.eye(3) and all(C[i,i]==1 for i in range(6))
rep=[]
for k in [1,2]:
    ec=expectation(frozen(A),k,'chol');el=expectation(frozen(A),k,'lu')
    ec2=expectation(frozen(C),k,'chol');el2=expectation(frozen(C),k,'lu')
    assert ec/c==ec2 and el/c**2==el2
    rep.append({'steps':k,'source_chol':str(ec),'replica_chol':str(ec2),'source_lu':str(el),'replica_lu':str(el2)})
result['correlation_replication']=rep
result['zero_residual']={}
for method in ['chol','lu']:
    value=expectation(frozen(sp.diag(1,0,0)),2,method)
    assert value==0
    result['zero_residual'][method]=str(value)
(OUT/'independent-results.json').write_text(json.dumps(result,default=str,indent=2))
print(json.dumps({k:v for k,v in result.items() if k!='independent_complete_pivot_enumerations'},default=str,indent=2))
print('Independent lower bounds:',[(x['r'],x['chol_lower_display'],x['lu_lower_display']) for x in result['independent_complete_pivot_enumerations']])
