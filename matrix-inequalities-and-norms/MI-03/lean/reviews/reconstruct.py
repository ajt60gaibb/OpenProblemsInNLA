"""Exact finite diagnostics in Q(sqrt(3), i), not a universal proof.

The field representation uses (1, sqrt(3), i, i*sqrt(3)); no floating arithmetic.
The chosen roots have orders 2, 3, 4 and 6. Generic k remains a Lean obligation.
"""
from fractions import Fraction as Q
from pathlib import Path
import json

class F:
    def __init__(self,a=0,b=0,c=0,d=0):self.v=tuple(map(Q,(a,b,c,d)))
    @staticmethod
    def coerce(x):return x if isinstance(x,F) else F(x)
    def __add__(self,x):
        x=F.coerce(x);return F(*(a+b for a,b in zip(self.v,x.v)))
    __radd__=__add__
    def __neg__(self):return F(*(-a for a in self.v))
    def __sub__(self,x):return self+-F.coerce(x)
    def __mul__(self,x):
        x=F.coerce(x);out=[Q(0)]*4
        for i,a in enumerate(self.v):
            for j,b in enumerate(x.v):
                out[i^j]+=a*b*(3 if i&j&1 else 1)*(-1 if i&j&2 else 1)
        return F(*out)
    __rmul__=__mul__
    def __pow__(self,n):
        ans=F(1)
        for _ in range(n):ans=ans*self
        return ans
    def star(self):return F(self.v[0],self.v[1],-self.v[2],-self.v[3])
    def __eq__(self,x):return self.v==F.coerce(x).v
    def record(self):return [str(x) for x in self.v]

def outer(u,v):return [[x*y.star() for y in v] for x in u]
def adj(a):return [[a[j][i].star() for j in range(2)] for i in range(2)]
def mm(a,b):return [[sum(a[i][q]*b[q][j] for q in range(2)) for j in range(2)] for i in range(2)]
def scale(c,a):return [[c*x for x in row] for row in a]
def add(a,b):return [[a[i][j]+b[i][j] for j in range(2)] for i in range(2)]
def sub(a,b):return add(a,scale(-1,b))
def msum(aa):
    out=[[F(),F()],[F(),F()]]
    for a in aa:out=add(out,a)
    return out
def diag(a,b):return [[F.coerce(a),F()],[F(),F.coerce(b)]]
def record(a):return [[x.record() for x in row] for row in a]

roots={2:F(-1),3:F(Q(-1,2),0,0,Q(1,2)),4:F(0,0,1),6:F(Q(1,2),0,0,Q(1,2))}
results=[]
for k,z in roots.items():
    assert z*z.star()==1 and z**k==1
    assert all(z**j!=1 for j in range(1,k))
    assert sum(z**j for j in range(k))==0
    vectors=[[F(Q(1,2)),F(0,Q(1,2))*z**j] for j in range(k)]
    assert all(sum(x*x.star() for x in v)==1 for v in vectors)
    a=[outer([F(1),F()],v) for v in vectors]
    modulus=[outer(v,v) for v in vectors]
    assert all(mm(adj(x),x)==r and mm(r,r)==r for x,r in zip(a,modulus))
    s=msum(a);t=msum(modulus);r=diag(Q(k,2),0)
    assert s==r and t==diag(Q(k,4),Q(3*k,4))
    assert mm(r,r)==mm(adj(s),s)
    difference=sub(r,t)
    assert difference==diag(Q(k,4),Q(-3*k,4))
    variance=scale(Q(1,2),msum([mm(adj(sub(x,y)),sub(x,y)) for x in a for y in a]))
    shifted=sub(r,diag(Q(k,2),Q(k,2)))
    lhs=scale(k,sub(add(t,diag(Q(k,4),Q(k,4))),r))
    rhs=add(scale(k,msum([sub(x,mm(x,x)) for x in modulus])),add(variance,mm(shifted,shifted)))
    assert lhs==rhs
    results.append(dict(k=k,root_coefficients=z.record(),vector_norm_squared='1',
        root_power='1',geometric_sum='0',gram_and_projection_identities=True,
        sum_A=record(s),sum_proposed_moduli=record(t),difference=record(difference),
        exact_positive_decomposition_identity=True))
out=dict(status='PASS',field='Exact Q(sqrt(3),i), basis 1,sqrt(3),i,i*sqrt(3)',
    scope='Finite algebraic transcription diagnostics only. No universal k, CFC, PSD, operator-norm or infimum theorem is proved by this script.',checks=results)
Path(__file__).with_name('reconstruction.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'PASS','exact_test_counts':list(roots),'uses_floating_point':False}))
