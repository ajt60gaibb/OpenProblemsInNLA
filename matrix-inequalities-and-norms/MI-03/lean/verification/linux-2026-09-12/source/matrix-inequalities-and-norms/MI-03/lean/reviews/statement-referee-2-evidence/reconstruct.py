"""Independent MI-03 diagnostics by referee 2; no imported author checker.
Exact coefficient arithmetic in Q[s,i]/(s^2-3,i^2+1). These finitely many
algebraic roots and matrices diagnose transcription; they do not prove the
required arbitrary-k exponential, CFC, norm or infimum statements.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import hashlib,json
@dataclass(frozen=True)
class E:
 c:tuple
 def __add__(self,other):
  q=coerce(other);return E(tuple(a+b for a,b in zip(self.c,q.c)))
 __radd__=__add__
 def __neg__(self):return E(tuple(-a for a in self.c))
 def __sub__(self,other):return self+-coerce(other)
 def __rsub__(self,other):return coerce(other)+-self
 def __mul__(self,other):
  q=coerce(other);r=[F(0)]*4
  for j,a in enumerate(self.c):
   for k,b in enumerate(q.c):
    r[j^k]+=a*b*(3 if j&k&1 else 1)*(-1 if j&k&2 else 1)
  return E(tuple(r))
 __rmul__=__mul__
 def __pow__(self,k):
  a=coerce(1)
  for _ in range(k):a=a*self
  return a
 def conj(self):return E((self.c[0],self.c[1],-self.c[2],-self.c[3]))
 def data(self):return [str(c) for c in self.c]
def coerce(q):return q if isinstance(q,E) else E((F(q),F(0),F(0),F(0)))
zero=coerce(0);one=coerce(1);s=E((F(0),F(1),F(0),F(0)));imag=E((F(0),F(0),F(1),F(0)))
assert s*s==coerce(3) and imag*imag==coerce(-1)
def mzero():return [[zero,zero],[zero,zero]]
def diag(a,b):return [[coerce(a),zero],[zero,coerce(b)]]
def add(a,b):return [[a[i][j]+b[i][j] for j in range(2)] for i in range(2)]
def scale(t,a):return [[coerce(t)*x for x in row] for row in a]
def sub(a,b):return add(a,scale(-1,b))
def total(ms):
 a=mzero()
 for m in ms:a=add(a,m)
 return a
def mul(a,b):return [[sum(a[i][h]*b[h][j] for h in range(2)) for j in range(2)] for i in range(2)]
def adj(a):return [[a[j][i].conj() for j in range(2)] for i in range(2)]
def outer(u,v):return [[u[i]*v[j].conj() for j in range(2)] for i in range(2)]
def inner(u,v):return sum(u[i].conj()*v[i] for i in range(2))
def action(a,v):return [sum(a[i][j]*v[j] for j in range(2)) for i in range(2)]
def gram(a):return mul(adj(a),a)
def data(a):return [[x.data() for x in row] for row in a]
def check_variance(A,Rj,R):
 k=len(A);S=total(A);T=total(Rj)
 for a,r in zip(A,Rj):assert mul(r,r)==gram(a) and adj(r)==r
 assert mul(R,R)==gram(S) and adj(R)==R
 ordered=scale(F(1,2),total([gram(sub(a,b)) for a in A for b in A]))
 unordered=total([gram(sub(A[i],A[j])) for i in range(k) for j in range(i+1,k)])
 assert ordered==unordered==sub(scale(k,total([gram(a) for a in A])),gram(S))
 shifted=sub(R,diag(F(k,2),F(k,2)))
 lhs=scale(k,sub(add(diag(F(k,4),F(k,4)),T),R))
 rhs=add(add(scale(k,total([sub(r,mul(r,r)) for r in Rj])),ordered),mul(shifted,shifted))
 assert lhs==rhs
 return {'ordered_equals_unordered':True,'gram_variance_identity':True,'positive_decomposition_identity':True,'decomposition_value':data(lhs)}
roots={2:coerce(-1),3:coerce(F(-1,2))+F(1,2)*s*imag,4:imag,6:coerce(F(1,2))+F(1,2)*s*imag,12:F(1,2)*s+F(1,2)*imag}
e=[one,zero];records=[]
for k,w in roots.items():
 assert w**k==one and all(w**j!=one for j in range(1,k))
 assert w.conj()*w==one and sum(w**j for j in range(k))==zero
 V=[[coerce(F(1,2)),F(1,2)*s*(w**j)] for j in range(k)]
 A=[outer(e,v) for v in V];P=[outer(v,v) for v in V]
 for v,a,p in zip(V,A,P):
  assert inner(v,v)==one and gram(a)==p and mul(p,p)==p and adj(p)==p
  assert action(a,v)==e
 S=total(A);T=total(P);R=diag(F(k,2),0)
 assert S==R and T==diag(F(k,4),F(3*k,4))
 diff=sub(R,T);assert diff==diag(F(k,4),F(-3*k,4))
 assert sub(diag(F(k,4),F(k,4)),diff)==diag(0,k)
 records.append({'k':k,'algebraic_root':w.data(),'root_order':k,'zero_geometric_sum':True,'all_unit_vectors':True,'all_gram_projection_certificates':True,'all_actions_Av_equal_e1':True,'sum_A':data(S),'sum_modulus_candidates':data(T),'difference':data(diff),**check_variance(A,P,R)})
# Non-unit, noncommuting contraction probe with vanishing sum. Its two nonzero
# singular values are the exact rational scales; individual moduli are λ vv*.
u=[coerce(F(3,5)),coerce(F(4,5))];v=[coerce(F(4,5)),F(3,5)*imag]
p=[zero,imag];q=[coerce(F(1,2)),F(1,2)*s]
assert all(inner(t,t)==one for t in [u,v,p,q])
a=scale(F(1,2),outer(u,v));b=scale(F(2,3),outer(p,q))
A=[a,scale(-1,a),b,scale(-1,b),mzero()]
ra=scale(F(1,2),outer(v,v));rb=scale(F(2,3),outer(q,q))
Rj=[ra,ra,rb,rb,mzero()]
assert total(A)==mzero() and mul(ra,rb)!=mul(rb,ra)
probe={'k':5,'noncommuting_moduli':True,'scales':['1/2','1/2','2/3','2/3','0'],**check_variance(A,Rj,mzero())}
out=Path(__file__).resolve().parent
record={'status':'PASS','reviewer':'/root/leancert_examples','scope':'Independent exact finite transcription and algebra diagnostics; not a universal-k proof or analytic spectral/norm oracle','basis':['1','sqrt(3)','i','sqrt(3)*i'],'root_cases':records,'additional_probe':probe,'generic_reasoning_checked_by_referee':'For every k>=2 the actual primitive root has unit norm and zero geometric sum; the unit outer products give the declared sums. The ordered-pair Gram sum identity is distributivity over arbitrary finite sets. Positive decomposition gives all-dimension upper bound, first coordinate of full witness gives every admissible c>=k/4, hence actual IsLeast and real infimum.'}
(out/'reconstruction.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS: exact root/witness cases k=2,3,4,6,12; noncommuting subunit k=5 variance probe; no floating arithmetic')
