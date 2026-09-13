from fractions import Fraction as F
import json
from pathlib import Path
# Exact rational matrix reconstruction; no submitted verifier is imported.
def tr(a): return list(map(list,zip(*a)))
def mm(a,b): return [[sum((x*y for x,y in zip(row,col)),F(0)) for col in zip(*b)] for row in a]
def eq(a,b): return a==b
A=[[F(1),F(1),F(0)],[F(1),F(0),F(1)]]
B=[[F(1,3),F(1,3)],[F(2,3),F(-1,3)],[F(-1,3),F(2,3)]]
X=[[F(0),F(0)],[F(1),F(0)],[F(0),F(1)]]
I=[[F(1),F(0)],[F(0),F(1)]]
G=[[F(2),F(1)],[F(1),F(2)]]
Gi=[[F(2,3),F(-1,3)],[F(-1,3),F(2,3)]]
checks={'AAstar':eq(mm(A,tr(A)),G),'G_inverse_left':eq(mm(Gi,G),I),'G_inverse_right':eq(mm(G,Gi),I),'pseudoinverse':eq(mm(tr(A),Gi),B),'AB':eq(mm(A,B),I),'AX':eq(mm(A,X),I),'BstarB':eq(mm(tr(B),B),Gi),'XstarX':eq(mm(tr(X),X),I),'distinct':B!=X,'rank_two_minor':A[0][1]*A[1][2]-A[0][2]*A[1][1]==1}
# Sparse polynomial arithmetic in real/imaginary coordinates (a,b,c,d).
class P:
 def __init__(self,x=0): self.d=x if isinstance(x,dict) else ({(0,0,0,0):F(x)} if x else {})
 def __add__(self,x):
  x=x if isinstance(x,P) else P(x);d=self.d.copy()
  for m,c in x.d.items(): d[m]=d.get(m,F(0))+c
  return P({m:c for m,c in d.items() if c})
 __radd__=__add__
 def __neg__(self): return P({m:-c for m,c in self.d.items()})
 def __sub__(self,x): return self+-asP(x)
 def __rsub__(self,x): return asP(x)+-self
 def __mul__(self,x):
  x=asP(x);d={}
  for m,c in self.d.items():
   for n,e in x.d.items():
    k=tuple(a+b for a,b in zip(m,n));d[k]=d.get(k,F(0))+c*e
  return P({m:c for m,c in d.items() if c})
 __rmul__=__mul__
 def __pow__(self,n):
  r=P(1)
  for _ in range(n):r=r*self
  return r
 def __eq__(self,x): return self.d==asP(x).d
 def __truediv__(self,x): return self*F(1,x)
def asP(x):return x if isinstance(x,P) else P(x)
a,b,c,d=[P({tuple(int(j==i) for j in range(4)):F(1)}) for i in range(4)]
y0sq=a*a+b*b;y1sq=c*c+d*d
outB=( (a+c)**2+(b+d)**2+(2*a-c)**2+(2*b-d)**2+(-a+2*c)**2+(-b+2*d)**2 )/9
checks['complex_B_action_norm_identity']=outB+((a+c)**2+(b+d)**2)/3==y0sq+y1sq
checks['complex_competitor_norm_identity']=a*a+b*b+(1-a)**2+b*b+(-1-a)**2+b*b==2+3*(a*a+b*b)
checks['fourth_power_comparison_residual']=2*(y0sq**2+y1sq**2)-(y0sq+y1sq)**2==(y0sq-y1sq)**2
v=[[F(1)],[F(-1)]]
checks['attaining_images']=mm(B,v)==mm(X,v)==[[F(0)],[F(1)],[F(-1)]]
assert all(checks.values()),checks
out={'method':'independent Fraction matrix arithmetic and exact sparse real-coordinate polynomial expansion','checks':checks,'all_pass':True,'limits':'Does not establish Lean elaboration or all-k MI-03 roots; those are source-reviewed separately.'}
Path('/private/tmp/nla-187-192-exact-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
