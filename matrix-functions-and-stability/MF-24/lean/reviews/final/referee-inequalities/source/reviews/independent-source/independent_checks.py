"""Supplementary exact checks only; no Lean execution or universal certificate.
The symbolic compressed identity is checked over a polynomial ring; finite
family checks are diagnostic and do not replace the source induction proofs.
"""
from fractions import Fraction as F
from collections import defaultdict
import json
from pathlib import Path

NV=8
ZERO=(0,)*NV
class P:
    def __init__(self, v=0): self.d=dict(v) if isinstance(v,dict) else ({ZERO:F(v)} if v else {})
    @staticmethod
    def var(i):
        e=list(ZERO);e[i]=1;return P({tuple(e):F(1)})
    def __add__(self,b):
        if not isinstance(b,P): b=P(b)
        d=defaultdict(F,self.d)
        for e,c in b.d.items():d[e]+=c
        return P({e:c for e,c in d.items() if c})
    __radd__=__add__
    def __neg__(self): return P({e:-c for e,c in self.d.items()})
    def __sub__(self,b):return self+-b if isinstance(b,P) else self+P(-b)
    def __mul__(self,b):
        if not isinstance(b,P):b=P(b)
        d=defaultdict(F)
        for e,c in self.d.items():
            for f,k in b.d.items():d[tuple(x+y for x,y in zip(e,f))]+=c*k
        return P({e:c for e,c in d.items() if c})
    __rmul__=__mul__
    def __eq__(self,b):return self.d==(b.d if isinstance(b,P) else P(b).d)

def mm(a,b):return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]
def mv(a,v):return [sum(x*y for x,y in zip(r,v)) for r in a]
def K(u,rho,a):return [[u+a,-rho*a],[1,0]]

p00,p01,p10,p11,u,rho,a,b=[P.var(i) for i in range(NV)]
M=[[p00,p01],[p10,p11]]
R,S=mm(M,K(u,rho,a)),mm(M,K(u,rho,b))
v=mv(M,[u,1])
assert mv(mm(R,S),v)[0]-mv(mm(S,R),v)[0]==0
tr=p00+p11;det=p00*p11-p01*p10
sq=mm(M,M)
for i in range(2):
 for j in range(2):assert sq[i][j]-tr*M[i][j]+det*(i==j)==0

cases=0;vertices=0;classes=0;word_edges=0
for m in range(2,21):
 for t in [F(3,2),F(2),F(m)]:
  k,D,N=m+1,m+2,(m+1)**2
  U=[t]+[F(1)]*(m-1);inv=[F(1,t)]+U
  wx=U+[F(1)]+U+inv*(m-1)
  wy=U+inv*(m-1)+[F(1)]+U
  assert len(wx)==len(wy)==N-1==m*D
  hx=lambda v:int(v%k>=1)+int(v//k>=1)
  hy=lambda v:int(v%k>=1)+int(v//k==m)
  assert hx(0)==hy(0)==0
  for w,h in [(wx,hx),(wy,hy)]:
   for r in range(N-1): assert w[r]==t**h(r+1)/t**h(r)
  word_edges+=2*(N-1)
  px=F(1);py=F(1);e=F(0)
  for r in range(1,N):
   px*=wx[r-1];py*=wy[r-1]
   if r%D==0:e+=px*px
  assert e==t**4*m and py==t**2
  for c in range(D):
   C=list(range(c,N,D));H=[hy(v) for v in C]
   assert len(C)<=m+1 and H.count(0)<=1 and H.count(2)<=1
   W=sum(t**(2*h) for h in H);I=sum(t**(-2*h) for h in H)
   assert W<=t**4+m*t**2 and I<=1+F(m,t*t)
   assert W*I<=(t*t+m)**2
   classes+=1
  for uu,rr in [(F(7,3),F(5)),(F(0),F(0)),(F(-2),F(1))]:
   def transfer(w):
    v=[uu,F(1)]
    for x in w:v=mv(K(uu,rr,x*x),v)
    return v[0]
   assert transfer(wx)==transfer(wy)
  vertices+=N;cases+=1

# Independently compute actual products and full polynomial support in modest
# complete dimensions, retaining every entry. No matrix norm is sampled.
entry_checks=0
for m in range(2,8):
 t=F(3,2);N=(m+1)**2;D=m+2;k=m+1
 U=[t]+[F(1)]*(m-1);inv=[1/t]+U
 for w,h in [(U+[F(1)]+U+inv*(m-1),lambda v:int(v%k>=1)+int(v//k>=1)),
             (U+inv*(m-1)+[F(1)]+U,lambda v:int(v%k>=1)+int(v//k==m))]:
  for r in range(N):
   prod=F(1)
   for s in range(N):
    if s>r:prod*=w[s-1]
    actual=prod if s>r and (s-r)%D==0 else F(0)
    predicted=t**h(s)/t**h(r) if s>r and (s-r)%D==0 else F(0)
    assert actual==predicted
    entry_checks+=1
out={'status':'supplementary exact diagnostic checks passed; not Lean verification',
'compressed_commutator':'zero polynomial in eight independent variables',
'generic_2x2_cayley_hamilton':'all four zero polynomial entries',
'finite_family_cases':cases,'word_edges_checked':word_edges,'vertices_retained':vertices,
'full_residue_classes_checked':classes,'full_polynomial_entries_checked':entry_checks,
'complex_vector_energy':'reviewed analytically in Lean source; not sampled',
'local_lean_execution':False,'universal_problem_verification':False}
Path(__file__).with_name('CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
