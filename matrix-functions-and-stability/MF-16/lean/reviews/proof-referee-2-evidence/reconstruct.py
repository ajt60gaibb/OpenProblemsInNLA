"""Independent exact MF16 reconstruction from the freshly elaborated AST/data.
Standard-library Fraction intervals/AD and sparse matrix polynomials; no author
checker imported. These diagnostics are not Lean proof assumptions.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
import json
E=Path(__file__).resolve().parent
raw=(E/'reviews-proof-referee-2-evidence-Inspect.log').read_text()
lines=[s.removeprefix('ACTUAL_DATA ') for s in raw.splitlines() if s.startswith('ACTUAL_DATA ')]
assert len(lines)==1
data=json.loads(lines[0]);(E/'actual-numerics.json').write_text(json.dumps(data,indent=2)+'\n')
q=lambda x:Q(int(x[0]),int(x[1]))
class I:
 def __init__(self,a,b=None): self.lo=Q(a);self.hi=Q(a if b is None else b);assert self.lo<=self.hi
 def __add__(a,b):
  if not isinstance(b,I):b=I(b)
  return I(a.lo+b.lo,a.hi+b.hi)
 __radd__=__add__
 def __neg__(a):return I(-a.hi,-a.lo)
 def __sub__(a,b):return a+-b
 def __mul__(a,b):
  if not isinstance(b,I):b=I(b)
  z=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi];return I(min(z),max(z))
 __rmul__=__mul__
 def bound(a):return max(abs(a.lo),abs(a.hi))
 def asjson(a):return [str(a.lo),str(a.hi)]
 def same(a,b):return (a.lo,a.hi)==(b.lo,b.hi)
class D:
 def __init__(self,v,d=None):self.v=v;self.d=[I(0)]*3 if d is None else d
 def __add__(a,b):return D(a.v+b.v,[x+y for x,y in zip(a.d,b.d)])
 def __neg__(a):return D(-a.v,[-x for x in a.d])
 def __mul__(a,b):return D(a.v*b.v,[x*b.v+a.v*y for x,y in zip(a.d,b.d)])
def evaluate(e,vs,const):
 tag=e[0]
 if tag=='const':return const(q(e[1]))
 if tag=='var':assert 0<=int(e[1])<3;return vs[int(e[1])]
 if tag=='neg':return -evaluate(e[1],vs,const)
 assert tag in ('add','mul'),e
 a=evaluate(e[1],vs,const);b=evaluate(e[2],vs,const)
 return a+b if tag=='add' else a*b
m=list(map(q,data['center']));box=[I(q(x[0]),q(x[1])) for x in data['box']]
C=[[q(x) for x in r] for r in data['C']]
r=Q(1,10000000)
assert all(x.lo==c-r and x.hi==c+r for x,c in zip(box,m)) and box[0].lo>3
vs=[D(x,[I(int(i==j)) for j in range(3)]) for i,x in enumerate(box)]
J=[evaluate(e,vs,lambda x:D(I(x))).d for e in data['F']]
observedJ=[[I(q(x[0]),q(x[1])) for x in row] for row in data['J']]
assert all(J[i][j].same(observedJ[i][j]) for i in range(3) for j in range(3))
R=[[I(int(i==j))-sum((C[i][k]*J[k][j] for k in range(3)),I(0)) for j in range(3)] for i in range(3)]
bound=max(sum(x.bound() for x in row) for row in R)
assert bound==q(data['q']) and bound<Q(27,1000)<1
values=[evaluate(e,m,Q) for e in data['F']]
newton=[m[i]-sum(C[i][j]*values[j] for j in range(3)) for i in range(3)]
image=[I(x-bound*r,x+bound*r) for x in newton]
assert all(x.same(I(q(y[0]),q(y[1]))) for x,y in zip(image,data['newtonImage']))
assert all(b.lo<a.lo and a.hi<b.hi for a,b in zip(image,box))
assert q(data['radius'])==r
pre_det=(C[0][0]*(C[1][1]*C[2][2]-C[1][2]*C[2][1])-C[0][1]*(C[1][0]*C[2][2]-C[1][2]*C[2][0])+C[0][2]*(C[1][0]*C[2][1]-C[1][1]*C[2][0]))
assert pre_det==Q(790668616748253,62500000000000000000000000000) and pre_det!=0
class P:
 def __init__(self,d=0):self.d={k:Q(v) for k,v in d.items() if v} if isinstance(d,dict) else ({(0,0,0):Q(d)} if d else {})
 def __add__(a,b):
  if not isinstance(b,P):b=P(b)
  d=a.d.copy()
  for k,v in b.d.items():d[k]=d.get(k,0)+v
  return P(d)
 __radd__=__add__
 def __neg__(a):return P({k:-v for k,v in a.d.items()})
 def __sub__(a,b):return a+-b
 def __rsub__(a,b):return P(b)+-a
 def __mul__(a,b):
  if not isinstance(b,P):b=P(b)
  d={}
  for u,x in a.d.items():
   for v,y in b.d.items():
    k=tuple(i+j for i,j in zip(u,v));d[k]=d.get(k,0)+x*y
  return P(d)
 __rmul__=__mul__
 def __pow__(a,n):
  out=P(1)
  for _ in range(n):out=out*a
  return out
 def eq(a,b):return a.d==(b.d if isinstance(b,P) else P(b).d)
 def reduce_det_three(a):
  d={}
  for (x,y,z),v in a.d.items():
   n=min(x,z)
   for k in range(n+1):
    e=(x-n,y+2*k,z-n);d[e]=d.get(e,0)+v*comb(n,k)*3**(n-k)
  return P(d)
def mm(A,B):return [[sum((A[i][k]*B[k][j] for k in range(2)),P()) for j in range(2)] for i in range(2)]
def mp(A,k):
 out=[[P(1),P()],[P(),P(1)]]
 for _ in range(k):out=mm(out,A)
 return out
x,y,z=[P({tuple(int(i==j) for j in range(3)):1}) for i in range(3)]
S=[[x,y],[y,z]];B=[[P(1),P(4)],[P(4),P(17)]];s=x+z;t=s*s
u=s*(t*(t*(t*(t*(t-30)+324)-1512)+2835)-1458)
v=3*(t*(t*(t*(t*(t-27)+252)-945)+1215)-243)
S12=mp(S,12);reduced=[[u*S[i][j]-v*int(i==j) for j in range(2)] for i in range(2)]
assert all(not (S12[i][j]-reduced[i][j]).reduce_det_three().d for i in range(2) for j in range(2))
word=mm(mm(mm(mm(S,B),S12),B),S);rw=mm(mm(mm(mm(S,B),reduced),B),S)
F=[evaluate(e,[x,y,z],P) for e in data['F']]
assert F[0].eq(x*z-y*y-3)
assert F[1].eq(rw[0][0]-4783113) and F[2].eq(rw[0][1]-6377496)
assert all(not (word[i][j]-rw[i][j]).reduce_det_three().d for i in range(2) for j in range(2))
assert word[0][1].eq(word[1][0])
assert (word[0][0]*word[1][1]-word[0][1]*word[1][0]).eq((x*z-y*y)**14)
def mi(A,B):return [[sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
X0=[[3,0],[0,1]];B0=[[1,4],[4,17]];X12=[[3**12,0],[0,1]]
P0=mi(mi(mi(mi(X0,B0),X12),B0),X0)
assert P0==[[4783113,6377496],[6377496,8503345]]
assert P0[0][0]*P0[1][1]-P0[0][1]**2==3**14
assert Q(3**14+P0[0][1]**2,P0[0][0])==P0[1][1]
word_letters=['X','B']+['X']*12+['B','X']
assert word_letters==word_letters[::-1] and word_letters.count('X')==14 and word_letters.count('B')==2
result={'scope':'Independent exact diagnostics; no Lean proof oracle.',
 'AST_supported_fragment':['const','var','add','mul','neg'],'exact_all_J_endpoints_match':True,
 'exact_contraction':str(bound),'contraction_float_for_orientation':float(bound),
 'strict_self_map':True,'preconditioner_det':str(pre_det),'radius':str(r),
 'x_box_entirely_above_three':True,'newton_images':[x.asjson() for x in image],
 'center_displacement':str(max(abs(x-y) for x,y in zip(m,newton))),
 'actual_source_word_matrix':P0,'source_determinant':3**14,
 'all_four_twelfth_power_entries_mod_det_three':True,
 'both_Expr_residuals_equal_actual_reduced_entries':True,
 'all_four_word_entries_mod_det_three':True,'actual_word_symmetric':True,
 'full_polynomial_determinant_identity':True,'remaining_entry_recovery':True,'word_palindrome_counts':True}
(E/'exact-diagnostics.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS actual AST, full interval Jacobian/enclosure, polynomial matrix/CH/determinant identities.')
