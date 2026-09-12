from fractions import Fraction as Q
from itertools import product
import json
A=[[Q(2),Q(1)],[Q(1),Q(2)]]
def f2(S): return sum((v*v for row in S for v in row),Q(0))
def update(S,p):
 if p is None: return [[Q(0) for _ in range(2)] for _ in range(2)]
 i,j=p
 if S[i][j]==0: return S
 return [[S[a][b]-S[a][j]*S[i][b]/S[i][j] for b in range(2)] for a in range(2)]
def mass(S,p):
 if f2(S)==0: return Q(int(p is None))
 if p is None: return Q(0)
 i,j=p
 return S[i][j]**2/f2(S)
labels=[None]+list(product(range(2),repeat=2))
rows=[]
for p in labels:
 S=update(A,p)
 rows.append({'pivot':p,'mass':str(mass(A,p)),'residual':[[str(v) for v in row] for row in S],'frobenius_sq':str(f2(S)),'contribution':str(mass(A,p)*f2(S))})
E=sum((mass(A,p)*f2(update(A,p)) for p in labels),Q(0))
assert E==Q(18,5)
assert sum((mass(A,p) for p in labels),Q(0))==1
G=[[sum((A[t][i]*A[t][j] for t in range(2)),Q(0)) for j in range(2)] for i in range(2)]
assert G==[[Q(5),Q(4)],[Q(4),Q(5)]]
# Distinct Gram eigenvectors (1,1),(1,-1) span the two-dimensional space.
eigs=[]
for ev,v in [(Q(9),[Q(1),Q(1)]),(Q(1),[Q(1),Q(-1)])]:
 gv=[sum((G[i][j]*v[j] for j in range(2)),Q(0)) for i in range(2)]
 assert gv==[ev*x for x in v]
 eigs.append({'eigenvalue':str(ev),'eigenvector':[str(x) for x in v]})
assert 3**2==9 and 1**2==1 and 3>1>0
hist=[]
for k in range(4):
 total=Q(0); error=Q(0); positive=0
 for h in product(labels,repeat=k):
  S=A; w=Q(1)
  for p in h:
   w*=mass(S,p)
   S=update(S,p)
  total+=w; error+=w*f2(S)
  positive+=w>0
 assert total==1
 hist.append({'k':k,'history_count':len(labels)**k,'positive_history_count':positive,'total_mass':str(total),'expected_squared_error':str(error)})
print(json.dumps({'method':'Independent exact rational direct rank-one updates, not supplied tables or manuscript cancellation formulas.','matrix':[[str(v) for v in row] for row in A],'frobenius_sq':str(f2(A)),'gram':[[str(v) for v in row] for row in G],'gram_eigenpairs':eigs,'ordered_singular_values':['3','1'],'pivot_outcomes':rows,'history_checks':hist,'singular_tail_k1':'1','proposed_bound':'2','actual_expected_error':str(E),'strict_gap':str(E-Q(2)),'all_assertions_passed':True,'scope':'Finite reconstruction supports statement review and is not a universal proof certificate.'},indent=2))
