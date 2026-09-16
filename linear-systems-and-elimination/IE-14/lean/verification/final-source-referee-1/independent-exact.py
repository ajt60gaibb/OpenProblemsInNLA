from fractions import Fraction as F
from pathlib import Path
import json,random
checks=[]
def ck(name,cond):assert cond,name;checks.append(name)
def fib(n):
 a,b=0,1
 for _ in range(n):a,b=b,a+b
 return a
class Q:
 def __init__(self,r=0,i=0):self.r=F(r);self.i=F(i)
 @staticmethod
 def coerce(x):return x if isinstance(x,Q) else Q(x)
 def __add__(self,z):z=Q.coerce(z);return Q(self.r+z.r,self.i+z.i)
 __radd__=__add__
 def __neg__(self):return Q(-self.r,-self.i)
 def __sub__(self,z):return self+-Q.coerce(z)
 def __mul__(self,z):z=Q.coerce(z);return Q(self.r*z.r-self.i*z.i,self.r*z.i+self.i*z.r)
 __rmul__=__mul__
 def __truediv__(self,z):z=Q.coerce(z);d=z.n2();assert d;return Q((self.r*z.r+self.i*z.i)/d,(self.i*z.r-self.r*z.i)/d)
 def __eq__(self,z):z=Q.coerce(z);return self.r==z.r and self.i==z.i
 def n2(self):return self.r*self.r+self.i*self.i
 def __repr__(self):return f'{self.r}+({self.i})i'
def mat(n,fun):return [[fun(i,j) for j in range(n)] for i in range(n)]
def mm(A,B):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*B)] for row in A]
def allowed(n,i,j):return abs(i-j)<=1 or (i,j) in [(0,n-1),(n-1,0)]
def setup(n):
 L=mat(n,lambda i,j: F(1 if i==j else -1 if i-j in [1,2] else 0))
 U=mat(n,lambda i,j: F(fib(n+1)+1 if i==j else fib(i+2)) if j==n-1 else F(1,2) if (i,j) in [(0,1),(1,1)] else F(i==j))
 C=mm(L,U);idx=lambda i:0 if i==0 else 1 if i==n-1 else i+1
 A=[C[idx(i)][:] for i in range(n)]
 return L,U,C,A,idx

# Referee's exact front/original-label diagnostic; finite diagnostic, not a theorem.
phase=[Q(1),Q(0,1),Q(-1),Q(0,-1)]
rng=random.Random(9151414)
visited=0;edges=0;dead=0
def inspect(A):
 n=len(A)
 def visit(S,k,labels,r,s):
  global visited,edges,dead
  visited+=1
  E=2 if max(z.n2() for row in A for z in row)==4 else 1
  def max_le(j,C):return max(S[r][j].n2(),S[s][j].n2())<=C*C
  def sum_le(j,C):
   a,b=S[r][j].n2(),S[s][j].n2();gap=C*C-a-b
   return C>=0 and gap>=0 and gap*gap>=4*a*b
  for j in range(k,n):
   ck(f'all active column bound {visited}/{j}',all(S[i][j].n2()<=((fib(n+1)+1)*E)**2 for i in range(k,n)))
   if j==n-1:
    if k<=n-3:ck(f'last Fibonacci envelope {visited}',max_le(j,fib(k+2)*E) and sum_le(j,fib(k+3)*E))
    else:ck(f'last sum before final {visited}',sum_le(j,(fib(n+1)+1)*E))
   elif j==n-2:
    if k<=n-4:ck(f'penultimate zero run {visited}',max_le(j,fib(k+1)*E) and sum_le(j,fib(k+2)*E))
    elif k==n-3:ck(f'penultimate transition {visited}',max_le(j,2*fib(n-3)*E) and sum_le(j,(fib(n-1)+1)*E))
    else:ck(f'penultimate last active stage {visited}',max_le(j,(fib(n-1)+1)*E))
   elif j==1:ck(f'second column {visited}',max_le(j,2*E))
   elif 2<=j<=n-3:
    if k<=j-2:ck(f'middle zero run {visited}/{j}',max_le(j,0) and sum_le(j,0))
    elif k==j-1:ck(f'middle first arrival {visited}/{j}',max_le(j,E) and sum_le(j,2*E))
    else:ck(f'middle last active stage {visited}/{j}',max_le(j,2*E))
  ck(f'front state {visited}',k<=r<n and k<=s<n and r!=s and
    (labels[r]<=k or labels[r]==n-1) and (labels[s]<=k or labels[s]==n-1) and
    all(k<labels[i]<n-1 for i in range(k,n) if i not in [r,s]) and
    all(labels.index(a)>=k and all(S[labels.index(a)][j]==A[a][j] for j in range(k,n)) for a in range(k+1,n-1)))
  if k==n-2:
   mx=max(S[i][k].n2() for i in range(k,n))
   if mx:
    for p in range(k,n):
     if S[p][k].n2()!=mx:continue
     B=[row[:] for row in S];B[k],B[p]=B[p],B[k]
     scalar=B[n-1][n-1]-B[n-1][k]/B[k][k]*B[k][n-1]
     ck(f'actual last scalar {visited}/{p}',scalar.n2()<=((fib(n+1)+1)*E)**2)
   return
  fresh=labels.index(k+1)
  ck(f'fresh distinct {visited}',fresh>=k and fresh not in [r,s])
  mx=max(S[i][k].n2() for i in range(k,n))
  if mx==0:dead+=1;return
  for p in range(k,n):
   if S[p][k].n2()!=mx:continue
   edges+=1
   ck(f'pivot front {edges}',p in [r,s,fresh])
   remaining=[s,fresh] if p==r else [r,fresh] if p==s else [r,s]
   swap=lambda x:p if x==k else k if x==p else x
   B=[row[:] for row in S];B[k],B[p]=B[p],B[k]
   lab=labels[:];lab[k],lab[p]=lab[p],lab[k]
   T=mat(n,lambda i,j:B[i][j]-B[i][k]/B[k][k]*B[k][j] if i>k and j>k else Q())
   visit(T,k+1,lab,swap(remaining[0]),swap(remaining[1]))
 visit(A,0,list(range(n)),0,n-1)
for sample in range(80):
 n=4+sample%5
 A=mat(n,lambda i,j:phase[rng.randrange(4)]*rng.choice([1,1,2]) if allowed(n,i,j) else Q())
 inspect(A)
for n in range(4,13):
 L,U,C,A,idx=setup(n);S=[r[:] for r in A]
 for k in range(n):
  stage=lambda i:idx(i) if k==0 else k if i==n-1 else i+1
  ck(f'full witness tail n{n} stage{k}',all(S[i][j]==sum(L[stage(i)][a]*U[a][j] for a in range(k,n)) for i in range(k,n) for j in range(k,n)))
  p=0 if k==0 else n-1;S[k],S[p]=S[p],S[k]
  S=mat(n,lambda i,j:S[i][j]-S[i][k]/S[k][k]*S[k][j] if i>k and j>k else F(0))
record={'result':'PASS finite exact full-column/front/last-scalar diagnostic, not universal proof','checks_count':len(checks),'front_states':visited,'admissible_tie_edges':edges,'dead_partial_paths':dead,'complex_samples':80,'sample_dimensions':[4,5,6,7,8],'full_active_witness_tail_orders':list(range(4,13)),'checks':checks,'arithmetic':'fractions.Fraction and exact Gaussian rational pairs; reused own prior helper definitions'}
Path(__file__).with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='checks'}))
