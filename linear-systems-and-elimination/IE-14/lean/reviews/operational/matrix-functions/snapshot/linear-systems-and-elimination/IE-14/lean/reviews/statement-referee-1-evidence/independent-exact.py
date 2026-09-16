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
summaries=[]
for n in range(4,31):
 L,U,C,A,idx=setup(n);bound=F(fib(n+1)+1)
 ck(f'n{n} permitted support and both corners',all(not A[i][j] or allowed(n,i,j) for i in range(n) for j in range(n)) and A[0][-1]==1 and A[-1][0]==-1)
 ck(f'n{n} normalized entry max',max(abs(x) for row in A for x in row)==1)
 ck(f'n{n} factor assignment invertible permutation',sorted(idx(i) for i in range(n))==list(range(n)))
 ck(f'n{n} upper nonzero diagonal and lower unit triangular',all(U[i][i]!=0 and L[i][i]==1 for i in range(n)) and all(U[i][j]==0 for i in range(n) for j in range(i)) and all(L[i][j]==0 for i in range(n) for j in range(i+1,n)))
 S=[r[:] for r in A];labels=list(range(n));growth=F(1);pivots=[]
 for k in range(n):
  p=0 if k==0 else n-1
  ck(f'n{n} stage{k} literal active pivot maximal',p>=k and S[p][k]!=0 and all(abs(S[i][k])<=abs(S[p][k]) for i in range(k,n)))
  ck(f'n{n} stage{k} factor-column identity',all(S[i][k]==L[idx(labels[i])][k]*U[k][k] for i in range(k,n)))
  growth=max(growth,max(abs(S[i][j]) for i in range(k,n) for j in range(k,n)))
  S[k],S[p]=S[p],S[k];labels[k],labels[p]=labels[p],labels[k]
  ck(f'n{n} stage{k} chosen full row matches U',all(S[k][j]==U[k][j] for j in range(k,n)))
  pivots.append(S[k][k]);T=mat(n,lambda i,j:S[i][j]-S[i][k]/S[k][k]*S[k][j] if i>k and j>k else F(0));S=T
 ck(f'n{n} original label path no preliminary permutation',labels==[0,n-1,*range(1,n-1)])
 ck(f'n{n} exact sharp growth all active entries',growth==bound)
 ck(f'n{n} last scalar equals bound',pivots[-1]==bound)
 summaries.append({'n':n,'growth':str(growth),'pivots':[str(x) for x in pivots]})
# Exact complex phase transforms verify genuine Gaussian arithmetic and all-active-stage conventions.
phase=[Q(1),Q(0,1),Q(-1),Q(0,-1)]
for n in range(4,10):
 _,_,_,A,_=setup(n);S=mat(n,lambda i,j:Q(2,1)*phase[i%4]*A[i][j]*phase[(j+1)%4]);base=max(x.n2() for row in S for x in row);peak=base
 for k in range(n):
  p=0 if k==0 else n-1
  ck(f'complex n{n} stage{k} actual maximal modulus tie',S[p][k]!=0 and all(S[i][k].n2()<=S[p][k].n2() for i in range(k,n)))
  peak=max(peak,max(S[i][j].n2() for i in range(k,n) for j in range(k,n)))
  S[k],S[p]=S[p],S[k];S=mat(n,lambda i,j:S[i][j]-S[i][k]/S[k][k]*S[k][j] if i>k and j>k else Q())
 ck(f'complex n{n} exact squared growth',peak/base==(fib(n+1)+1)**2)
# Enumerate every admissible pivot tie for bounded, reproducible independent samples.
rng=random.Random(9142026);tie_runs=[]
def all_paths(A):
 n=len(A);base=max(x.n2() for row in A for x in row)
 def visit(S,k,peak):
  active=max(S[i][j].n2() for i in range(k,n) for j in range(k,n));peak=max(peak,active)
  mx=max(S[i][k].n2() for i in range(k,n))
  if mx==0:return []
  if k==n-1:return [peak/base]
  out=[]
  for p in range(k,n):
   if S[p][k].n2()!=mx:continue
   B=[row[:] for row in S];B[k],B[p]=B[p],B[k]
   T=mat(n,lambda i,j:B[i][j]-B[i][k]/B[k][k]*B[k][j] if i>k and j>k else Q())
   out+=visit(T,k+1,peak)
  return out
 return visit(A,0,base)
for sample in range(40):
 n=4 if sample<32 else 5
 A=mat(n,lambda i,j:phase[rng.randrange(4)]*rng.choice([1,1,2]) if allowed(n,i,j) else Q())
 values=all_paths(A)
 ck(f'complex all-tie sample{sample} upper bound',all(x<=(fib(n+1)+1)**2 for x in values))
 tie_runs.append({'sample':sample,'n':n,'complete_paths':len(values),'singular':not values,'max_squared_growth':str(max(values)) if values else None})
ck('initial Fibonacci sharp values',[fib(n+1)+1 for n in range(4,8)]==[6,9,14,22])
record={'reviewer':'OpenAI GPT-6 Codex /root/reference_api_review, independent non-implementing AI','phase':'independent IE14 pre-proof numerical diagnostics; no universal proof','result':'PASS','checks_count':len(checks),'checks':checks,'witnesses':summaries,'complex_phase_orders':[4,5,6,7,8,9],'all_tie_sample_results':tie_runs,'total_complete_tie_paths':sum(x['complete_paths'] for x in tie_runs),'contributor_checker_imported_or_executed':False}
Path(__file__).with_suffix('.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({'result':'PASS','checks':len(checks),'complete_tie_paths':record['total_complete_tie_paths']}))
