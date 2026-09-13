import itertools as it, numpy as np, json, sys
from pathlib import Path
root=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[1]/"submitted"
mons=list(it.combinations_with_replacement(range(9),4)); exps=[[m.count(i) for i in range(9)] for m in mons]
subsets=list(it.combinations(range(9),4))
def deriv(e,j,I):
 if not e[j]:return 0
 return e[j] if all(e[k]-(k==j)==0 for k in range(9) if k not in I) else 0
A=[]
for tup in subsets:
 I=set(tup);outside=sorted(set(range(9))-I)
 D=[[deriv(e,j,I) for e in exps] for j in range(9)]
 A.extend(D[j] for j in tup)
 A.extend([a-b for a,b in zip(D[j],D[outside[0]])] for j in outside[1:])
A=np.array(A,dtype=np.int64)
def mul(a,b):
 out={}
 for x,c in a.items():
  for y,d in b.items():
   m=tuple(sorted(x+y));out[m]=out.get(m,0)+c*d
 return out
def plus(*terms):
 out={}
 for c,p in terms:
  for m,v in p.items():out[m]=out.get(m,0)+c*v
 return out
sigma={(i,):1 for i in range(9)}; s2={(i,i):1 for i in range(9)}
q=plus((4,s2),(-1,mul(sigma,sigma)))
z=[plus((4,{(i,i):1}),(-1,mul(sigma,{(i,):1}))) for i in range(9)]
h=plus((32,{(i,i,i):1 for i in range(9)}),(-12,mul(sigma,s2)),(1,mul(mul(sigma,sigma),sigma)))
polys=[mul(q,{(i,j):1}) for i,j in it.combinations(range(9),2)]+[mul(z[i],z[j]) for i,j in it.combinations_with_replacement(range(9),2)]+[mul(h,{(i,):1}) for i in range(9)]
F=np.array([[p.get(m,0) for p in polys] for m in mons],dtype=np.int64)
assert not (A@F).any()
archive=np.load(root/'verification/quartic_matrices.npz');assert np.array_equal(A,archive['constraints']) and np.array_equal(F,archive['basis'])
def rank(mat,p=1000033):
 a=mat.copy()%p;r=0
 for j in range(a.shape[1]):
  nz=np.where(a[r:,j]!=0)[0]
  if not len(nz):continue
  i=r+int(nz[0]);a[[i,r]]=a[[r,i]];a[r]=a[r]*pow(int(a[r,j]),-1,p)%p
  a[r+1:]=(a[r+1:]-a[r+1:,j,None]*a[r])%p
  r+=1
  if r==a.shape[0]:break
 return r
p=1000033
assert all(p%d for d in range(2,int(p**.5)+1))
assert rank(A)==405 and rank(F)==90 and rank(F[:,:81])==81
E=np.array([[int(i in I) for i in range(9)] for I in subsets]);D=4-E@E.T
W=np.array([[int(set(pair)<=set(I)) for pair in it.combinations(range(9),2)] for I in subsets])
assert np.array_equal(D*D,16*np.ones_like(D)-7*E@E.T+2*W@W.T)
assert rank(D*D)==36 and rank(W)==36
f=(1-E[:,0])*(2-E[:,2]-E[:,3]);g=E[:,0]*(2*E[:,2]-1)
sums=[int(f[(E[:,a]==0)&(E[:,b]!=E[:,c])].sum()) for a in range(9) for b,c in it.combinations([i for i in range(9) if i!=a],2)]
assert min(sums)==10 and len(sums)==252 and (f>0).sum()==55 and (g!=0).sum()==56 and not (f*g).any()
print(json.dumps({'status':'PASS','independent_prime':p,'constraint_rank':405,'basis_rank':90,'restricted_rank':81,'integer_AF_zero':True,'matches_archived_arrays':True,'square_rank':36,'pair_incidence_rank':36,'witness_support':[55,56],'covering_minimum':10},indent=2))
