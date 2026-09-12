from itertools import combinations
import numpy as np
from scipy.optimize import minimize
from pathlib import Path
import argparse, json, time


def setup(n):
 vals=[a for a in range(-(n-1),n) if a!=0]
 pairs=list(combinations(vals,2)); d=len(pairs); ind={p:i for i,p in enumerate(pairs)}
 C=np.zeros((n*n,d),dtype=np.int64)
 for i in range(n):
  for j in range(n):
   for k in range(n):
    a=i-k; b=k-j
    if a==0 or b==0 or a==b: continue
    if a<b: C[i*n+j,ind[a,b]]+=1
    else: C[i*n+j,ind[b,a]]-=1
 w=np.array([(n-abs(a))*(n-abs(b)) for a,b in pairs],dtype=np.int64)
 Q0=2*np.diag(w)-C.T@C
 zero=np.flatnonzero(np.diag(Q0)==0).tolist()
 constraints=[]; free=[]
 for abcd in combinations(vals,4):
  a,b,c,dv=abcd
  loc=[(ind[a,b],ind[c,dv],1),(ind[a,c],ind[b,dv],-1),(ind[a,dv],ind[b,c],1)]
  forced=[]
  for i,j,sgn in loc:
   if i in zero or j in zero: forced.append(-Q0[i,j]/sgn)
  if forced:
   assert all(v==forced[0] for v in forced)
   constraints.append((abcd,int(forced[0])))
   for i,j,sgn in loc: Q0[i,j]+=sgn*forced[0];Q0[j,i]+=sgn*forced[0]
  else: free.append((abcd,loc))
 assert np.max(np.abs(Q0[zero,:]),initial=0)==0
 keep=[i for i in range(len(pairs)) if i not in zero]; kp={i:j for j,i in enumerate(keep)}
 ii=np.array([[kp[i] for i,j,s in loc] for _,loc in free],dtype=int)
 jj=np.array([[kp[j] for i,j,s in loc] for _,loc in free],dtype=int)
 signs=np.array([1.,-1.,1.])
 return vals,pairs,C,Q0,zero,keep,free,constraints,ii,jj,signs


def solve(n,margin,maxiter):
 vals,pairs,C,Q0,zero,keep,free,forced,ii,jj,sg=setup(n)
 base=Q0[np.ix_(keep,keep)].astype(float)
 def make(t):
  Q=base.copy();Q[ii,jj]+=t[:,None]*sg;Q[jj,ii]+=t[:,None]*sg
  return Q
 calls=[0];start=time.time()
 def fg(t):
  Q=make(t)
  w,v=np.linalg.eigh(Q-margin*np.eye(len(keep)))
  wneg=np.minimum(w,0);neg=(v*wneg)@v.T
  f=.5*np.dot(wneg,wneg)
  grad=2*np.sum(neg[ii,jj]*sg,axis=1)
  calls[0]+=1
  if calls[0]%100==0: print('step',calls[0],'loss',f,'min_eig',w[0]+margin,'sec',round(time.time()-start,2),flush=True)
  return f,grad
 t0=np.zeros(len(free))
 prev=Path(__file__).parent/f'mi15_n{n}_float.npz'
 if prev.exists():t0=np.load(prev)['t']
 print('n',n,'matrix dimension',len(keep),'variables',len(free),'forced',len(forced),'starting min',np.linalg.eigvalsh(make(t0))[0],flush=True)
 res=minimize(fg,t0,jac=True,method='L-BFGS-B',options={'maxiter':maxiter,'ftol':1e-30,'gtol':1e-11,'maxls':40,'maxcor':30})
 Q=make(res.x); eig=np.linalg.eigvalsh(Q)
 np.savez(prev,t=res.x,Q=Q,margin=margin,eigenvalues=eig)
 print(res.message,'final minimum',eig[0],'loss',res.fun,'time',time.time()-start,flush=True)
 return res

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=8);ap.add_argument('--margin',type=float,default=.01);ap.add_argument('--maxiter',type=int,default=2000);args=ap.parse_args()
 solve(args.n,args.margin,args.maxiter)
