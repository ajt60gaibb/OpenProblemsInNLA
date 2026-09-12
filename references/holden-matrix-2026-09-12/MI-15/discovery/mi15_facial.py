from mi15_gram import setup
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
import argparse,json,time

def facial(n,K):
 vals,pairs,C,Q0,zero,keep,free,forced,ii,jj,sg=setup(n)
 kp={i:j for j,i in enumerate(keep)};d=len(keep);v=len(free)
 W=np.zeros((d,K),dtype=int)
 for k in range(1,K+1):
  for i,old in enumerate(keep):
   a,b=pairs[old]
   if b-a==2*(n-1)-k:W[i,k-1]=1
 coeff={}
 for a,(_,loc) in enumerate(free):
  for oi,oj,s in loc:
   i,j=kp[oi],kp[oj]
   coeff[i,j]=(a,s);coeff[j,i]=(a,s)
 base=Q0[np.ix_(keep,keep)]
 equations=[]
 for k in range(K):
  support=np.flatnonzero(W[:,k])
  for i in range(d):
   eq={v:F(-sum(int(base[i,j]) for j in support))}
   for j in support:
    if (i,j) in coeff:
     a,s=coeff[i,j];eq[a]=eq.get(a,F(0))+F(s)
   equations.append({a:b for a,b in eq.items() if b})
 rows={}
 for eq in equations:
  eq=dict(eq)
  while any(a!=v for a in eq):
   p=min(a for a in eq if a!=v)
   c=eq[p]
   if p not in rows:
    rows[p]={a:b/c for a,b in eq.items()};break
   rr=rows[p]
   for a,b in rr.items():
    eq[a]=eq.get(a,F(0))-c*b
    if not eq[a]:del eq[a]
  else:
   if eq.get(v,0):raise ValueError('inconsistent')
 independent=[a for a in range(v) if a not in rows];imap={a:j for j,a in enumerate(independent)}
 expr={a:({imap[a]:F(1)},F(0)) for a in independent}
 for p in sorted(rows,reverse=True):
  eq=rows[p]; out={};const=eq.get(v,F(0))
  for a,c in eq.items():
   if a in (p,v):continue
   aa,bb=expr[a];const-=c*bb
   for b,cc in aa.items():out[b]=out.get(b,F(0))-c*cc
  expr[p]=({a:b for a,b in out.items() if b},const)
 const=np.array([float(expr[a][1]) for a in range(v)])
 N=np.zeros((v,len(independent)))
 for a in range(v):
  for b,c in expr[a][0].items():N[a,b]=float(c)
 # Required convention: equations stored sum coeff*t = right hand side.
 print('n',n,'K',K,'constraints rank',len(rows),'free',len(independent),flush=True)
 return (vals,pairs,C,Q0,zero,keep,free,forced,ii,jj,sg),W,expr,independent,const,N

def solve(n,K,margin,maxiter):
 data,W,expr,ind,offset,N=facial(n,K)
 vals,pairs,C,Q0,zero,keep,free,forced,ii,jj,sg=data
 base=Q0[np.ix_(keep,keep)].astype(float);d=len(keep)
 P=(W/np.sqrt(np.sum(W*W,axis=0))) if K else np.zeros((d,0))
 shift=-margin*np.eye(d)+(1+margin)*P@P.T
 def make_t(t):
  Q=base.copy();Q[ii,jj]+=t[:,None]*sg;Q[jj,ii]+=t[:,None]*sg
  return Q
 def make(z):return make_t(offset+N@z)
 assert np.max(abs(make(np.zeros(len(ind)))@W),initial=0)<1e-9
 calls=[0];start=time.time()
 def fg(z):
  Q=make(z)+shift;w,V=np.linalg.eigh(Q);wn=np.minimum(w,0);neg=(V*wn)@V.T
  f=.5*wn@wn;g=N.T@(2*np.sum(neg[ii,jj]*sg,axis=1));calls[0]+=1
  if calls[0]%100==0:print('step',calls[0],'loss',f,'min complement',w[0]+margin,flush=True)
  return f,g
 out=Path(__file__).parent/f'mi15_n{n}_K{K}.npz';z0=np.zeros(len(ind))
 if out.exists():z0=np.load(out)['z']
 print('start min',np.linalg.eigvalsh(make(z0)+P@P.T)[0],flush=True)
 r=minimize(fg,z0,jac=True,method='L-BFGS-B',options={'maxiter':maxiter,'ftol':1e-30,'gtol':1e-10,'maxls':40,'maxcor':30})
 Q=make(r.x);t=offset+N@r.x
 np.savez(out,z=r.x,t=t,Q=Q,W=W,eigenvalues=np.linalg.eigvalsh(Q))
 desc={'n':n,'K':K,'independent':ind,'expressions':[{ 'constant':str(expr[a][1]),'coefficients':{str(b):str(c) for b,c in expr[a][0].items()}} for a in range(len(free))]}
 out.with_suffix('.json').write_text(json.dumps(desc,indent=2))
 print('final',r.message,r.fun,'eigs',np.linalg.eigvalsh(Q)[:12],'time',time.time()-start,flush=True)

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=8);ap.add_argument('--K',type=int,default=3);ap.add_argument('--margin',type=float,default=.01);ap.add_argument('--maxiter',type=int,default=3000);args=ap.parse_args()
 solve(args.n,args.K,args.margin,args.maxiter)
