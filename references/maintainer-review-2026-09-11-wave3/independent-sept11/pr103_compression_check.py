#!/usr/bin/env python3
"""Independent diagnostic calculations for PR 103; not a proof or submission code."""
from decimal import Decimal as D, localcontext
from fractions import Fraction as F
import json
import numpy as np

# Exact rational check of the resolvent identities on a noncommuting 2x2 PSD A,C.
def mm(A,B): return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]
def add(A,B): return [[a+b for a,b in zip(x,y)] for x,y in zip(A,B)]
def scale(t,A): return [[t*x for x in row] for row in A]
def transpose(A): return [list(x) for x in zip(*A)]
def eye(n,typ=F): return [[typ(int(i==j)) for j in range(n)] for i in range(n)]
def inverse(A):
 n=len(A);M=[list(A[i])+eye(n,type(A[0][0]))[i] for i in range(n)]
 for j in range(n):
  q=next(i for i in range(j,n) if M[i][j]);M[j],M[q]=M[q],M[j]
  d=M[j][j];M[j]=[x/d for x in M[j]]
  for i in range(n):
   if i!=j:
    d=M[i][j];M[i]=[x-d*y for x,y in zip(M[i],M[j])]
 return [x[n:] for x in M]
A=[[F(1),F(1)],[F(1),F(1)]];C=[[F(1),F(0)],[F(0),F(0)]]
I=eye(2);Z=add(inverse(add(I,A)),scale(-1,inverse(add(I,C))))
v=[[F(-2)],[F(1)]];lam=F(1,3);mu=F(1,4)
assert mm(Z,v)==scale(lam,v)
assert F(1)*v[1][0]==-mu*2*v[0][0] # (2), unnormalized
assert (1+mu)/2*v[0][0]+(1+mu)*v[1][0]==0 # (3)
assert F(1,5)==mu*(F(4,5)-F(1,5))+mu**2*F(4,5) # (4)
assert F(3,5)==mu+mu*(2-mu)*F(4,5) # (6)
# Independent noncommuting active blocks for (14), exact inverse arithmetic.
B0=[[F(3),F(1)],[F(1),F(3)]];H=[[F(2),F(1)],[F(1),F(1)]];s=F(2,3)
U=add(scale(s,I),B0);V=add(scale(s,I),H)
assert mm(B0,H)!=mm(H,B0)
assert add(inverse(V),scale(-1,inverse(U)))==mm(mm(inverse(U),add(B0,scale(-1,H))),inverse(V))

rng=np.random.default_rng(10320260911)
def sym(A):return (A+A.T)/2
def nuc(A):return float(np.abs(np.linalg.eigvalsh(sym(A))).sum())
def pos(A):return float(np.maximum(np.linalg.eigvalsh(sym(A)),0).sum())
def fun(A,fn):
 a,U=np.linalg.eigh(sym(A));a=np.maximum(a,0);return (U*fn(a))@U.T
def ridge(A,s):return fun(A,lambda x:x/(s+x))
metrics={'cases':0,'noncommuting_B0_H':0,'selected_B_rank_deficient':0,'max_lemma_ratio':0.,'max_assembly_ratio':0.,'max_transfer_ratio':0.,'max_block_identity_scaled_residual':0.}
fail=[]
def bound(name,lhs,rhs,sc):
 if lhs>rhs+3e-9*max(sc,1e-12):fail.append((name,lhs,rhs,sc))
for j in range(1800):
 n=int(rng.integers(2,9));k=int(rng.integers(1,n));U=np.linalg.qr(rng.normal(size=(n,n)))[0]
 a=np.sort(10.**rng.uniform(-5,5,n))[::-1];A=(U*a)@U.T
 H=A[:k,:k];C=np.zeros((n,n));C[:k,:k]=H;E=A[:k,k:];G=A[k:,k:]
 c=10.**rng.uniform(-7,7);s=10.**rng.uniform(-7,7);Z=ridge(C,s)-ridge(A,s);DD=C-A
 lhs=pos(Z);rhs=2/(s+c)*(pos(DD)+pos(c*np.eye(k)-H));bound('lemma2',lhs,rhs,max(lhs,rhs,1.))
 if rhs:metrics['max_lemma_ratio']=max(metrics['max_lemma_ratio'],lhs/rhs)
 zz,VV=np.linalg.eigh(sym(Z))
 for t in np.where(zz>1e-7)[0]:
  la=zz[t];mu=la/(1+la);v=VV[:,t];u=v[:k];w=v[k:];M=s*np.eye(k)+H
  residuals=[np.linalg.norm(E@w+mu*M@u),np.linalg.norm(E.T@np.linalg.solve(M,(s*np.eye(k)+mu*H)@u)+(G+mu*s*np.eye(n-k))@w),abs(w@G@w-mu*s*(u@u-w@w)-mu**2*(u@H@u)),abs(v@DD@v-mu*s-mu*(2-mu)*(u@H@u))]
  rr=max(residuals)/(max(1.,np.linalg.norm(A),s));metrics['max_block_identity_scaled_residual']=max(metrics['max_block_identity_scaled_residual'],rr)
 V=np.linalg.qr(rng.normal(size=(k,k)))[0];BB0=(V*a[:k])@V.T
 B0=np.zeros_like(A);B0[:k,:k]=BB0;b=np.sort(10.**rng.uniform(-5,5,k))[::-1]
 if j%3==0:b[int(rng.integers(0,k)):]=0;metrics['selected_B_rank_deficient']+=1
 B=np.zeros_like(A);B[:k,:k]=(V*b)@V.T
 if np.linalg.norm(BB0@H-H@BB0)>1e-6:metrics['noncommuting_B0_H']+=1
 tau=a[k:].sum();cc=a[k-1];g=1/(s+cc);L=a[:k].sum()-np.trace(H);R=nuc(B0-C);e0=nuc(A-B0)-tau;eC=nuc(A-C)-tau;e=nuc(A-B)-tau;r=np.abs(a[:k]-b).sum()
 ts=(a[k:]/(s+a[k:])).sum();ex0=nuc(ridge(A,s)-ridge(B0,s))-ts;ex=nuc(ridge(A,s)-ridge(B,s))-ts
 for name,x,y in [('8',R+L,e0),('9',eC,e0+R),('15',ex0,5*g*e0),('16',r,e),('17',e0,e+r),('19',ex,11*g*e),('20',g*tau,ts)]:bound(name,x,y,max(nuc(A),nuc(B),abs(x),abs(y),1.))
 if g*e>1e-9:metrics['max_assembly_ratio']=max(metrics['max_assembly_ratio'],ex/(g*e))
 alpha=10.**rng.uniform(-2,2);beta=10.**rng.uniform(-2,2)
 ff=lambda x:alpha+beta*x+x/(s+x)+.3*np.sqrt(x)
 FA=fun(A,ff);FB=np.zeros_like(A);FB[:k,:k]=(V*ff(b))@V.T # retain selected zero eigendirections
 tf=ff(a[k:]).sum();exf=nuc(FA-FB)-tf;bound('positive f(0) transfer',exf,11*e/tau*tf,max(nuc(FA),nuc(FB),11*e/tau*tf,1.))
 if e/tau*tf>1e-8:metrics['max_transfer_ratio']=max(metrics['max_transfer_ratio'],exf/(e/tau*tf))
 metrics['cases']+=1

# A tiny independent Decimal Jacobi eigensolver avoids binary64 cancellation
# in the deliberately 10^-40-gap / 10^-70-compression tests below.
def deig(A):
 n=len(A);M=[r[:] for r in A];Q=eye(n,D);sc=max(D(1),max(abs(x) for r in A for x in r))
 for _ in range(300*n*n):
  p,q=max(((i,j) for i in range(n) for j in range(i+1,n)),key=lambda ij:abs(M[ij[0]][ij[1]]))
  if abs(M[p][q])<D('1e-115')*sc:break
  tau=(M[q][q]-M[p][p])/(2*M[p][q]);t=(D(1) if tau>=0 else D(-1))/(abs(tau)+(1+tau*tau).sqrt());c=1/(1+t*t).sqrt();s=t*c
  d=M[p][q];M[p][p]-=t*d;M[q][q]+=t*d;M[p][q]=M[q][p]=D(0)
  for i in range(n):
   if i not in (p,q):
    u,v=M[i][p],M[i][q];M[i][p]=M[p][i]=c*u-s*v;M[i][q]=M[q][i]=s*u+c*v
   u,v=Q[i][p],Q[i][q];Q[i][p]=c*u-s*v;Q[i][q]=s*u+c*v
 else:raise AssertionError('Jacobi did not converge')
 order=sorted(range(n),key=lambda i:M[i][i],reverse=True)
 return [M[i][i] for i in order],[[r[i] for i in order] for r in Q]
def dnuc(A):return sum(abs(x) for x in deig(A)[0])
def dpos(A):return sum(max(x,D(0)) for x in deig(A)[0])
def dtrace(A):return sum(A[i][i] for i in range(len(A)))
def dfunc(A,fn):
 a,U=deig(A);assert min(a)>-D('1e-100')
 return mm([[u*fn(max(x,D(0))) for u,x in zip(row,a)] for row in U],transpose(U))
def dgram(G):return mm(G,transpose(G))
def dcase(name,A,k,b,s,c,alpha=D(3),epszero=False):
 n=len(A);I=eye(n,D);P=[[D(int(i==j and i<k)) for j in range(n)] for i in range(n)];C=mm(mm(P,A),P);H=[row[:k] for row in A[:k]]
 rid=lambda x:x/(s+x);Z=add(dfunc(C,rid),scale(-1,dfunc(A,rid)));DD=add(C,scale(-1,A))
 # Pad the positive defect rather than ask a 1x1 eigensolver for H.
 defect=[[D(0) for _ in range(n)] for _ in range(n)]
 for i in range(k):
  for j in range(k):defect[i][j]=c*D(i==j)-H[i][j]
 rhs=2/(s+c)*(dpos(DD)+dpos(defect));lhs=dpos(Z)
 assert lhs<=rhs+D('1e-90')*max(D(1),rhs),(name,'lemma')
 a,_=deig(A);tau=sum(a[k:]);B=[[b[i]*D(i==j) if i<k else D(0) for j in range(n)] for i in range(n)]
 e=dnuc(add(A,scale(-1,B)))-tau;fa=dfunc(A,lambda x:alpha+rid(x));fb=[[D(0) for _ in range(n)] for _ in range(n)]
 for i in range(k):fb[i][i]=alpha+rid(b[i])
 tail=sum(alpha+rid(max(x,D(0))) for x in a[k:]);err=dnuc(add(fa,scale(-1,fb)))
 out={'case':name,'lemma_lhs':str(lhs),'lemma_rhs':str(rhs),'tail':str(tau),'excess':str(e),'functional_error':str(err),'functional_tail':str(tail)}
 if tau>D('1e-100'):
  atom_tail=sum(rid(x) for x in a[k:]);atom_ex=dnuc(add(dfunc(A,rid),scale(-1,dfunc(B,rid))))-atom_tail;g=1/(s+a[k-1])
  assert atom_ex<=11*g*e+D('1e-90')*max(D(1),abs(11*g*e)),(name,'assembly')
  assert err<=tail+11*max(e,D(0))/tau*tail+D('1e-80')*max(D(1),err),(name,'transfer')
  out['atom_excess_over_g_e']=str(atom_ex/(g*e)) if abs(e)>D('1e-100') else 'zero excess'
 if epszero:
  assert abs(e)<D('1e-90');assert abs(err-tail)<D('1e-90'),name
 high.append(out)
high=[]
with localcontext() as ctx:
 ctx.prec=145
 z=D(0);o=D(1);gap=D('1e-40');rot=[[o,z,z,z],[z,D(3)/5,D(4)/5,z],[z,-D(4)/5,D(3)/5,z],[z,z,z,o]]
 diag=[[x*D(i==j) for j in range(4)] for i,x in enumerate([D(2),1+gap,o,D(1)/4])];A=mm(mm(rot,diag),transpose(rot))
 dcase('gap_1e-40',A,2,[D(2),1+gap],D('1e-25'),o)
 h=D('1e-35');A=dgram([[h,z,z],[z,o,z],[o,o,o]])
 dcase('H_min_1e-70',A,2,[D(3),o],D('1e-75'),o)
 dcase('rank_deficient_selected_B',A,2,[D(3),z],D('1e-35'),o)
 A=dgram([[z,z,z],[z,o,z],[o,o,o]])
 dcase('singular_H',A,2,[D(3),z],D('1e-30'),o)
 A=[[x*D(i==j) for j in range(4)] for i,x in enumerate([D(2),o,o,D(0)])]
 dcase('epsilon_zero_positive_tail',A,2,[D(2),o],D('1e-30'),o,epszero=True)
 A=[[x*D(i==j) for j in range(3)] for i,x in enumerate([o,z,z])]
 dcase('zero_tail_rank_deficient_selected_B_f0_positive',A,2,[o,z],D('1e-20'),o,epszero=True)
 A=[[z for j in range(4)] for i in range(4)]
 dcase('A_B_zero_f0_positive',A,2,[z,z],o,o,epszero=True)
print(json.dumps({'exact_rational_identities':'PASS','binary64':metrics,'violations':fail,'decimal_precision':145,'high_precision_cases':high},indent=2))
assert not fail
