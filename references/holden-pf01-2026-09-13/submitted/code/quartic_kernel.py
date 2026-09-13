"""Exact integer jet-constraint and basis construction for n=9,r=4.

Use verify_round2.py for the full rank certificates and tests.
"""
from itertools import combinations,combinations_with_replacement
import numpy as np,json,time
from pathlib import Path

def rank_mod(A,p=1000003,certificate=False):
 A=np.array(A,dtype=np.int64,copy=True)%p;m,n=A.shape
 origin=np.arange(m); pivrows=[];pivcols=[];r=0
 for j in range(n):
  wh=np.flatnonzero(A[r:,j])
  if len(wh)==0:continue
  i=r+int(wh[0]);A[[r,i]]=A[[i,r]];origin[[r,i]]=origin[[i,r]]
  pivrows.append(int(origin[r]));pivcols.append(j)
  inv=pow(int(A[r,j]),-1,p);A[r,j:]=A[r,j:]*inv%p
  for a in range(r+1,m,64):
   z=min(a+64,m);A[a:z,j:] = (A[a:z,j:]-A[a:z,j,None]*A[None,r,j:])%p
  r+=1
  if r==m:break
 return (r,pivrows,pivcols) if certificate else r

def build(n=9,r=4,d=4):
 mons=list(combinations_with_replacement(range(n),d));N=len(mons)
 E=np.zeros((N,n),np.int64)
 for a,mon in enumerate(mons):
  for j in mon:E[a,j]+=1
 supports=E>0
 cons=[];rows=[]
 for I in combinations(range(n),r):
  I=set(I);out=[j for j in range(n) if j not in I]
  deriv=[]
  for j in range(n):
   e=E.copy();e[:,j]-=1
   ok=(E[:,j]>0)&np.all((e[:,out]<=0),axis=1)
   v=E[:,j]*ok
   deriv.append(v)
  for j in sorted(I):cons.append(deriv[j]);rows.append([sorted(I),'zero',j])
  for j in out[1:]:cons.append(deriv[j]-deriv[out[0]]);rows.append([sorted(I),'equal',j,out[0]])
 return np.array(cons),mons,rows

def family(n,r,mons):
 # z_i = r x_i^2 - sigma*x_i; q = sum_i z_i.
 idx={m:j for j,m in enumerate(mons)}
 def add(a,b):
  out={}
  for x,u in a.items():
   for y,v in b.items():
    z=tuple(sorted(x+y));out[z]=out.get(z,0)+u*v
  return out
 z=[]
 for i in range(n):
  pol={(i,i):r}
  for j in range(n):
   key=tuple(sorted((i,j)));pol[key]=pol.get(key,0)-1
  z.append(pol)
 q={}
 for pol in z:
  for a,c in pol.items():q[a]=q.get(a,0)+c
 fs=[]
 for i,j in combinations(range(n),2):fs.append(add(q,{(i,j):1}))
 for i,j in combinations_with_replacement(range(n),2):fs.append(add(z[i],z[j]))
 # h = 2*r^2*sum x_i^3 - 3*r*sigma*sum x_i^2 + sigma^3.
 sigma={(i,):1 for i in range(n)}
 cubes={(i,i,i):2*r*r for i in range(n)}
 hs=add(sigma,{(i,i):1 for i in range(n)})
 for a,c in hs.items():cubes[a]=cubes.get(a,0)-3*r*c
 hc=add(add(sigma,sigma),sigma)
 for a,c in hc.items():cubes[a]=cubes.get(a,0)+c
 for i in range(n):fs.append(add(cubes,{(i,):1}))
 F=np.zeros((len(mons),len(fs)),np.int64)
 for b,f in enumerate(fs):
  for a,c in f.items():F[idx[a],b]=c
 return F
if __name__=='__main__':
 A,mons,rows=build(9,4);F=family(9,4,mons)
 assert np.all(A@F==0)
 print('Constraint shape:', A.shape, 'basis shape:', F.shape)
 print('Prime-field ranks:', rank_mod(A), rank_mod(F))
 print('Run verify_round2.py to regenerate complete exact certificates.')
