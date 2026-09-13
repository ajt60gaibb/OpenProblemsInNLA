#!/usr/bin/env python3
"""Numerical sanity checks only; mathematical reductions are proved in result.md."""
from pathlib import Path
import numpy as np,json


def root(A):
 w,V=np.linalg.eigh((A+A.conj().T)/2)
 return (V*np.sqrt(np.maximum(w,0)))@V.conj().T

def norm(A,p):return float(np.sum(np.linalg.svd(A,compute_uv=False)**p)**(1/p))

def main():
 maxerr=0.;count=0
 for path in sorted((Path(__file__).parent/'experiments').glob('*.json')):
  d=json.loads(path.read_text());L=np.array(d['L']);r=np.array(d['r']);p=d['p'];q=p/(p-1)
  X=L@L.transpose(0,2,1);R=np.diag(r);S=X.sum(0)
  dual=sum(norm(R@x,1) for x in X)/(norm(R,q)*norm(S,p))
  err=abs(dual-d['ratio']);assert err<1e-11
  maxerr=max(maxerr,err);count+=1
  # Recover feasible primal matrices with at least the displayed dual quotient.
  A=[]
  for x in X:
   left,s,right=np.linalg.svd(x@R,full_matrices=True)
   U=right.conj().T@left.conj().T
   A.append(U@x)
  primal=norm(sum(A),p)/norm(S,p)
  assert primal+1e-10>=dual
 rng=np.random.default_rng(200912);dilation_tests=0
 for n in (2,3,4):
  for m in (2,3):
   for singular in (False,True):
    L=rng.normal(size=(m,n,n))
    if singular:L[:,-1,:]=0
    X=L@L.transpose(0,2,1);S=X.sum(0)
    w,V=np.linalg.eigh(S);positive=w>1e-10
    si=(V[:,positive]/np.sqrt(w[positive]))@V[:,positive].T
    E=V[:,positive]@V[:,positive].T
    K=[si@x@si for x in X];K[0]+=np.eye(n)-E
    W=np.vstack([root(k) for k in K])
    assert np.linalg.norm(W.T@W-np.eye(n))<1e-9
    Lr=rng.normal(size=(n,n));R=Lr@Lr.T
    St=W@S@W.T;Rt=W@R@W.T;Sh=root(St)
    for j in range(m):
     P=np.zeros_like(St);P[j*n:(j+1)*n,j*n:(j+1)*n]=np.eye(n)
     Xt=Sh@P@Sh
     assert np.linalg.norm(Xt-W@X[j]@W.T)<1e-7
     assert abs(norm(Rt@Xt,1)-norm(R@X[j],1))<1e-6
    dilation_tests+=1
 print(json.dumps({'result':'PASS','type':'NUMERICAL SANITY CHECK ONLY',
                   'archived_search_records_checked':count,'maximum_saved_ratio_discrepancy':maxerr,
                   'dilation_cases_including_singular_S':dilation_tests},indent=2))

if __name__=='__main__':main()
