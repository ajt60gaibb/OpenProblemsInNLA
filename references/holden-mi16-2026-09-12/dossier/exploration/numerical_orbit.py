"""Exploratory Riemannian ascent, never a global certificate."""
import numpy as np
from scipy.linalg import expm
import itertools, json, time
from pathlib import Path

_cache={}
def per_gradient(A):
    n=len(A)
    if n not in _cache:
        masks=np.array([[bool(k & (1<<j)) for j in range(n)] for k in range(1,1<<n)],float).T
        signs=(-1.)**(n+masks.sum(axis=0))
        _cache[n]=(masks,signs)
    masks,signs=_cache[n]
    sums=A@masks
    value=np.dot(signs,np.prod(sums,axis=0)).real
    q=np.empty_like(A)
    for i in range(n):
        products=np.prod(np.delete(sums,i,axis=0),axis=0)
        q[i,:]=(products*signs)@masks.T
    return value,q.T

def ascend(lam,rng,real=False,maxiter=2000):
    n=len(lam)
    z=rng.normal(size=(n,n))
    if not real:z=z+1j*rng.normal(size=(n,n))
    U=np.linalg.qr(z)[0]
    A=(U*np.array(lam))@U.conj().T
    f,C=per_gradient(A)
    step=1.
    for it in range(maxiter):
        G=C@A-A@C
        G=(G-G.conj().T)/2
        gn=np.linalg.norm(G)
        if gn<1e-10:break
        step=min(step*1.6,1000.)
        success=False
        for k in range(35):
            Q=expm(step*G)
            B=Q@A@Q.conj().T
            fb,Cb=per_gradient(B)
            if fb>=f+1e-4*step*gn**2:
                success=True;break
            step*=.5
        if not success:break
        if abs(fb-f)<1e-14 and gn<1e-7:
            A,f,C=B,fb,Cb;break
        A,f,C=B,fb,Cb
    return f,A,float(gn),it

def main():
    specs=[[0,1,2,3],[0,1,1,2],[0,.1,1,1],[0,0,1,1],[0,0,1,2],[1,2,3,5],[0,.5,1,4], [0,0,0,1,1],[0,0,1,1,1]]
    out=[];rng=np.random.default_rng(160926)
    for spec in specs:
        lam=np.array(spec)/max(spec)
        for real in [True,False]:
            records=[]
            for trial in range(20):
                f,A,g,it=ascend(lam,rng,real)
                records.append((f,A,g,it))
            f,A,g,it=max(records,key=lambda x:x[0])
            result={'lambda':spec,'field':'real' if real else 'complex','permanent':float(f*max(spec)**len(spec)), 'matrix_real':(A*max(spec)).real.tolist(),'matrix_imag':(A*max(spec)).imag.tolist(),'grad_norm_normalized':g,'starts':len(records),'distinct_values':sorted(set(round(r[0]*max(spec)**len(spec),8) for r in records))}
            out.append(result)
            Path('/mnt/data/mi16_work/numerical_results.json').write_text(json.dumps(out,indent=2))
            print(spec,result['field'],result['permanent'],np.round(np.diag(A).real*max(spec),5),g,flush=True)
if __name__=='__main__':main()
