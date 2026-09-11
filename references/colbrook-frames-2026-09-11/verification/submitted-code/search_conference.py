#!/usr/bin/env python3
"""Exploratory two-circulant Hermitian-conference search. Not a certificate."""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
os.environ.setdefault('OMP_NUM_THREADS','1')
import numpy as np
from scipy.optimize import minimize,least_squares
import argparse,json,time
from pathlib import Path


def model(d, x, jac=False):
    h=(d-1)//2
    a=np.zeros(d,dtype=complex)
    a[1:h+1]=np.exp(1j*x[:h]);a[-h:]=a[1:h+1][::-1].conj()
    if d%2==0:a[d//2]=1
    b=np.exp(1j*np.r_[0.,x[h:]])
    alpha=np.fft.fft(a).real;beta=np.fft.fft(b)
    f=(alpha*alpha+abs(beta)**2-(2*d-1))/d
    if not jac:return f,a,b
    n=len(x)
    da=np.zeros((d,h),dtype=complex)
    for j in range(h):da[j+1,j]=1j*a[j+1];da[-j-1,j]=-1j*a[-j-1]
    db=np.zeros((d,d-1),dtype=complex)
    db[1:,]=np.diag(1j*b[1:])
    ja=2*alpha[:,None]*np.fft.fft(da,axis=0).real/d
    jb=2*np.real(beta.conj()[:,None]*np.fft.fft(db,axis=0))/d
    return f,np.c_[ja,jb],a,b


def run(d,seed,starts,steps,out):
    rng=np.random.default_rng(seed);h=(d-1)//2
    best=None
    for k in range(starts):
        x=rng.uniform(-np.pi,np.pi,h+d-1)
        def fun(x):
            f,J,*_=model(d,x,True)
            return f@f,2*J.T@f
        t=time.time()
        res=minimize(fun,x,jac=True,method='L-BFGS-B',options={'maxiter':steps,'ftol':1e-15,'gtol':1e-10,'maxls':40})
        f,J,a,b=model(d,res.x,True)
        score=float(np.max(np.abs(f)))
        record={'d':d,'seed':seed,'start':k,'max_scaled_residual':score,'objective':float(f@f),'iterations':res.nit,'seconds':time.time()-t}
        with open(out.with_suffix('.jsonl'),'a') as g:g.write(json.dumps(record)+'\n')
        print(json.dumps(record),flush=True)
        if best is None or score<best['max_scaled_residual']:
            best={**record,'angles':res.x.tolist(),'a_real':a.real.tolist(),'a_imag':a.imag.tolist(),'b_real':b.real.tolist(),'b_imag':b.imag.tolist(),'status':'numerical candidate only; not certified'}
            out.write_text(json.dumps(best,indent=2)+'\n')
        if score<1e-9:break

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--d',type=int,required=True);p.add_argument('--seed',type=int,default=0);p.add_argument('--starts',type=int,default=4);p.add_argument('--steps',type=int,default=1000);p.add_argument('--out',type=Path)
    a=p.parse_args();run(a.d,a.seed,a.starts,a.steps,a.out or Path(__file__).with_name(f'conference_d{a.d}_seed{a.seed}.json'))
