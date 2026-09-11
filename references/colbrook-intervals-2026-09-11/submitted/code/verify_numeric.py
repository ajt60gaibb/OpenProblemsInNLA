"""Floating-point diagnostic screening; these tests do not certify the proofs.
Run --section av01, iv03, or iv05. Use --full for the larger fixed-seed suites.
"""
from __future__ import annotations
import argparse, datetime, itertools, json, time, traceback
from pathlib import Path
import numpy as np
from nla_algorithms import (signs,av01_recognize_float,inverse_m_float,
    inverse_m_vertices_float,inverse_m_hull_float,inverse_m_ave_float)

ROOT=Path(__file__).resolve().parents[1]


def av01(full):
    rng=np.random.default_rng(9102026)
    counts=[(1,300),(2,2000),(3,3000),(4,2000),(5,1000),(6,500),(7,300),(8,100)]
    if not full: counts=[(n,min(t,30)) for n,t in counts]
    tested=0;yes={}
    for n,trials in counts:
        yes[n]=0
        for _ in range(trials):
            scale=rng.choice([1,2,4,8,16,32])
            A=rng.integers(-8,9,size=(n,n))/scale
            b=rng.integers(1,10,size=n).astype(float)
            truth=True
            for ss in signs(n):
                s=np.asarray(ss)
                M=A+np.diag(s)
                if abs(np.linalg.det(M))<1e-8:
                    truth=False;break
                x=np.linalg.solve(M,b)
                if np.min(s*x)<=1e-8:
                    truth=False;break
            got=av01_recognize_float(A,b)
            assert got==truth,{'n':n,'A':A.tolist(),'b':b.tolist(),'LP':got,'orthants':truth}
            yes[n]+=int(got);tested+=1
        print('AV-01',n,trials,yes[n],flush=True)
    return {'instances':tested,'accepted_by_dimension':yes,'mismatches':0}


def random_box(rng,n,noise):
    W=rng.uniform(.05,1,(n,n));np.fill_diagonal(W,0)
    M=np.diag(W.sum(axis=1)+rng.uniform(noise[0],noise[1],n))-W
    C=np.linalg.inv(M);R=np.zeros_like(C)
    idx=rng.choice(n*n,size=min(n*n,10),replace=False)
    R.flat[idx]=rng.uniform(.2,1.5,len(idx))*C.flat[idx]
    high=.999*min(C.flat[j]/R.flat[j] for j in idx)
    low=0.
    for _ in range(18):
        mid=(low+high)/2
        if inverse_m_vertices_float(C,mid*R):low=mid
        else:high=mid
    return C,R,idx,low


def matrices(C,R,idx):
    for ss in signs(len(idx)):
        A=C.copy();A.flat[idx]+=np.asarray(ss)*R.flat[idx]
        yield A


def iv03(full):
    rng=np.random.default_rng(8030911)
    counts=[(2,200),(3,300),(4,200),(5,150),(6,100),(7,50)]
    if not full:counts=[(n,5) for n,t in counts]
    total=0;yes={};vertices=0
    for n,trials in counts:
        yes[n]=0
        for _ in range(trials):
            C,R,idx,t=random_box(rng,n,(.2,2))
            R*=t*rng.choice([.95,.999,1.001,1.05])
            got=inverse_m_vertices_float(C,R)
            truth=True
            for A in matrices(C,R,idx):
                vertices+=1
                if not inverse_m_float(A):truth=False;break
            assert got==truth,{'n':n,'center':C.tolist(),'radius':R.tolist()}
            total+=1;yes[n]+=int(got)
        print('IV-03',n,trials,yes[n],flush=True)
    return {'boxes':total,'vertices_checked':vertices,'accepted_by_dimension':yes,'mismatches':0}


def iv05(full):
    rng=np.random.default_rng(8050911)
    counts=[(1,50),(2,100),(3,150),(4,100),(5,75),(6,50)]
    if not full:counts=[(n,5) for n,t in counts]
    total=0;vertices=0;max_error=0.;lp_count=0
    for n,trials in counts:
        for _ in range(trials):
            C,R,idx,t=random_box(rng,n,(.5,2))
            R*=.7*t
            bc=rng.uniform(-10,10,n);br=rng.uniform(0,5,n)
            lower=np.full(n,np.inf);upper=np.full(n,-np.inf)
            for A in matrices(C,R,idx):
                assert inverse_m_float(A)
                B=np.linalg.inv(A);vertices+=1
                for i in range(n):
                    sigma=-np.ones(n);sigma[i]=1
                    upper[i]=max(upper[i],B[i]@(bc+sigma*br))
                    lower[i]=min(lower[i],B[i]@(bc-sigma*br))
            lo,hi=inverse_m_hull_float(C,R,bc,br)
            error=max(np.max(abs(lo-lower)/(1+abs(lower))),
                      np.max(abs(hi-upper)/(1+abs(upper))))
            max_error=max(max_error,float(error))
            assert error<1e-7,{'n':n,'scaled_error':float(error)}
            total+=1;lp_count+=2*n
        print('IV-05',n,trials,max_error,flush=True)
    return {'boxes':total,'vertices_checked':vertices,'LPs':lp_count,
            'maximum_scaled_endpoint_error':max_error,'mismatches':0}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--section',choices=['av01','iv03','iv05'],required=True)
    parser.add_argument('--full',action='store_true');args=parser.parse_args()
    out=ROOT/'verification'/f'{args.section}_numeric_results.json'
    result={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'arithmetic':'floating point; diagnostic only','section':args.section,
            'mode':'full' if args.full else 'smoke'}
    start=time.monotonic()
    try:
        result.update(globals()[args.section](args.full));result['status']='passed'
    except Exception:
        result['status']='failed';result['traceback']=traceback.format_exc();raise
    finally:
        result['elapsed_seconds']=time.monotonic()-start
        result['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
        out.write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))

if __name__=='__main__':main()
