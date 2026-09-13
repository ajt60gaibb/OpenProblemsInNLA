"""Exploratory local PSD-factor search. Failure is NOT a lower-bound certificate.

Example: python code/search_factors.py 7 4 --root-rank 4 --seeds 30
The stored historical logs used the same objective and solver settings.
"""
from __future__ import annotations
import argparse
from itertools import combinations
from pathlib import Path
import json
import time
import numpy as np
from scipy.optimize import minimize

def objective(x: np.ndarray, nrows: int, k: int, root_rank: int,
              target: np.ndarray) -> tuple[float,np.ndarray]:
    u,v=x.reshape(2,nrows,k,root_rank)
    a=u@u.transpose(0,2,1);b=v@v.transpose(0,2,1)
    residual=a.reshape(nrows,-1)@b.reshape(nrows,-1).T-target
    denom=float(np.sum(target*target))
    du=4*(residual@b.reshape(nrows,-1)).reshape(nrows,k,k)@u/denom
    dv=4*(residual.T@a.reshape(nrows,-1)).reshape(nrows,k,k)@v/denom
    return float(np.sum(residual*residual)/denom),np.stack([du,dv]).ravel()

def solve(n: int, k: int, root_rank: int, seed: int,
          maxiter: int, output: Path) -> dict:
    if n<3 or n>12 or not 1<=root_rank<=k:
        raise ValueError('Require 3<=n<=12 and 1<=root_rank<=k')
    subsets=np.array(list(combinations(range(n),n//2)))
    e=np.zeros((len(subsets),n));e[np.arange(len(e))[:,None],subsets]=1
    d=n//2-e@e.T
    rng=np.random.default_rng(seed)
    initial=rng.normal(size=(2,len(e),k,root_rank))/(k*root_rank)**.25
    start=time.monotonic()
    result=minimize(objective,initial.ravel(),args=(len(e),k,root_rank,d),jac=True,
                    method='L-BFGS-B',options={'maxiter':maxiter,'ftol':1.e-16,
                    'gtol':1.e-12,'maxcor':30,'maxls':40})
    output.mkdir(parents=True,exist_ok=True)
    np.savez_compressed(output/f'fit_n{n}_k{k}_q{root_rank}_s{seed}.npz',
                        uv=result.x.reshape(2,len(e),k,root_rank),D=d,subsets=subsets)
    record={'n':n,'k':k,'q':root_rank,'seed':seed,'loss':float(result.fun),
            'nit':int(result.nit),'seconds':time.monotonic()-start,
            'solver_message':str(result.message),
            'interpretation':'Numerical search output, not an exact factorization or a lower bound.'}
    print(json.dumps(record),flush=True)
    return record

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n',type=int);parser.add_argument('k',type=int)
    parser.add_argument('--root-rank',type=int,default=None)
    parser.add_argument('--seeds',type=int,default=3)
    parser.add_argument('--maxiter',type=int,default=3000)
    parser.add_argument('--output',type=Path,default=Path('search_output'))
    args=parser.parse_args()
    if args.seeds<1 or args.maxiter<1: parser.error('seeds and maxiter must be positive')
    q=args.k if args.root_rank is None else args.root_rank
    records=[solve(args.n,args.k,q,seed,args.maxiter,args.output) for seed in range(args.seeds)]
    (args.output/'search_log.json').write_text(json.dumps(records,indent=2)+'\n')

if __name__=='__main__':main()
