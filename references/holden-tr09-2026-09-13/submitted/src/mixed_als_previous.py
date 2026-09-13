#!/usr/bin/env python3
"""Numerical mixed-block ALS, with explicitly local diagnostic starts.

NumPy is required. Floating-point output is not a certified error bound.
The exact theorem concerns local convergence, not global initialization.
"""
from __future__ import annotations
import itertools
import json
from pathlib import Path
import numpy as np


def represented(factors):
    a,b,c=factors
    return np.einsum('ai,bi,ci->abc',a,b,c,optimize=True)


def cycle_schedule(r):
    if not isinstance(r,int) or r < 1:
        raise ValueError('r must be a positive integer')
    if r == 1:
        return [[0],[1],[2]]
    out=[[0]*r]
    for bit in range((r-1).bit_length()):
        v=[1 if ((i>>bit)&1)==0 else 2 for i in range(r)]
        out.extend([v,[3-x for x in v]])
    return out


def mixed_update(target,factors,assignment,rcond=1e-14):
    """Return the exact-LS formula evaluated numerically, or raise on rank loss.

    At most one factor vector is selected from each summand. Internal design
    column scaling is an invertible change of unknowns in the same problem.
    """
    t=np.asarray(target,dtype=float)
    f=[np.array(x,dtype=float,copy=True) for x in factors]
    if t.ndim != 3 or len(set(t.shape)) != 1:
        raise ValueError('Expected a cubic order-three tensor')
    n=t.shape[0]
    if len(f)!=3 or any(x.ndim!=2 or x.shape[0]!=n for x in f):
        raise ValueError('Expected three factor matrices with n rows')
    r=f[0].shape[1]
    if any(x.shape != (n,r) for x in f) or len(assignment)!=r:
        raise ValueError('Factor shapes and assignment disagree')
    if any(x is not None and x not in (0,1,2) for x in assignment):
        raise ValueError('Assignments must be 0, 1, 2, or None')
    if not np.all(np.isfinite(t)) or any(not np.all(np.isfinite(x)) for x in f):
        raise ValueError('Nonfinite input')
    columns=[]; where=[]; fixed=np.zeros_like(t)
    eye=np.eye(n)
    for i,m in enumerate(assignment):
        if m is None:
            fixed += np.einsum('a,b,c->abc',f[0][:,i],f[1][:,i],f[2][:,i])
        else:
            for j in range(n):
                vectors=[f[q][:,i] for q in range(3)]
                vectors[m]=eye[:,j]
                columns.append(np.einsum('a,b,c->abc',*vectors).ravel())
                where.append((m,i,j))
    if not columns:
        return f
    d=np.column_stack(columns)
    norms=np.linalg.norm(d,axis=0)
    if np.any(norms==0) or not np.all(np.isfinite(norms)):
        raise np.linalg.LinAlgError('Zero or nonfinite design column')
    ds=d/norms
    answer,_,rank,singular=np.linalg.lstsq(ds,(t-fixed).ravel(),rcond=rcond)
    if rank != len(columns):
        raise np.linalg.LinAlgError('Numerical rank loss; no truncated-rank continuation')
    answer=answer/norms
    for value,(m,i,j) in zip(answer,where):
        f[m][j,i]=value
    return f


def solve(target,initial,max_cycles=20,tolerance=1e-12,method='mixed'):
    if max_cycles < 0 or not 0 < tolerance < 1:
        raise ValueError('Invalid budget or tolerance')
    f=[np.array(x,dtype=float,copy=True) for x in initial]
    r=f[0].shape[1]
    schedule=cycle_schedule(r) if method=='mixed' else [[0]*r,[1]*r,[2]*r]
    denom=np.linalg.norm(target)
    if denom==0:
        raise ValueError('Diagnostic requires a nonzero target')
    history=[float(np.linalg.norm(represented(f)-target)/denom)]
    status='budget_exhausted'; blocks=0
    try:
        for _ in range(max_cycles):
            if history[-1]<=tolerance:
                status='tolerance_reached'; break
            for assignment in schedule:
                f=mixed_update(target,f,assignment)
                blocks+=1
            history.append(float(np.linalg.norm(represented(f)-target)/denom))
        if history[-1]<=tolerance:
            status='tolerance_reached'
    except np.linalg.LinAlgError as exc:
        status='numerical_rank_failure: '+str(exc)
    return {'status':status,'block_updates':blocks,'relative_residual_history':history}


def main():
    records=[]
    for sine in (0.6,0.1,0.01):
        cosine=float(np.sqrt(1-sine*sine))
        coherent=np.array([[1,cosine],[0,sine]],dtype=float)
        for family in ('one_coherent_mode','three_coherent_modes'):
            true=[coherent,np.eye(2),np.eye(2)] if family=='one_coherent_mode' else [coherent.copy() for _ in range(3)]
            target=represented(true)
            for seed in (0,1):
                rng=np.random.default_rng(seed)
                initial=[x+1e-5*rng.standard_normal(x.shape) for x in true]
                for method in ('ordinary','mixed'):
                    record={'family':family,'sine':sine,'seed':seed,'method':method,
                            'initialization':'true-factor-dependent local diagnostic; not a global admissible initializer'}
                    record.update(solve(target,initial,method=method))
                    records.append(record)
    path=Path(__file__).with_name('local_diagnostics.json')
    path.write_text(json.dumps({'scope':'Uncertified floating-point local diagnostics; all scheduled cases retained.','records':records},indent=2)+'\n')
    print('Wrote',len(records),'local diagnostic records to',path)

if __name__=='__main__':
    main()
