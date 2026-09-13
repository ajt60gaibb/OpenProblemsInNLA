#!/usr/bin/env python3
"""Uncertified local and global diagnostics. All predetermined cases retained.

Local starts use hidden true factors and cannot establish the TR-09 initializer
requirement. Global starts are input-independent except for scalar target
normalization; their finite runs do not prove either success or impossibility.
"""
from __future__ import annotations
import json
from pathlib import Path
import time
import numpy as np
from mixed_als_previous import represented, solve, cycle_schedule


def derivative_design(fs, assignment, chart=False):
    n,r=fs[0].shape; eye=np.eye(n); columns=[]
    if chart:
        triples=[(m,i,j) for m in range(3) for i in range(r) for j in range(n)
                 if not(m>0 and j==i)]
    else:
        triples=[(m,i,j) for i,m in enumerate(assignment) for j in range(n)]
    for m,i,j in triples:
        v=[f[:,i] for f in fs]; v[m]=eye[:,j]
        columns.append(np.einsum('a,b,c->abc',*v).ravel())
    return np.column_stack(columns)


def local_derivative_record(fs):
    n,r=fs[0].shape
    jac=derivative_design(fs,None,chart=True)
    u,sv,_=np.linalg.svd(jac,full_matrices=False)
    tangent_rank=int(np.sum(sv>1e-13*sv[0]))
    e=u[:,:tangent_rank]
    for assignment in cycle_schedule(r):
        d=derivative_design(fs,assignment)
        # Full-rank QR is only used for these deliberately nonsingular cases.
        q,_=np.linalg.qr(d,mode='reduced')
        e-=q@(q.T@e)
    bc=[]
    for f in fs[1:]:
        b=f/np.linalg.norm(f,axis=0)
        bc.append(float(np.linalg.norm(b.T@b-np.eye(r),2)))
    tau=max(bc); delta=2*tau+tau*tau; cycles=len(cycle_schedule(r))
    bound=cycles*delta*np.sqrt((1+delta)/(1-delta))/(1-delta) if delta<1 else None
    return {'derivative_norm_observed':float(np.linalg.norm(e,2)),
            'theorem_bound':bound,'normalized_gram_deviation':tau,
            'tangent_rank':tangent_rank,'expected_chart_dimension':3*n*r-2*r,
            'smallest_chart_singular_value':float(sv[-1])}


def main():
    started=time.monotonic(); local=[]; global_records=[]
    for sep in (1e-1,1e-3,1e-6):
        for perturbation in (0.,1e-4):
            for seed in range(3):
                n,r=5,3; rng=np.random.default_rng(100+seed)
                a=np.ones((n,1))@np.ones((1,r))+sep*rng.normal(size=(n,r))
                b=np.eye(n)[:,:r]+perturbation*rng.normal(size=(n,r))
                c=np.eye(n)[:,:r]+perturbation*rng.normal(size=(n,r))
                true=[a,b,c]; target=represented(true)
                initial=[x+1e-7*rng.normal(size=x.shape) for x in true]
                derivative=local_derivative_record(true)
                for method in ('mixed','ordinary'):
                    rec={'kind':'local','first_mode_separation_parameter':sep,
                         'other_mode_perturbation':perturbation,'seed':seed,'method':method,
                         'initialization':'true-factor-dependent local perturbation; inadmissible as global initializer',
                         **derivative}
                    rec.update(solve(target,initial,max_cycles=30,tolerance=1e-11,method=method))
                    local.append(rec)
    for n,r in ((5,3),(7,4)):
        rho=r**-1
        for family in ('two_orthogonal_bases','three_coherent_bases'):
            for scale in (1.,30.,1000.):
                for smoothing_seed in (0,1):
                    base_rng=np.random.default_rng(550+n*10+r)
                    directions=[base_rng.normal(size=n) for _ in range(3)]
                    directions=[u/np.linalg.norm(u) for u in directions]
                    bases=[scale*u[:,None]*np.ones((1,r)) for u in directions]
                    if family=='two_orthogonal_bases':
                        for m in (1,2):
                            q,_=np.linalg.qr(base_rng.normal(size=(n,r)))
                            bases[m]=scale*q
                    noise=np.random.default_rng(10000+100*n+10*r+smoothing_seed)
                    true=[b+rho/np.sqrt(n)*noise.normal(size=(n,r)) for b in bases]
                    target=represented(true)
                    scale_t=np.linalg.norm(target); target=target/scale_t
                    for initialization_seed in range(5):
                        rng=np.random.default_rng(20000+initialization_seed)
                        initial=[np.zeros((n,r)),rng.normal(size=(n,r)),rng.normal(size=(n,r))]
                        for method in ('mixed','ordinary'):
                            rec={'kind':'global','n':n,'r':r,'width':r,'family':family,
                                 'base_scale':scale,'rho':rho,'smoothing_seed':smoothing_seed,
                                 'initialization_seed':initialization_seed,'method':method,
                                 'tensor_normalization':float(scale_t),
                                 'initialization':'X=0, independent Gaussian Y,Z; only scalar target normalization',
                                 'max_cycles':60,'tolerance':1e-10}
                            rec.update(solve(target,initial,max_cycles=60,tolerance=1e-10,method=method))
                            global_records.append(rec)
    summary={}
    for kind,records in (('local',local),('global',global_records)):
        for rec in records:
            key=kind+' / '+rec.get('family','near_two_orthogonal_modes')+' / '+rec['method']
            counts=summary.setdefault(key,{'runs':0,'tolerance_reached':0,'numerical_rank_failure':0,'budget_exhausted':0})
            counts['runs']+=1
            if rec['status']=='tolerance_reached': counts['tolerance_reached']+=1
            elif rec['status'].startswith('numerical_rank_failure'): counts['numerical_rank_failure']+=1
            else: counts['budget_exhausted']+=1
    out={'scope':'Uncertified floating-point diagnostics; no equal-work comparison or convergence proof.',
         'elapsed_seconds':time.monotonic()-started,'summary':summary,
         'local_records':local,'global_records':global_records}
    path=Path(__file__).resolve().parents[1]/'results'/'diagnostics.json'
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
    print('Saved all',len(local)+len(global_records),'runs to',path)

if __name__=='__main__': main()
