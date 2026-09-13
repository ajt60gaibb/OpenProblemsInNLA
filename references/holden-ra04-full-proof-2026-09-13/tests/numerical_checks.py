#!/usr/bin/env python3
"""Reproducible diagnostics for RA-04. Numerical tests are not proof certificates."""
from __future__ import annotations
import argparse
import csv
import json
import math
import platform
from pathlib import Path
import numpy as np
import mpmath as mp


def krylov(nodes: np.ndarray, h: np.ndarray, t: int) -> np.ndarray:
    return np.concatenate([nodes[:,None]**j*h for j in range(t)],axis=1)


def gap(nodes: np.ndarray,b: int) -> float:
    return 1.0 if len(nodes)==b else float(np.min(1-nodes[b:]/nodes[:-b]))


def anchored(nodes: np.ndarray,h: np.ndarray,t: int):
    k=krylov(nodes,h,t); b=h.shape[1]; m=len(nodes)
    e=np.linalg.solve(k.T,np.eye(m)[:b,:].T).T
    ue,s,ve=np.linalg.svd(e,full_matrices=False)
    return k,e,ue,s,ve


def head_diagnostics() -> list[dict]:
    rows=[]
    for b in (1,2,3,4):
        for t in (1,2,3,4):
            m=b*t
            for kind in ('geometric','repeated','wide_bands'):
                if kind=='geometric':
                    nodes=np.exp(-np.linspace(0,2,m))
                elif kind=='repeated':
                    nodes=np.repeat(np.exp(-np.linspace(0,2,t)),b)
                else:
                    nodes=np.array([math.exp(-0.7*r)*(1-0.20*j/max(1,b-1)) for r in range(t) for j in range(b)])
                delta=gap(nodes,b)
                assert delta>0
                for seed in (11,29):
                    rng=np.random.default_rng(seed+100*b+1000*t)
                    h=rng.standard_normal((m,b))
                    k,e,ue,s,ve=anchored(nodes,h,t)
                    f=1/s[0]; u=ve[0,:]
                    coeff=np.linalg.solve(k,u*f).reshape(t,b)
                    vand=np.vander(nodes,N=t,increasing=True)
                    pvals=vand@coeff
                    d=float(np.sqrt(np.sum(u*u*np.sum(pvals*pvals,axis=1))))
                    direction=-u[:,None]*pvals/d
                    dk=krylov(nodes,direction,t)
                    de=-np.linalg.solve(k.T,(e@dk).T).T
                    analytic_derivative=-float(ue[:,0]@de@ve[0,:])/(s[0]**2)
                    derivative_error=abs(analytic_derivative+d)/max(1,d)
                    moment_residual=float(np.linalg.norm(k[:,b:].T@u)/max(1,np.linalg.norm(k[:,b:],2))) if t>1 else 0.0
                    step=min(1e-5*max(1,np.linalg.norm(h)),1e-4*f/d)
                    fplus=1/anchored(nodes,h+step*direction,t)[3][0]
                    finite_derivative=(fplus-f)/step
                    finite_error=abs(finite_derivative+d)/max(1,d)
                    local_mu=min(np.linalg.svd(h[r:r+b,:],compute_uv=False)[-1] for r in range(m-b+1))
                    rho=(delta/(128*math.e))**(t-1)
                    alpha=local_mu*(delta/(64*m))*rho/(4*math.sqrt(m)*np.linalg.norm(h,2))
                    assert d>=alpha*(1-1e-9)
                    assert derivative_error<2e-5, (b,t,kind,seed,derivative_error)
                    assert finite_error<2e-3, (b,t,kind,seed,finite_error)
                    assert moment_residual<1e-7
                    eta=.1
                    log_bound=24*math.log(2)+8*math.log(m)+4*math.log(1/eta)+t*math.log(128*math.e/delta)
                    maximum_log=-math.inf
                    translation_residual=0.0
                    for x in np.linspace(0,nodes[-1],13):
                        ev=np.concatenate([x**j*np.eye(b) for j in range(t)],axis=1)@np.linalg.inv(k)
                        maximum_log=max(maximum_log,math.log(np.linalg.norm(ev,2)))
                        shifted=anchored(nodes-x,h,t)[1]
                        translation_residual=max(translation_residual,np.linalg.norm(ev-shifted)/max(1,np.linalg.norm(ev)))
                    assert maximum_log<=log_bound
                    assert translation_residual<1e-6
                    rows.append(dict(b=b,t=t,m=m,case=kind,seed=seed,delta=delta,
                        raw_krylov_condition=float(np.linalg.cond(k)),f=f,descent_norm=d,
                        deterministic_alpha=alpha,derivative_relative_error=derivative_error,
                        finite_difference_relative_error=finite_error,moment_relative_residual=moment_residual,
                        translation_relative_residual=translation_residual,
                        log10_interpolation_bound_margin=(log_bound-maximum_log)/math.log(10)))
    return rows


def high_precision_stress() -> list[dict]:
    rows=[]
    with mp.workdps(180):
        for b,t in [(1,3),(2,3)]:
            for exponent in (4,16,50):
                eta=mp.mpf(10)**(-exponent)
                if b==1:
                    nodes=[mp.mpf(1),eta,eta/2]
                    h=mp.matrix([[mp.mpf(7)/10],[-mp.mpf(13)/10],[mp.mpf(1)/2]])
                else:
                    nodes=[mp.mpf(1),mp.mpf(1),mp.mpf(1)/2,mp.mpf(1)/2,eta,eta/2]
                    h=mp.matrix([[1,2],[3,-1],[-2,4],[1,3],[2,-3],[4,1]])
                m=b*t
                k=mp.matrix(m,m)
                for i in range(m):
                    for j in range(t):
                        for r in range(b): k[i,j*b+r]=nodes[i]**j*h[i,r]
                inv=k**-1; e=inv[:b,:]
                singular=mp.svd(k,compute_uv=False)
                enorm=mp.svd(e,compute_uv=False)[0]
                residual=mp.norm(k*inv-mp.eye(m))/max(mp.mpf(1),mp.norm(k)*mp.norm(inv))
                delta=min(1-nodes[i+b]/nodes[i] for i in range(m-b))
                rows.append(dict(b=b,t=t,eta_exponent=exponent,working_decimal_digits=mp.mp.dps,
                    delta=mp.nstr(delta,25),raw_smallest_singular_value=mp.nstr(singular[m-1],25),
                    anchored_evaluation_norm=mp.nstr(enorm,25),normalized_inverse_residual=mp.nstr(residual,12)))
    return rows


def arnoldi_spaces(nodes: np.ndarray,g: np.ndarray,max_q: int):
    u,s,_=np.linalg.svd(g,full_matrices=False)
    rank=int(np.sum(s>1e-13*max(1,s[0])))
    qbasis=u[:,:rank]; last=qbasis.copy()
    yield 1,qbasis.copy()
    for depth in range(2,max_q+1):
        if last.shape[1]:
            w=nodes[:,None]*last
            for _ in range(2): w-=qbasis@(qbasis.T@w)
            un,sn,_=np.linalg.svd(w,full_matrices=False)
            rank=int(np.sum(sn>1e-13))
            rank=min(rank,len(nodes)-qbasis.shape[1])
            last=un[:,:rank]
            qbasis=np.concatenate([qbasis,last],axis=1)
        yield depth,qbasis.copy()


def algorithm_diagnostics() -> list[dict]:
    cases=[]
    b,k,n=4,24,72; head=np.repeat(np.exp(-.25*np.arange(6)),4)
    nodes=np.r_[head,head[-1]*.9*np.exp(-.05*np.arange(n-len(head)))]
    cases.append(('exact_clusters',nodes,b,k,[6,8,12,18]))
    b,k,n=4,19,64; head=np.exp(-.09*np.arange(20))
    nodes=np.r_[head,head[-1]*.97*np.exp(-.035*np.arange(n-len(head)))]
    cases.append(('wide_unaligned',nodes,b,k,[5,7,10,16]))
    b,k,n=3,10,42; head=np.array([1,1,.85,.7,.7,.55,.4,.4,.3,.2,.16,.12])
    nodes=np.r_[head,[.12,.12],.1*np.exp(-.08*np.arange(n-len(head)-2))]
    cases.append(('mixed_multiplicities_boundary',nodes,b,k,[4,6,9,14]))
    b,k,n=3,14,45
    head=np.array([math.exp(-.35*r)*(1-.04*j) for r in range(5) for j in range(3)])
    nodes=np.r_[head,head[-1]*.95*np.exp(-.09*np.arange(n-len(head)))]
    cases.append(('nonzero_width_clusters',nodes,b,k,[5,7,10,15]))
    b,k,n=1,5,20; nodes=np.exp(-.20*np.arange(n))
    cases.append(('scalar_block',nodes,b,k,[5,8,12,20]))
    b,k,n=6,6,32; nodes=np.exp(-.12*np.arange(n))
    cases.append(('full_starting_block',nodes,b,k,[1,2,4,8]))
    b,k,n=3,12,40; nodes=np.r_[np.exp(-.08*np.arange(k)),np.zeros(n-k)]
    cases.append(('zero_optimal_error',nodes,b,k,[4,5,6]))
    rows=[]; eps=.1
    for name,nodes,b,k,depths in cases:
        m=math.ceil(k/b)*b; delta=gap(nodes[:m],b)
        for seed in (101,202,303):
            rng=np.random.default_rng(seed)
            g=rng.standard_normal((len(nodes),b)); a=np.diag(np.sqrt(nodes))
            for depth,qbasis in arnoldi_spaces(nodes,g,max(depths)):
                if depth not in depths: continue
                uq,s,vt=np.linalg.svd(qbasis.T@a,full_matrices=False)
                ahat=((qbasis@uq[:,:k])*s[:k])@vt[:k,:]
                residual=a-ahat
                err2=np.linalg.norm(residual,2); errf=np.linalg.norm(residual,'fro')
                energies=np.sum(nodes[None,:]*(vt[:k,:]**2),axis=1)
                defect=float(np.max(np.abs(energies-nodes[:k])))
                opt2=math.sqrt(nodes[k]) if k<len(nodes) else 0.0
                optf=math.sqrt(np.sum(nodes[k:]))
                record=dict(case=name,n=len(nodes),b=b,k=k,m=m,q=depth,seed=seed,delta=delta,
                    basis_dimension=qbasis.shape[1],orthogonality_error=float(np.linalg.norm(qbasis.T@qbasis-np.eye(qbasis.shape[1]))),
                    spectral_error=float(err2),frobenius_error=float(errf),right_energy_defect=defect,
                    spectral_ratio=float(err2/opt2) if opt2 else None,
                    frobenius_ratio=float(errf/optf) if optf else None,
                    relative_right_energy_defect=defect/nodes[k] if opt2 else None)
                if opt2:
                    record['all_criteria_at_epsilon_0_1']=bool(err2<=(1+eps)*opt2+1e-12 and errf<=(1+eps)*optf+1e-12 and defect<=eps*nodes[k]+1e-12)
                else:
                    record['all_criteria_at_epsilon_0_1']=bool(max(err2,errf,defect)<=1e-10)
                    if depth>=math.ceil(k/b)+1:
                        assert record['all_criteria_at_epsilon_0_1'],record
                rows.append(record)
    return rows


def write_csv(path: Path,rows: list[dict]):
    with path.open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0])); writer.writeheader(); writer.writerows(rows)


def main(out: Path):
    out.mkdir(parents=True,exist_ok=True)
    head=head_diagnostics(); stress=high_precision_stress(); algo=algorithm_diagnostics()
    write_csv(out/'head_diagnostics.csv',head)
    write_csv(out/'algorithm_diagnostics.csv',algo)
    (out/'high_precision_stress.json').write_text(json.dumps(stress,indent=2)+'\n')
    summary=dict(status='PASS',python=platform.python_version(),numpy=np.__version__,mpmath=mp.__version__,
        head_records=len(head),algorithm_records=len(algo),high_precision_records=len(stress),
        max_analytic_derivative_relative_error=max(r['derivative_relative_error'] for r in head),
        max_finite_difference_relative_error=max(r['finite_difference_relative_error'] for r in head),
        max_moment_relative_residual=max(r['moment_relative_residual'] for r in head),
        max_translation_relative_residual=max(r['translation_relative_residual'] for r in head),
        minimum_log10_interpolation_bound_margin=min(r['log10_interpolation_bound_margin'] for r in head),
        algorithm_records_meeting_epsilon_0_1=sum(r['all_criteria_at_epsilon_0_1'] for r in algo),
        limitations='Numerical diagnostics, not probability estimates, forward-error certificates, or universal proof verification. Exact-arithmetic theorem is distinct from binary64 execution.')
    (out/'numerical_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser(); parser.add_argument('--output-dir',type=Path,default=Path('results'))
    main(parser.parse_args().output_dir)
