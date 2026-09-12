#!/usr/bin/env python3
"""Reproducible finite-precision checks accompanying the RA-04 report.

The mathematical target is exact arithmetic.  These experiments are evidence
about selected instances, not a proof of the general assertion.  In particular,
no numerical value of the universal constant in RA-04 is being certified.
"""
from __future__ import annotations
import argparse
import csv
import json
from pathlib import Path
from typing import Any
import numpy as np
import mpmath as mp
from threadpoolctl import threadpool_limits


def gap_b(lam: np.ndarray, b: int) -> float:
    if len(lam) == b:
        return 1.0
    return float(np.min((lam[:-b]-lam[b:])/lam[:-b]))


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise ValueError('No rows to write.')
    with path.open('w', newline='', encoding='utf-8') as file:
        writer = csv.DictWriter(file, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def append_orthogonal_block(Z: np.ndarray, V: np.ndarray) -> np.ndarray:
    """Two-pass reorthogonalization and SVD numerical-rank detection."""
    if Z.shape[1]:
        for _ in range(2):
            V = V-Z@(Z.T@V)
    U, s, _ = np.linalg.svd(V, full_matrices=False)
    if not s.size or s[0] == 0:
        return np.empty((V.shape[0],0))
    threshold = 64*np.finfo(float).eps*max(V.shape)*max(1.0,s[0])
    return U[:,s>threshold]


def block_krylov_basis(lam: np.ndarray, G: np.ndarray, q: int) -> np.ndarray:
    if q < 1 or len(lam) != G.shape[0]:
        raise ValueError('Invalid Krylov parameters.')
    Z = np.empty((len(lam),0))
    block = append_orthogonal_block(Z,G)
    for j in range(q):
        if block.shape[1] == 0:
            break
        Z = np.hstack((Z,block))
        if Z.shape[1] >= len(lam):
            break
        if j+1 < q:
            block = append_orthogonal_block(Z,lam[:,None]*block)
    return Z


def approximation_metrics(lam: np.ndarray, k: int, G: np.ndarray, q: int) -> dict[str, Any]:
    Z = block_krylov_basis(lam,G,q)
    sigma = np.sqrt(lam)
    projected = Z.T*sigma[None,:]
    U, s, Vh = np.linalg.svd(projected, full_matrices=False)
    if len(s) < k:
        raise ValueError('The numerical Krylov subspace has fewer than k directions.')
    Ahat = (Z@U[:,:k]*s[:k][None,:])@Vh[:k,:]
    residual = np.diag(sigma)-Ahat
    error2 = float(np.linalg.norm(residual,2))
    errorF = float(np.linalg.norm(residual,'fro'))
    tail2 = float(sigma[k]) if k < len(lam) else 0.0
    tailF = float(np.linalg.norm(sigma[k:]))
    energies = (Vh[:k,:]**2)@lam
    pca_error = float(np.max(np.abs(energies-lam[:k])))
    return {'q':q, 'numerical_subspace_dimension':Z.shape[1],
            'spectral_ratio':error2/tail2 if tail2 > 0 else '',
            'frobenius_ratio':errorF/tailF if tailF > 0 else '',
            'right_pca_normalized_error':pca_error/(tail2**2) if tail2 > 0 else '',
            'spectral_absolute_error':error2, 'frobenius_absolute_error':errorF,
            'right_pca_absolute_error':pca_error,
            'orthogonality_error':float(np.linalg.norm(Z.T@Z-np.eye(Z.shape[1]),2))}


def instances() -> list[dict[str, Any]]:
    result = []
    centers = np.array([8.0,5.0,3.0,2.0,1.5,1.2])
    result.append({'case':'exact_b_fold_clusters','b':4,'k':24,
                   'lam':np.r_[np.repeat(centers,4),np.linspace(1.0,.025,136)],
                   'q_values':[6,8,10,12,16,20]})
    result.append({'case':'near_b_fold_clusters','b':4,'k':24,
                   'lam':np.r_[np.concatenate([c*np.linspace(1.0001,.9999,4) for c in centers]),
                                np.linspace(1.0,.025,136)],
                   'q_values':[6,8,10,12,16,20]})
    result.append({'case':'t2_unaligned_spectrum','b':8,'k':14,
                   'lam':np.r_[np.linspace(4,1.2,16),np.linspace(1,.025,112)],
                   'q_values':[2,3,4,6,8,12]})
    result.append({'case':'nondivisible_target_rank','b':4,'k':15,
                   'lam':np.r_[np.concatenate([c*np.linspace(1.001,.999,4) for c in [5,3,2,1.3]]),
                                np.linspace(1,.02,80)],
                   'q_values':[4,6,8,10,12,16]})
    result.append({'case':'mixed_multiplicities','b':3,'k':12,
                   'lam':np.r_[np.array([5,5,4,3,3,3,2,2,1.5,1.3,1.3,1.2]),
                                np.linspace(1.1,.025,84)],
                   'q_values':[4,6,8,10,12,16]})
    result.append({'case':'scalar_block','b':1,'k':6,
                   'lam':np.r_[centers,np.linspace(1,.025,54)],
                   'q_values':[6,8,10,12,16,20]})
    result.append({'case':'rank_equals_kprime','b':4,'k':24,
                   'lam':np.r_[np.linspace(5,1,24),np.zeros(56)],
                   'q_values':[6,7,8]})
    for case in result:
        m = case['b']*((case['k']+case['b']-1)//case['b'])
        if np.any(np.diff(case['lam'])>0) or case['lam'][m-1] <= 0:
            raise AssertionError('Invalid test spectrum.')
        case['m'] = m
    return result


def rbki_checks() -> list[dict[str, Any]]:
    rows = []
    for case_id,case in enumerate(instances()):
        for repetition in range(3):
            seed = 1729+100*case_id+repetition
            rng = np.random.default_rng(seed)
            G = rng.standard_normal((len(case['lam']),case['b']))
            for q in case['q_values']:
                row = {'case':case['case'],'seed':seed,'n':len(case['lam']),
                       'b':case['b'],'k':case['k'],'kprime':case['m'],
                       'gap_b':gap_b(case['lam'][:case['m']],case['b'])}
                row.update(approximation_metrics(case['lam'],case['k'],G,q))
                rows.append(row)
    return rows


def t2_bounds() -> list[dict[str, Any]]:
    rows = []
    for b in [1,2,4,8,16]:
        m=2*b
        lam=np.linspace(2.0,1.0,m)
        gap=gap_b(lam,b)
        for rep in range(10):
            seed=9000+100*b+rep
            H=np.random.default_rng(seed).standard_normal((m,b))
            K=np.hstack((H,lam[:,None]*H))
            inverse=np.linalg.inv(K)
            ratios=[]
            for i in range(m):
                near=np.flatnonzero((lam>=(1-gap/2)*lam[i])&(lam<=(1+gap/2)*lam[i])).tolist()
                near += [j for j in range(m) if j not in near][:b-len(near)]
                far=[j for j in range(m) if j not in near]
                HS=H[far,:]
                z=inverse[:b,i]+lam[i]*inverse[b:,i]
                # For a normalized leave-one-out vector, |alpha|=1/||z||.
                alpha_abs=1/np.linalg.norm(z)
                bound=(1+2*np.linalg.cond(HS)/gap)/alpha_abs
                for x in np.linspace(0,lam[-1],21):
                    value=inverse[:b,i]+x*inverse[b:,i]
                    ratios.append(float(np.linalg.norm(value)/bound))
            rows.append({'b':b,'m':m,'seed':seed,'gap_b':gap,
                         'max_observed_column_bound_ratio':max(ratios),
                         'matrix_inverse_residual':float(np.linalg.norm(K@inverse-np.eye(m),'fro'))})
    return rows


def high_precision_probes() -> list[dict[str, Any]]:
    rows=[]
    mp.mp.dps=120
    for b,t,rho in [(1,8,mp.mpf('0.8')),(4,6,mp.mpf('0.25')),
                    (8,8,mp.mpf('0.8')),(12,6,mp.mpf('0.25'))]:
        for rep in range(3):
            seed=31415+100*b+10*t+rep
            rng=np.random.default_rng(seed)
            m=b*t
            if b == 1:
                factors=[mp.mpf(1)]
            else:
                factors=[1-mp.mpf(j)/(10*(b-1)) for j in range(b)]
            lam=[rho**r*f for r in range(t) for f in factors]
            x=lam[-1]/2
            H=rng.standard_normal((m,b))
            g=rng.standard_normal(b)
            # Center the polynomial basis at x.  This leaves the graph invariant.
            K=mp.matrix([[mp.mpf(float(H[i,c]))*(lam[i]-x)**j
                          for j in range(t) for c in range(b)] for i in range(m)])
            rhs=mp.matrix([mp.mpf(float(g[c])) if j==0 else 0
                           for j in range(t) for c in range(b)])
            z=mp.lu_solve(K.T,rhs)
            rel=mp.norm(K.T*z-rhs)/(mp.norm(K)*mp.norm(z)+mp.norm(rhs))
            actual_gap=min((lam[i]-lam[i+b])/lam[i] for i in range(m-b))
            rows.append({'b':b,'t':t,'m':m,'seed':seed,'rho':str(rho),
                         'gap_b':mp.nstr(actual_gap,18),'decimal_precision':mp.mp.dps,
                         'log_single_tail_graph_norm':mp.nstr(mp.log(mp.norm(z)),18),
                         'relative_linear_solve_residual':mp.nstr(rel,6)})
    return rows


def raw_conditioning_examples() -> list[dict[str, Any]]:
    mp.mp.dps=100
    g=[mp.mpf('.7'),mp.mpf('-1.3'),mp.mpf('.5')]
    rows=[]
    for exponent in [1,2,4,6,8,12,16,24]:
        eta=mp.mpf(10)**(-exponent)
        lam=[mp.mpf(1),eta,eta/2]
        K=mp.matrix([[g[i]*lam[i]**j for j in range(3)] for i in range(3)])
        singular=mp.svd(K,compute_uv=False)
        actual=singular[len(singular)-1]
        bound=eta/mp.sqrt(2)*mp.sqrt(g[1]**2+g[2]**2/4)
        assert actual <= bound*(1+mp.mpf('1e-70'))
        rows.append({'eta':mp.nstr(eta,10),'gap_b':'0.5',
                     'sigma_min':mp.nstr(actual,18),'test_vector_upper_bound':mp.nstr(bound,18),
                     'decimal_precision':mp.mp.dps})
    return rows


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,default=Path('results'))
    parser.add_argument('--skip-high-precision',action='store_true')
    args=parser.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    with threadpool_limits(limits=1):
        rbki=rbki_checks()
        t2=t2_bounds()
        raw=raw_conditioning_examples()
        hp=[] if args.skip_high_precision else high_precision_probes()
    write_csv(args.output_dir/'rbki_metrics.csv',rbki)
    write_csv(args.output_dir/'t2_bound_checks.csv',t2)
    write_csv(args.output_dir/'raw_conditioning.csv',raw)
    if hp:
        write_csv(args.output_dir/'high_precision_graph_probes.csv',hp)
    target_epsilon=.1
    representative=[]
    for case in instances():
        subset=[r for r in rbki if r['case']==case['case']]
        success=[]
        for q in case['q_values']:
            values=[r for r in subset if r['q']==q]
            if values[0]['spectral_ratio'] == '':
                ok=all(r['spectral_absolute_error']<1e-10 and r['right_pca_absolute_error']<1e-10 for r in values)
            else:
                ok=all(r['spectral_ratio']<=1+target_epsilon and
                       r['frobenius_ratio']<=1+target_epsilon and
                       r['right_pca_normalized_error']<=target_epsilon for r in values)
            if ok:
                success.append(q)
        representative.append({'case':case['case'],'n':len(case['lam']),
                               'b':case['b'],'k':case['k'],'kprime':case['m'],
                               'smallest_tested_q_passing_all_three_seeds':min(success) if success else None})
    summary={'numpy_version':np.__version__,'mpmath_version':mp.__version__,
             'rbki_rows':len(rbki),'t2_bound_rows':len(t2),'high_precision_rows':len(hp),
             'raw_conditioning_rows':len(raw),
             'max_t2_column_bound_ratio':max(r['max_observed_column_bound_ratio'] for r in t2),
             'max_rbki_orthogonality_error':max(r['orthogonality_error'] for r in rbki),
             'target_epsilon_for_summary':target_epsilon,'representative_summary':representative,
             'limitation':'Selected numerical instances only; not a proof or a certified universal constant.'}
    (args.output_dir/'numerical_summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    main()
