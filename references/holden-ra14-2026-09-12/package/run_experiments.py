"""Reproduce the numerical illustrations (not probabilistic lower-bound proofs).

Run from the package directory:
    OPENBLAS_NUM_THREADS=1 python run_experiments.py
Validation computes dense norms/eigenvalues outside the oracle-counted solver.
"""
from __future__ import annotations
import csv
import json
import math
import platform
from pathlib import Path
import numpy as np
import sympy as sp
from src.ra14 import (
    dense_oracle, block_krylov_lra, warm_start_pca, sharp_overlap_instance,
    residual_norm, fejer_polynomial,
)

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results'


def inverse_sqrt(a):
    w, v = np.linalg.eigh(a)
    return (v / np.sqrt(w)) @ v.T


def write_csv(path, rows):
    with path.open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def main():
    OUT.mkdir(exist_ok=True)
    rng = np.random.default_rng(2026091214)
    rows = []
    n, k, eps = 96, 4, .1
    for family in ['flat_spike', 'slow_decay', 'large_dynamic_range']:
        for trial in range(30):
            if family == 'flat_spike':
                singulars = np.r_[np.full(k, 1.2), np.linspace(1, .05, n-k)]
            elif family == 'slow_decay':
                singulars = .96 ** np.arange(n)
            else:
                singulars = np.r_[1e4, 1e3, 10, 2, np.linspace(1, .01, n-k)]
            left = np.linalg.qr(rng.normal(size=(n,n)))[0]
            right = np.linalg.qr(rng.normal(size=(n,n)))[0]
            a = (left*singulars)@right.T
            # A fixed seed couples depths within each trial.
            algorithm_seed = int(rng.integers(0, 2**32-1))
            for steps in [2, 4, 8]:
                oracle = dense_oracle(a)
                z = block_krylov_lra(oracle, k, steps,
                                     np.random.default_rng(algorithm_seed))
                ratio = residual_norm(a,z)/singulars[k]
                rows.append(dict(family=family, trial=trial, n=n, k=k,
                                 epsilon=eps, steps=steps, queries=oracle.queries,
                                 query_bound=k*(2*steps+2), residual_ratio=ratio,
                                 meets_target=bool(ratio <= 1+eps+1e-9),
                                 orthogonality_error=float(np.linalg.norm(z.T@z-np.eye(k),2))))
    write_csv(OUT/'krylov_trials.csv', rows)

    warm_rows = []
    for n, k, eps in [(120,3,.49),(160,3,.1),(80,4,.01)]:
        for trial in range(20):
            top = 1+1.5*eps+np.linspace(0,.7,k)
            tail = np.linspace(-1,1,n-k)
            tau = 1+eps
            contraction = rng.normal(size=(n-k,k))
            contraction /= np.linalg.norm(contraction,2)
            graph = np.sqrt(tau*tau-tail*tail)[:,None]*contraction
            graph /= np.sqrt(top*top-tau*tau)[None,:]
            z = np.vstack((np.eye(k),graph))@inverse_sqrt(np.eye(k)+graph.T@graph)
            rotation = np.linalg.qr(rng.normal(size=(n,n)))[0]
            a = (rotation*np.r_[top,tail])@rotation.T
            z = rotation@z
            oracle = dense_oracle(a,symmetric=True)
            result = warm_start_pca(oracle,z,eps)
            initial = float(np.trace(z.T@a@z)/top.sum())
            final = float(np.trace(result.T@a@result)/top.sum())
            warm_rows.append(dict(n=n,k=k,epsilon=eps,trial=trial,
                                  initial_residual=residual_norm(a,z),
                                  allowed_residual=tau,initial_trace_fraction=initial,
                                  final_trace_fraction=final,
                                  required_trace_fraction=1-eps/200,
                                  queries=oracle.queries,
                                  query_bound=k*math.ceil(10/math.sqrt(eps)),
                                  meets_target=bool(final >= 1-eps/200-1e-10)))
    write_csv(OUT/'warm_start_trials.csv',warm_rows)

    sharp_rows = []
    for eps in [.1,.01,.001,1e-4,1e-6]:
        a,z,alpha2 = sharp_overlap_instance(4,eps)
        sharp_rows.append(dict(epsilon=eps,rank=4,n=9,
                               overlap_squared=alpha2,
                               residual_ratio=residual_norm(a,z),
                               pca_trace_fraction=float(np.trace(z.T@a@z)/(4*(1+2*eps)))))
    write_csv(OUT/'sharp_counterexample.csv',sharp_rows)

    scalar_rows=[]
    for eps in np.geomspace(1e-8,.49,20):
        m=math.ceil(10/math.sqrt(eps))
        s=np.unique(np.r_[np.linspace(0,2,16001),np.geomspace(1e-12,2,4000)])
        x=1-s
        a0,tau=1+1.5*eps,1+eps
        coeff=(a0-x)*(tau*tau-x*x)/(a0*a0-tau*tau)
        coeff *= (fejer_polynomial(x,m)/fejer_polynomial(a0,m))**2
        scalar_rows.append(dict(epsilon=float(eps),m=m,
                                max_coefficient_over_epsilon=float(coeff.max()/eps),
                                proved_upper_bound=1/200))
    write_csv(OUT/'fejer_scalar_grid.csv',scalar_rows)

    group=[]
    for family in ['flat_spike','slow_decay','large_dynamic_range']:
        for steps in [2,4,8]:
            r=[x for x in rows if x['family']==family and x['steps']==steps]
            group.append(dict(family=family,steps=steps,trials=len(r),
                              successes=sum(x['meets_target'] for x in r),
                              min_queries=min(x['queries'] for x in r),
                              max_queries=max(x['queries'] for x in r),
                              max_residual_ratio=max(x['residual_ratio'] for x in r)))
    lower=sum(sp.Rational(10**(2*j),math.factorial(2*j)) for j in range(1,8))
    summary=dict(
        status='Numerical illustrations; no formal or universal lower-bound verification',
        seed=2026091214,
        environment=dict(python=platform.python_version(),numpy=np.__version__,sympy=sp.__version__),
        krylov_trials=len(rows),krylov_groups=group,
        warm_start_trials=len(warm_rows),
        warm_start_successes=sum(x['meets_target'] for x in warm_rows),
        warm_start_min_final_trace_fraction=min(x['final_trace_fraction'] for x in warm_rows),
        warm_start_max_query_budget_violation=max(x['queries']-x['query_bound'] for x in warm_rows),
        max_orthogonality_error=max(x['orthogonality_error'] for x in rows),
        fejer_grid_cases=len(scalar_rows),
        fejer_max_coefficient_over_epsilon=max(x['max_coefficient_over_epsilon'] for x in scalar_rows),
        exact_cosh_certificate=str(lower),
        exact_cosh_certificate_greater_than_10000=bool(lower>10000),
    )
    (OUT/'validation.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':
    main()
