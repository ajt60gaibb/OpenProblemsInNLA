"""Reproduce component tests and diagnostics, retaining all outcomes.

Usage: OPENBLAS_NUM_THREADS=1 python run_checks.py
This runner also extracts the preserved v4 archive to a temporary directory
and reruns its two unchanged test suites.  It does not modify prior artifacts.
"""
from __future__ import annotations
import csv
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import subprocess
import sys
import tempfile
import zipfile
from datetime import datetime, timezone
import numpy as np
import scipy
from src.wishart_geometry import (
    haar_frame, sample_tilted_wishart, schur_components, kernel_graph,
    ridge_potential, angular_quantities, angular_bound, logdet_spd,
    SymmetricOracle, adaptive_frames, finite_accuracy_scale,
)

ROOT=Path(__file__).resolve().parent
OUT=ROOT/'results'


def suite(name: str, cwd: Path, test_dir: str) -> dict:
    p=subprocess.run([sys.executable,'-m','unittest','discover','-s',test_dir,'-v'],
                     cwd=cwd,text=True,capture_output=True,
                     env={**os.environ,'OPENBLAS_NUM_THREADS':'1'})
    (OUT/f'{name}.stdout.txt').write_text(p.stdout)
    (OUT/f'{name}.stderr.txt').write_text(p.stderr)
    import re
    match=re.search(r'Ran (\d+) tests?',p.stdout+p.stderr)
    return {'name':name,'exit_code':p.returncode,
            'test_count':int(match.group(1)) if match else None,
            'stdout':f'{name}.stdout.txt','stderr':f'{name}.stderr.txt'}


def save_csv(name: str, rows: list[dict]) -> None:
    with (OUT/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)


def geometry_trials() -> dict:
    rng=np.random.default_rng(8142026);rows=[]
    for n,k,t in [(18,2,4),(28,3,6),(48,4,8)]:
        for nu in [0,4,20]:
            for trial in range(8):
                h,u=sample_tilted_wishart(n,k,nu,rng,scale=1/n)
                v=haar_frame(n,t,rng);a,b,s,w=schur_components(h,v)
                _,qs=np.linalg.eigh(s);us=qs[:,:k]
                c,z,km=kernel_graph(a,b,us)
                pdet_l=np.log(np.linalg.eigvalsh(h)[k:]).sum()
                pdet_r=logdet_spd(a)+np.log(np.linalg.eigvalsh(s)[k:]).sum()+logdet_spd(np.eye(k)+c)
                alpha=max(1,nu)/k
                direct=ridge_potential(u,v,alpha)
                graph=logdet_spd(np.eye(k)+(1+alpha)*c)-logdet_spd(np.eye(k)+c)
                rows.append({'n':n,'k':k,'nu':nu,'t':t,'trial':trial,
                    'pseudodeterminant_log_error':abs(pdet_l-pdet_r),
                    'potential_graph_error':abs(direct-graph),
                    'kernel_equation_error':float(np.linalg.norm(h@np.column_stack([v,w])@z,2))})
    save_csv('geometry_trials.csv',rows)
    return {'rows':len(rows),
            'maximum_pseudodeterminant_log_error':max(r['pseudodeterminant_log_error'] for r in rows),
            'maximum_potential_graph_error':max(r['potential_graph_error'] for r in rows),
            'maximum_kernel_equation_error':max(r['kernel_equation_error'] for r in rows)}


def angular_trials() -> dict:
    # Importance sampling under the exact angular density.  Standard errors
    # below are asymptotic self-normalized importance-sampling diagnostics.
    rng=np.random.default_rng(9152026);rows=[];draws=10000
    cases=[(8,1,0,2),(8,1,5,1),(12,2,8,2),(10,3,10,3),
           (20,2,30,0.3),(16,3,4,10)]
    for case,(d,k,nu,scale) in enumerate(cases):
        km=np.diag(np.linspace(0,scale,d));v=np.eye(d)[:,-1]
        beta=1+nu/k;logw=[];values=[]
        for _ in range(draws):
            u=haar_frame(d,k,rng)
            values.append(angular_quantities(u,km,v,beta,nu))
            logw.append(nu/2*logdet_spd(np.eye(k)+u.T@km@u))
        values=np.asarray(values);logw=np.asarray(logw)
        weights=np.exp(logw-logw.max());weights/=weights.sum()
        station_values=values[:,0]+values[:,1]
        station=float(weights@station_values)
        se=float(np.sqrt(np.sum(weights**2*(station_values-station)**2)))
        observed=float(weights@values[:,2]);bound=angular_bound(d,k,nu,beta)
        rows.append({'case':case,'d':d,'k':k,'nu':nu,'K_scale':scale,
                     'draws':draws,'effective_sample_size':float(1/(weights@weights)),
                     'stationarity_mean':station,'stationarity_asymptotic_se':se,
                     'observed_regularized_moment':observed,
                     'proved_moment_upper_bound':bound,
                     'observed_over_bound':observed/bound})
    save_csv('angular_diagnostics.csv',rows)
    return {'cases':len(rows),'total_draws':len(rows)*draws,
            'minimum_effective_sample_size':min(r['effective_sample_size'] for r in rows),
            'maximum_observed_over_proved_bound':max(r['observed_over_bound'] for r in rows),
            'maximum_absolute_stationarity_mean':max(abs(r['stationarity_mean']) for r in rows)}


def adaptive_trials() -> dict:
    rows=[];index=0
    for n in [48,72,96]:
        for k in [1,3]:
            for nu in [2,8,32]:
                for strategy in ['random','krylov','reply_null']:
                    for trial in range(8):
                        seed=722100+index;index+=1
                        rng=np.random.default_rng(seed)
                        h,u=sample_tilted_wishart(n,k,nu,rng,scale=1/n)
                        oracle=SymmetricOracle(h)
                        frames=adaptive_frames(oracle,n//4,strategy,rng)
                        for t,v in enumerate(frames):
                            rows.append({'n':n,'k':k,'nu':nu,'strategy':strategy,
                                'trial':trial,'seed':seed,'t':t,
                                'potential':ridge_potential(u,v,nu/k),
                                'expectation_upper_bound':4*nu*t/n,
                                'kernel_trace':float(np.linalg.norm(u.T@v,'fro')**2),
                                'orthogonality_error':float(np.linalg.norm(v.T@v-np.eye(t),2)) if t else 0.,
                                'total_queries_in_run':oracle.queries})
    save_csv('adaptive_trials.csv',rows)
    # Compare sample means only; the theorem does not bound each realized path.
    groups={}
    for row in rows:
        key=(row['n'],row['k'],row['nu'],row['strategy'],row['t'])
        groups.setdefault(key,[]).append(row['potential'])
    aggregates=[]
    for (n,k,nu,strategy,t),vals in groups.items():
        vals=np.asarray(vals);bound=4*nu*t/n
        aggregates.append({'n':n,'k':k,'nu':nu,'strategy':strategy,'t':t,
                           'runs':len(vals),'mean_potential':float(vals.mean()),
                           'sample_standard_error':float(vals.std(ddof=1)/math.sqrt(len(vals))),
                           'expectation_upper_bound':bound,
                           'mean_over_bound':float(vals.mean()/bound) if bound else 0.})
    save_csv('adaptive_expectations.csv',aggregates)
    return {'runs':index,'path_rows':len(rows),'expectation_rows':len(aggregates),
            'maximum_orthogonality_error':max(r['orthogonality_error'] for r in rows),
            'maximum_empirical_mean_over_proved_bound':max(r['mean_over_bound'] for r in aggregates),
            'empirical_mean_exceedances':sum(r['mean_potential']>r['expectation_upper_bound']+1e-12 for r in aggregates)}


def parameter_trials() -> dict:
    rows=[]
    for n in [100,1000,10000,1000000]:
        for k in [1,2,10]:
            if k>=n:continue
            x=n/k;ell=math.log(math.e*x)
            for y in [0.01,0.1,1,math.sqrt(ell),ell,ell**2,math.sqrt(x)]:
                eps=(y/x)**2
                if not 0<eps<0.5: continue
                lower=finite_accuracy_scale(n,k,eps)
                upper=min(n,k/math.sqrt(eps)*ell)
                rows.append({'n':n,'k':k,'epsilon':eps,'y':y,'F_lower_scale':lower,
                             'U_upper_scale_without_constants':upper,'scale_ratio':upper/lower,
                             'maximum_ratio_for_this_x':ell/math.log1p(ell)})
    save_csv('finite_parameter_scales.csv',rows)
    return {'rows':len(rows),'maximum_scale_ratio':max(r['scale_ratio'] for r in rows)}


def main() -> int:
    OUT.mkdir(exist_ok=True)
    suites=[suite('unit_tests',ROOT,'tests')]
    previous=ROOT/'prior'/'RA14_adaptive_lower_bounds_v4.zip'
    with tempfile.TemporaryDirectory(prefix='ra14_v4_check_') as tmp:
        with zipfile.ZipFile(previous) as z:z.extractall(tmp)
        prev=Path(tmp)/'RA14_adaptive_lower_bounds_v4'
        suites.append(suite('unchanged_v4_components',prev,'tests'))
        suites.append(suite('unchanged_v3_upper_bound',prev/'upper_bound','tests'))
    summary={'created_utc':datetime.now(timezone.utc).isoformat(),
        'environment':{'python':platform.python_version(),'numpy':np.__version__,
                       'scipy':scipy.__version__,'platform':platform.platform()},
        'suites':suites,'all_suites_passed':all(s['exit_code']==0 for s in suites),
        'geometry':geometry_trials(),'angular':angular_trials(),
        'adaptive':adaptive_trials(),'parameters':parameter_trials(),
        'prior_zip_sha256':hashlib.sha256(previous.read_bytes()).hexdigest(),
        'limitations':[
            'Component checks do not establish a universal statement about all adaptive algorithms.',
            'The all-adaptive proof is the manuscript, with the RV theorem explicitly imported.',
            'No numerical value for the universal lower-bound constant is inferred from these runs.',
            'Importance-sampling standard errors are diagnostic, not rigorous confidence certificates.',
            'The expectation bound is not a bound on every individual realized query path.',
            'Hidden kernel bases are available only to validation code, not query selection.',
            'All floating-point outcomes are retained; these are not exact-real computations.',
            'No new all-parameter upper-bound algorithm is claimed.',
        ]}
    (OUT/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
    return 0 if summary['all_suites_passed'] else 1

if __name__=='__main__':raise SystemExit(main())
