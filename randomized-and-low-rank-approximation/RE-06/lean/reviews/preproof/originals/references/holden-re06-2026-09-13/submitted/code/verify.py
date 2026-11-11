"""Reproducible numerical audits for the RE-06 proof and implementation.

Run from this directory: OPENBLAS_NUM_THREADS=1 python verify.py
Output is written to ../results. These experiments are not a proof, and the
end-to-end experiments deliberately use dimensions smaller than the explicit
sufficient constants of the theorem.
"""
from __future__ import annotations
import csv
import json
import math
import platform
from pathlib import Path
import numpy as np
import scipy
from scipy.stats import chi2
from re06 import make_sketch_plan, collect_answers, postprocess

OUT = Path(__file__).resolve().parents[1] / 'results'
OUT.mkdir(exist_ok=True)
rng = np.random.default_rng(20260912)


def flat_tail_audit():
    rows = []
    for r in [1,2,4,8,16]:
        for s in [1,2,4,8,16,32]:
            for eta in [.03,.05,.1,.2,.4,.8]:
                sizes = sorted({r+1,2*r,4*r,math.ceil(r/eta),math.ceil(10*r/eta)})
                for n in sizes:
                    if n <= r:
                        continue
                    probability = float(chi2.cdf(s*(1-eta)*(n-r),s*n))
                    bound = math.exp(-s*r*eta/4)
                    assert probability <= bound*(1+1e-12)
                    rows.append(dict(n=n,r=r,s=s,eta=eta,exact_probability=probability,
                                     proved_bound=bound,ratio=probability/bound))
    with (OUT/'flat_spectrum_tail_audit.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=rows[0].keys());writer.writeheader();writer.writerows(rows)
    return {'cases':len(rows),'max_probability_to_bound_ratio':max(x['ratio'] for x in rows)}


def chernoff_algebra_audit():
    worst_slack = float('inf')
    for _ in range(3000):
        n=int(rng.integers(3,250));r=int(rng.integers(1,n));s=int(rng.integers(1,80))
        eta=float(rng.uniform(.001,.99))
        lam=np.sort(np.exp(rng.normal(0,3,n)))[::-1]
        T=float(lam[r:].sum());L=float(lam[r]);theta=eta/(2*L)
        log_chernoff=s*theta*(1-eta)*T-.5*s*float(np.log1p(2*theta*lam).sum())
        target=-s*r*eta/4
        slack=target-log_chernoff
        assert slack >= -1e-8
        worst_slack=min(worst_slack,slack)
    return {'spectra_checked':3000,'minimum_log_bound_slack':worst_slack}


def pseudoinverse_moment_audit():
    rows=[]
    trials=5000
    for d,p in [(1,6),(2,8),(4,12),(8,20)]:
        X=rng.normal(size=(trials,d,p))
        values=np.trace(np.linalg.inv(X @ X.transpose(0,2,1)),axis1=1,axis2=2)
        mean=float(values.mean());se=float(values.std(ddof=1)/math.sqrt(trials))
        theory=d/(p-d-1)
        rows.append(dict(d=d,p=p,trials=trials,observed_mean=mean,theory=theory,
                         standard_error=se,z_score=(mean-theory)/se))
    with (OUT/'pseudoinverse_moments.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=rows[0].keys());writer.writeheader();writer.writerows(rows)
    return rows


def unit_vectors(n,m):
    v=rng.normal(size=(m,n))
    return v / np.linalg.norm(v,axis=1,keepdims=True)


def data_cases():
    n=64
    # A genuinely fixed target and fixed family are reused across random plans.
    u=unit_vectors(n,128);v=unit_vectors(n,128)
    spikes=[4*np.outer(u[i],v[i]) for i in range(128)]
    yield 'rank_one_distractors',np.eye(n)/math.sqrt(n),[np.zeros((n,n))]+spikes,(1,8,18)
    base=rng.normal(size=(n,n))
    family=[base+2*np.outer(u[i],v[i]) for i in range(32)]
    E=rng.normal(size=(n,n));E*=.7/np.linalg.norm(E)
    yield 'translated_rank_one_family',family[11]+E,family,(3,10,22)
    family=[rng.normal(size=(n,n))/math.sqrt(n) for _ in range(32)]
    E=rng.normal(size=(n,n));E*=2/np.linalg.norm(E)
    yield 'dense_full_rank_family',family[9]+E,family,(3,8,18)
    base=rng.normal(size=(n,n))
    family=[]
    for j in range(48):
        rank=1+j%6
        B=rng.normal(size=(n,rank))@rng.normal(size=(rank,n))
        family.append(base+B/np.linalg.norm(B)*3)
    E=rng.normal(size=(n,2))@rng.normal(size=(2,n));E*=1/np.linalg.norm(E)
    yield 'mixed_rank_family_low_rank_noise',family[17]+E,family,(2,10,22)


def end_to_end_audit():
    summaries=[];trials_rows=[]
    trials=160;epsilon=.25
    for case,A,F,dims in data_cases():
        s,k,ell=dims
        opt=min(np.linalg.norm(A-B,'fro') for B in F)
        warm_ratios=[];final_ratios=[];surrogate_ratios=[]
        for trial in range(trials):
            plan=make_sketch_plan(len(A),s,k,ell,seed=700000+trial)
            log=[]
            def av(v): log.append(('A',v.copy()));return A@v
            def atv(v):log.append(('AT',v.copy()));return A.T@v
            answers=collect_answers(plan,av,atv)
            result=postprocess(plan,answers,F)
            assert len(log)==s+k+ell
            for (actual_side,actual_vector),(planned_side,planned_vector) in zip(log,plan.queries()):
                assert actual_side==planned_side and np.array_equal(actual_vector,planned_vector)
            wr=float(np.linalg.norm(A-F[result.warm_index],'fro')/opt)
            fr=float(np.linalg.norm(A-F[result.selected_index],'fro')/opt)
            sr=float(np.linalg.norm(A-result.surrogate,'fro')/opt)
            warm_ratios.append(wr);final_ratios.append(fr);surrogate_ratios.append(sr)
            trials_rows.append(dict(case=case,trial=trial,warm_ratio=wr,final_ratio=fr,
                                   surrogate_ratio=sr,queries=result.oracle_calls,
                                   exceeds_requested_factor=fr>3+epsilon+1e-10))
        summaries.append(dict(case=case,n=len(A),M=len(F),s=s,k=k,ell=ell,trials=trials,
                              queries=s+k+ell,epsilon=epsilon,
                              theorem_sufficient_dimensions=False,
                              warm_above_requested_factor=sum(z>3+epsilon+1e-10 for z in warm_ratios),
                              returned_above_requested_factor=sum(z>3+epsilon+1e-10 for z in final_ratios),
                              max_warm_ratio=max(warm_ratios),max_returned_ratio=max(final_ratios),
                              max_surrogate_ratio=max(surrogate_ratios),
                              mean_returned_ratio=float(np.mean(final_ratios)),
                              all_query_audits_passed=True))
    with (OUT/'end_to_end_trials.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=trials_rows[0].keys());writer.writeheader();writer.writerows(trials_rows)
    return summaries


if __name__=='__main__':
    report={
        'notice':'Numerical audits are not a proof. Experimental sketch dimensions are below the explicit theorem dimensions.',
        'python':platform.python_version(),'numpy':np.__version__,'scipy':scipy.__version__,
        'seed':20260912,
        'flat_tail':flat_tail_audit(),
        'chernoff_algebra':chernoff_algebra_audit(),
        'pseudoinverse_moments':pseudoinverse_moment_audit(),
        'end_to_end':end_to_end_audit(),
        'proved_total_failure_upper_bound':math.exp(-8)+2*math.exp(-16)+1/128+1/524288,
    }
    (OUT/'verification_summary.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
