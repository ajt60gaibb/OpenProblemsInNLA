"""Audit the constant-success closed-convex extension on coefficient boxes."""
from pathlib import Path
import json
import numpy as np
from scipy.optimize import lsq_linear
from linear_family_sketch import make_plan,median_radius_index
ROOT=Path(__file__).resolve().parents[1]
rng=np.random.default_rng(20260913)
records=[];worst=0.;tested=0
for trial in range(600):
    q,m,n=6,9,8
    raw=rng.standard_normal((q,m,n))
    plan=make_plan(raw,seed=trial,practical_rank=trial%3,practical_samples=30)
    p,u,g=plan.basis,plan.left,plan.right
    theta=rng.uniform(-2,2,q)
    Bstar=np.einsum('i,imn->mn',np.clip(theta,-1,1),p)
    R=rng.standard_normal((m,n))
    R-=np.einsum('i,imn->mn',np.einsum('imn,mn->i',p,R),p)
    R/=np.linalg.norm(R)
    A=np.einsum('i,imn->mn',theta,p)+R
    E=A-Bstar
    exact=np.einsum('mr,imn->irn',u,p)
    residual=p-np.einsum('mr,irn->imn',u,exact)
    random=np.einsum('imn,ns->ims',residual,g)/np.sqrt(g.shape[1])
    design=np.concatenate([exact.reshape(q,-1),random.reshape(q,-1)],axis=1).T
    response=np.concatenate([(u.T@A).reshape(-1),((A-u@(u.T@A))@g/np.sqrt(g.shape[1])).reshape(-1)])
    fit=lsq_linear(design,response,bounds=(-1,1),method='bvls',tol=1e-13,max_iter=300)
    assert fit.success
    cstar=np.clip(theta,-1,1);d=fit.x-cstar
    Gram=design.T@design
    mineig=float(np.linalg.eigvalsh(Gram)[0])
    r=design.T@(response-design@cstar)
    e=np.einsum('imn,mn->i',p,E)
    z=r-e
    delta=float(np.dot(d,d)-2*np.dot(e,d))
    assert np.dot(e,d)<=2e-12
    assert d@Gram@d<=(e+z)@d+1e-10
    if mineig>=.5:
        bound=float(4*np.dot(z,z))
        assert delta<=bound+2e-10
        ratio=delta/bound if bound>1e-18 else 0.
        worst=max(worst,ratio);tested+=1
    if trial<12:
        records.append({'trial':trial,'minimum_gram_eigenvalue':mineig,'true_excess':delta,
                        'four_times_centered_noise_squared':float(4*np.dot(z,z))})
# Deterministic guarantee for the linear-family confidence selector.
for trial in range(500):
    L=11;dimension=8;truth=rng.standard_normal(dimension)
    good=rng.standard_normal((6,dimension));good/=np.maximum(np.linalg.norm(good,axis=1)[:,None],1)
    candidates=np.concatenate([truth+good,truth+10**rng.uniform(-1,3)*rng.standard_normal((5,dimension))])
    rng.shuffle(candidates)
    chosen=candidates[median_radius_index(candidates)]
    assert np.linalg.norm(chosen-truth)<=3+1e-12
result={'status':'PASS','seed':20260913,'convex_box_cases':600,'gram_good_cases':tested,
        'maximum_ratio_excess_to_four_noise_squared':worst,'illustrative_records':records,
        'linear_median_selector_majority_tests':500,
        'scope':'The convex extension is constant-success only; linear confidence amplification is tested separately.'}
(ROOT/'results'/'convex_family_verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='illustrative_records'},indent=2))
