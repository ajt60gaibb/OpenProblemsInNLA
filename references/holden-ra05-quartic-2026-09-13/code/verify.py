"""Reproducible finite checks for the unrestricted quartic proof.

Run from any directory: python code/verify.py.
Results go to generated_results/ unless --output-dir is supplied.
The packaged results/ directory is never overwritten by the default run.
The counts measure assertions, not independent proofs or asymptotic tests.
"""
from __future__ import annotations

if not __debug__:
    raise RuntimeError("Verification requires assertions: run Python without -O or PYTHONOPTIMIZE.")

import argparse
import json
from collections import Counter
from pathlib import Path
import numpy as np
from scipy.linalg import null_space
from quartic_features import (prepare, projector_query, exact_optimal_block,
    symmetric_power_rows, variance_pair, projected_series_atoms, invsqrt_positive)
from check_exact_certificate import check as exact_check
from exact_freezing import run as freezing_run

ROOT=Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output-dir', type=Path, default=ROOT/'generated_results',
                    help='Directory for this run; default leaves packaged results unchanged.')
args = parser.parse_args()
OUT = args.output_dir.resolve()
OUT.mkdir(parents=True, exist_ok=True)
rng=np.random.default_rng(20260913)
checks=Counter(); worst={}


def require(cat, condition, detail=''):
    checks[cat]+=1
    if not bool(condition): raise AssertionError(f'{cat}: {detail}')


def close(cat,a,b,atol=2e-8,rtol=2e-8):
    a,b=np.asarray(a),np.asarray(b)
    err=float(np.max(np.abs(a-b),initial=0))
    worst[cat]=max(worst.get(cat,0),err)
    require(cat,np.allclose(a,b,atol=atol,rtol=rtol),f'error {err}')


def leq(cat,A,B,tol=2e-8):
    A,B=np.asarray(A),np.asarray(B)
    if not A.size: require(cat,True); return
    eig=float(np.min(np.linalg.eigvalsh((B-A+(B-A).T)/2)))
    scale=max(float(np.linalg.norm(A,2)),float(np.linalg.norm(B,2)),1)
    require(cat,eig>=-tol*scale,f'min gap {eig}, scale {scale}')


def random_frame(k,bases,tail):
    u=np.vstack([np.linalg.qr(rng.normal(size=(k,k)))[0].T for _ in range(bases)])
    lam=np.full(len(u),1/bases)
    b=u*lam[:,None]**.25
    c=rng.normal(size=(len(u),tail))*np.exp(rng.normal(size=(len(u),1))*.4)
    c/=np.sum(np.sum(c*c,1)**2)**.25
    return prepare(b,c,u,lam)


def query(k,tail,rank,fractional=False):
    O=np.linalg.qr(rng.normal(size=(k+tail,rank)))[0]
    vals=rng.uniform(.05,1,size=rank) if fractional else np.ones(rank)
    return (O*vals)@O.T


def test_features(f,optimal=False):
    n,k=len(f.b),f.k
    close('normalization',f.pi.sum(),1)
    close('normalization',f.e.T@f.e,np.eye(f.D))
    close('normalization',f.t.sum(),f.h)
    close('normalization',np.sum(f.rho2**2),1)
    leq('normalization',f.g.T@f.g,np.eye(f.g.shape[1]))
    for arr,cap in [(f.lam,4*k),(f.tau,4*f.D),(f.t,4*max(1,f.h)),(f.rho2**2,4)]:
        require('density_ratios',np.max(arr/f.pi)<=cap+1e-7)
    for j in range(70):
        P=query(k,f.c.shape[1],1+j%k,j%3==0)
        theta=rng.normal(size=n)
        q=projector_query(f,P,theta)
        close('quartic_decomposition',q['sum'],q['direct'])
        close('query_contractions',np.linalg.norm(q['a'])**2,q['head_cost'])
        close('query_contractions',f.g@q['z'],q['cross'])
        require('query_contractions',np.linalg.norm(q['z'])**2<=q['mixed_quadratic_bound']+1e-7)
        require('query_contractions',q['mixed_quadratic_bound']<=np.sqrt(q['head_cost'])+1e-7)
        require('query_contractions',np.linalg.norm(q['p'])**2<=k+1e-7)
        require('query_contractions',q['p']@f.tail_regularizer@q['p']<=2+1e-7)
        require('query_contractions',q['head_cost']<=8*(q['cost']+1)+1e-7)
        if optimal:
            require('optimal_head_queries',q['cost']>=1-1e-7)
            require('optimal_head_queries',q['head_cost']<=16*q['cost']+1e-7)
            require('rounding_sensitivity',np.max(q['costs']/f.pi)<=544*k*k*q['cost']+1e-7)
        else:
            require('rounding_sensitivity',np.max(q['head_row_cost']/f.pi)<=4*k*k*q['head_cost']+1e-7)


examples=[]
for k,bases,tail in [(1,8,3),(2,5,3),(3,5,4),(4,5,3)]:
    f=random_frame(k,bases,tail); examples.append(f); test_features(f)
for k,N in [(1,3),(2,3),(3,4)]:
    f=prepare(*exact_optimal_block(k,N)); test_features(f,True)
# Nontrivial null range in N, but not in the head span.
b,c,u,lam=exact_optimal_block(3,4)
c[np.flatnonzero(u[:,0]==0)]=0
c/=np.sum(np.sum(c*c,axis=1)**2)**.25
f=prepare(b,c,u,lam)
require('singular_range',f.h==1)
test_features(f)
# Completely vanishing head/tail overlap: each row lies in exactly one block.
b=np.vstack([np.eye(2),np.zeros((3,2))]); c=np.vstack([np.zeros((2,3)),np.eye(3)/3**.25])
u=np.vstack([np.eye(2),np.zeros((3,2))]); lam=np.array([1,1,0,0,0.])
f=prepare(b,c,u,lam)
require('singular_range',f.h==0)
test_features(f)

variance_diagnostics=[]
for f in examples[1:3]:
    n,k,D=len(f.b),f.k,f.D
    eta=1/(8*n)
    indices=np.repeat(np.arange(n),np.floor(f.pi/eta).astype(int))
    X=f.atom_matrices(indices); m=len(indices)
    Ecur=eta*np.sum(X['E'],axis=0); Gcur=eta*np.sum(X['G'],axis=0); Tcur=eta*np.sum(X['T'],axis=0)
    leq('current_covariances',Ecur,np.eye(D))
    leq('current_covariances',Gcur,np.eye(Gcur.shape[0]))
    leq('current_covariances',Tcur,np.eye(Tcur.shape[0]))
    A1,B1=variance_pair(X['X1']); A2,B2=variance_pair(X['X2']); A4,B4=variance_pair(X['X4'])
    leq('variance_table',A1,4*k/eta*np.eye(D))
    leq('variance_table',A2,4/eta*np.eye(D))
    leq('variance_table',A4,4/eta*np.eye(A4.shape[0]))
    require('variance_table',np.trace(B1)<=4*k*D/eta+1e-6)
    require('variance_table',np.trace(B2)<=4*D/eta+1e-6)
    for label,cap in [('E',4*D/eta),('G',4*k/eta),('T',4*k/eta)]:
        a,b=variance_pair(X[label]); leq('variance_table',a,cap*np.eye(len(a))); close('variance_table',a,b)
    require('variance_table',np.sum(X['v40']**2)<=4*k/eta+1e-7)
    require('variance_table',np.sum(X['tail_linear']**2)<=4/eta+1e-7)
    # Fixed-matrix anisotropic whitening: this checks deterministic variances.
    R4=B4+4/eta*np.eye(len(B4)); iR4=invsqrt_positive(R4)
    Y=np.einsum('nij,jk->nik',X['X4'],iR4)
    aa,bb=variance_pair(Y)
    leq('anisotropic_whitening',aa,np.eye(len(aa)))
    leq('anisotropic_whitening',bb,np.eye(len(bb)))
    for _ in range(60):
        P=query(k,f.c.shape[1],k,True)
        p=P[k:,k:].reshape(-1)
        require('anisotropic_query_bound',p@B4@p<=4*k/eta+1e-6)
        require('anisotropic_query_bound',p@R4@p<=8*k/eta+1e-6)
    q=1
    U1=np.linalg.eigh(B1)[1][:,-q:]; U2=np.linalg.eigh(B2)[1][:,-q:]
    J1=np.eye(len(B1))-U1@U1.T; J2=np.eye(len(B2))-U2@U2.T
    for B,J in [(B1,J1),(B2,J2)]:
        require('protected_variance',np.linalg.norm(J@B@J,2)<=np.trace(B)/(q+1)+1e-6)
    # Exact moment constraints at this finite size plus protected right modes.
    ids=indices
    constraints=[np.ones((1,m)),
        (f.rho2[ids]**2/f.pi[ids])[None,:],(f.t[ids]/f.pi[ids])[None,:],
        (f.e[ids]*f.rho2[ids,None]/f.pi[ids,None]).T,
        np.einsum('nij,jk->nik',X['X1'],U1).reshape(m,-1).T,
        np.einsum('nij,jk->nik',X['X2'],U2).reshape(m,-1).T]
    # Protect two leading head-feature modes.
    hv,hU=np.linalg.eigh(X['head'].T@X['head']); HU=hU[:,-2:]
    constraints.append((X['head']@HU).T)
    constraints=np.vstack(constraints)
    F=null_space(constraints,rcond=1e-11)
    require('coefficient_projection',F.shape[1]>0)
    close('coefficient_projection',F.T@F,np.eye(F.shape[1]))
    close('protected_constraints',constraints@F,np.zeros((constraints.shape[0],F.shape[1])),atol=5e-7)
    for label in ['X1','X2','X4','E','G','T']:
        YY=projected_series_atoms(X[label],F)
        A,B=variance_pair(X[label]); Ap,Bp=variance_pair(YY)
        leq('projected_variance_contraction',Ap,A)
        leq('projected_variance_contraction',Bp,B)
    for _ in range(20):
        xi=F@rng.normal(size=F.shape[1])
        Z1=np.einsum('n,nij->ij',xi,X['X1']); Z2=np.einsum('n,nij->ij',xi,X['X2'])
        close('protected_constraints',Z1@U1,np.zeros((D,q)),atol=2e-6)
        close('protected_constraints',Z2@U2,np.zeros((D,q)),atol=2e-6)
    Hcov=X['head'].T@F@F.T@X['head']
    require('head_covariance_truncation',np.linalg.norm(Hcov,2)<=np.trace(X['head'].T@X['head'])/3+1e-6)
    variance_diagnostics.append({'k':k,'head_tensor_rank':D,'tail_dimension':f.c.shape[1],
                                'copies':m,'constraint_rank':m-F.shape[1],
                                'coefficient_subspace_dimension':F.shape[1],
                                'maximum_density_ratios':{'Lewis':float(np.max(f.lam/f.pi)),
                                'head_leverage':float(np.max(f.tau/f.pi)),
                                'mixed_leverage':float(np.max(f.t/f.pi)),
                                'tail_mass':float(np.max(f.rho2**2/f.pi))}})

# Density-independent regime identity and monotonicity checks.
for k in [1,2,3,5,16,64,256]:
    for eps in np.geomspace(1e-8,.49,150):
        a=k*k/eps**2; b=k**2.5/eps; c=k**4; d=k/eps**2
        old=max(min(a,b,c),d); new=min(a,b+d)
        require('three_regime_equivalence',old<=new*(1+1e-12) and new<=2*old*(1+1e-12))

# Exact full-rank block witness.
k,N,R=2,3,2; ambient=k+k*N; rows=[]; weights=[]
for j in range(k):
    for t in range(N):
        for sign in (1,-1):
            row=[0]*ambient; row[j]=R; row[k+j*N+t]=sign; rows.append(row); weights.append(2 if sign==1 else 0)
queries=[]
for sign,label,wcost in [(1,'positive tilt','648/25'),(-1,'negative tilt','1672/25')]:
    Z=np.zeros((ambient,ambient),dtype=int)
    for j in range(k):
        v=np.zeros(ambient,dtype=int); v[j]=2; v[k+j*N]=sign; Z+=np.outer(v,v)
    queries.append({'label':label,'denominator':5,'projector_numerator':Z.tolist(),
                    'original_cost':'232/5','weighted_cost':wcost,'relative_error':'64/145'})
cert={'k':k,'N':N,'R':R,'rows':rows,'weights':weights,'epsilon':'1/10','optimal_cost':'12','queries':queries}
(OUT/'exact_full_rank_certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
checked=exact_check(OUT/'exact_full_rank_certificate.json')
require('exact_full_rank_certificate',checked['passed'])
(OUT/'exact_full_rank_certificate_check.json').write_text(json.dumps(checked,indent=2)+'\n')

# Exact positive fractional-exception bookkeeping on a rank-three input.
rr=np.random.default_rng(909)
rows=[]
while len(rows)<38:
    row=rr.integers(-3,4,size=3).tolist()
    if any(row) and row not in rows and [-v for v in row] not in rows: rows.append(row)
fr=freezing_run(rows)
require('exact_fractional_freezing',fr['exact_all_quartic_moments'])
require('exact_fractional_freezing',fr['retained_rows']<fr['original_rows'])
require('exact_fractional_freezing',np.linalg.matrix_rank(np.asarray(rows,float))==3)
for stage in fr['stages']:
    require('exact_fractional_freezing',stage['full_positive']<=stage['copies_before']//2)
    require('exact_fractional_freezing',stage['fractional_frozen']<=fr['moment_count_including_mass'])
(OUT/'exact_fractional_freezing.json').write_text(json.dumps(fr,indent=2)+'\n')

result={'passed':True,'seed':20260913,'total_assertions':sum(checks.values()),'categories':dict(checks),
        'maximum_recorded_absolute_residuals':worst,'variance_instances':variance_diagnostics,
        'exact_block_witness':checked,
        'freezing_summary':{key:fr[key] for key in ['original_rows','retained_rows','dimension','stages']},
        'limitations':['These finite assertions are not independent mathematical proofs.',
        'The Rothvoss and matrix-Gaussian theorems are imported, not validated by numerical sampling.',
        'The exact freezing demo uses full quartic moments, not the asymptotic small-discrepancy oracle.',
        'Generic random head/tail tests check identities and estimates that do not require head optimality.',
        'Only the structured sign-pair block inputs have a proved optimal head in these tests.']}
(OUT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
