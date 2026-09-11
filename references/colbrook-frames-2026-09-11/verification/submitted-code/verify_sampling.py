#!/usr/bin/env python3
"""Finite checks for sampling_thresholds.tex (not a substitute for its proof).

Checks exact rational/integer rate certificates, affine-plane incidence counts,
the exact shared-character joint-type probability, and exhaustive support Gram
identities for small Walsh matrices. Optional Monte Carlo reports finite-size
RIP probabilities; those observations are not asymptotic certifications.

Requires Python 3.10+, numpy, scipy. Uses no network.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, factorial, log
from pathlib import Path
import json
import numpy as np


def kl(q: float, p: float) -> float:
    return q*log(q/p)+(1-q)*log((1-q)/(1-p))


def exact_rate_checks() -> dict:
    # For log((1+t)/(1-t)), truncation is a lower bound. The remainder after
    # index J is <= 2 t^(2J+3)/((2J+3)(1-t^2)).
    def log_bounds(t: F, J: int):
        lower = 2*sum((t**(2*j+1)/F(2*j+1) for j in range(J+1)), F(0))
        upper = lower+2*t**(2*J+3)/(F(2*J+3)*(1-t*t))
        return lower, upper
    assert log_bounds(F(3,11),0)[1] == F(345,616)
    assert log_bounds(F(1,7),1)[0] == F(296,1029)
    i3_upper = F(7,16)*F(345,616)-F(9,16)*F(296,1029)
    assert i3_upper == F(40191,482944) < F(1,12)
    assert log_bounds(F(1,5),0)[1] == F(73,180)
    assert log_bounds(F(1,11),0)[0] == F(2,11)
    i4_upper = F(3,8)*F(73,180)-F(5,8)*F(2,11)
    assert i4_upper == F(203,5280) < F(1,24)
    ratio3 = F(7**7*2**32, 3**3*5**20)
    ratio4 = F(2**24*3**42, 5**5*7**28)
    assert ratio3 > 1 and ratio4 > 1
    i2, i3, i4 = kl(.75,.5), kl(7/16,.25), kl(3/8,.25)
    j3, j4 = kl(5/8,.5), kl(7/12,.5)
    assert abs(16*(i3-2*j3)-log(float(ratio3))) < 1e-13
    assert abs(24*(i4-2*j4)-log(float(ratio4))) < 1e-13
    assert kl(1/8,1/4) > i4
    return {'I2':i2, 'I3':i3, 'I4':i4,
            'C2_per_d':log(2)/i2, 'C3_per_d':2*log(2)/i3,
            'C4_per_d':2*log(2)/i4,
            'I3_rational_upper':str(i3_upper), 'I4_rational_upper':str(i4_upper),
            'I3_minus_2J3':i3-2*j3, 'I4_minus_2J4':i4-2*j4,
            'full_Fourier_delta_one_third_constant':1/((4/3)*log(4/3)-1/3),
            'full_Walsh_delta_one_half_constant':1/(1.5*log(1.5)-.5)}


def plane_triples(N: int) -> np.ndarray:
    return np.asarray([(a,b,a^b) for a in range(1,N) for b in range(a+1,N)
                       if b < (a^b)], dtype=np.int64).reshape(-1,3)


def exact_incidence_checks() -> list:
    out=[]
    for d in range(2,8):
        N=2**d
        planes=plane_triples(N)
        assert len(planes)==(N-1)*(N-2)//6
        V=set(planes[0])
        count=sum(len(V.intersection(P))==1 for P in planes)
        assert count==3*(N//2-2)
        out.append({'d':d,'planes':len(planes),'shared_line_partners':count})
    return out


def exact_type_checks() -> dict:
    records=[]
    for m,k0 in [(6,3),(9,6),(12,6),(15,9),(18,9),(21,12)]:
        ell=(m-k0)//3
        assert k0+3*ell==m and k0!=ell
        k=k0+ell
        p=F(factorial(m), factorial(k0)*factorial(ell)**3*4**m)
        s=F(comb(m,k),2**m)
        joint=F(comb(m,k)*comb(k,k0)**2*comb(m-k,ell)**2,8**m)
        assert joint==p*p/s
        records.append({'m':m,'type':[k0,ell,ell,ell],
                        'p':str(p),'s':str(s),'joint':str(joint)})
    # Independently enumerate all 8^6 triples-of-bit row sequences.
    m=6
    ids=np.arange(8**m,dtype=np.int64)
    bits=np.stack([(ids//(8**j))%8 for j in range(m)],axis=1)
    x=bits&1; y=(bits>>1)&1; z=(bits>>2)&1
    xy=2*x+y; xz=2*x+z
    nxy=np.stack([(xy==j).sum(1) for j in range(4)],1)
    nxz=np.stack([(xz==j).sum(1) for j in range(4)],1)
    e1=(nxy==[3,1,1,1]).all(1)
    e2=(nxz==[3,1,1,1]).all(1)
    incompatible=(nxz==[1,1,3,1]).all(1)
    assert int((e1&e2).sum())==960
    assert not np.any(e1&incompatible)
    # Four independent bits give independent two-character row labels.
    labels=[((v&1)*2+((v>>1)&1),((v>>2)&1)*2+((v>>3)&1)) for v in range(16)]
    assert len(set(labels))==16
    return {'exact_probability_cases':records,
            'exhaustive_shared_bit_sequences':8**m,
            'compatible_count':960,'incompatible_count':0}


def walsh(N: int) -> np.ndarray:
    return np.asarray([[1-2*((a&v).bit_count()%2) for v in range(N)]
                       for a in range(N)],dtype=np.float64)


def fwht(x: np.ndarray) -> np.ndarray:
    out=np.array(x,dtype=np.float64,copy=True)
    h=1
    while h<len(out):
        block=out.reshape(-1,2*h)
        left=block[:,:h].copy(); right=block[:,h:].copy()
        block[:,:h]=left+right; block[:,h:]=left-right
        h*=2
    return out


def delta3_from_correlations(r: np.ndarray) -> float:
    P=plane_triples(len(r))
    G=np.tile(np.eye(3),(len(P),1,1))
    G[:,0,1]=G[:,1,0]=r[P[:,0]]
    G[:,0,2]=G[:,2,0]=r[P[:,1]]
    G[:,1,2]=G[:,2,1]=r[P[:,2]]
    return float(np.max(np.abs(np.linalg.eigvalsh(G)-1)))


def plane_delta4_from_correlations(r: np.ndarray) -> float:
    t=r[plane_triples(len(r))]
    signs=np.asarray([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]])
    return float(np.max(np.abs(t@signs.T)))


def exhaustive_gram_checks(seed: int) -> dict:
    rng=np.random.default_rng(seed)
    results=[]
    for d in [2,3,4]:
        N=2**d; W=walsh(N)
        assert np.array_equal(W.T@W,N*np.eye(N))
        for trial in range(4):
            m=11+3*trial
            rows=rng.integers(N,size=m)
            counts=np.bincount(rows,minlength=N)
            r=fwht(counts)/m
            G=(W[rows].T@W[rows])/m
            assert np.allclose(r,(counts@W)/m,atol=1e-14)
            exact3=max(float(np.max(np.abs(np.linalg.eigvalsh(G[np.ix_(S,S)])-1)))
                       for S in combinations(range(N),3))
            assert abs(exact3-delta3_from_correlations(r))<1e-12
            for P in plane_triples(N):
                S=[0,*P]
                vals=np.linalg.eigvalsh(G[np.ix_(S,S)])
                C=np.bincount(((W[rows,P[0]]<0).astype(int)*2+
                               (W[rows,P[1]]<0).astype(int)),minlength=4)
                assert np.allclose(np.sort(vals),np.sort(4*C/m),atol=1e-12)
            # Direct exhaustive delta4 versus the complete affine-rank split.
            exact4=0.; plane4=0.; rank3_4=0.
            for S in combinations(range(N),4):
                val=float(np.max(np.abs(np.linalg.eigvalsh(G[np.ix_(S,S)])-1)))
                exact4=max(exact4,val)
                if S[0]^S[1]^S[2]^S[3]==0: plane4=max(plane4,val)
                else: rank3_4=max(rank3_4,val)
            assert abs(plane4-plane_delta4_from_correlations(r))<1e-12
            assert abs(exact4-max(plane4,rank3_4))<1e-12
            results.append({'d':d,'m':m,'delta3':exact3,
                            'delta4_all_supports':exact4,'delta4_planes':plane4})
    # Check the moment-generating-function envelope on a fixed diagnostic grid.
    signs=np.asarray(list(product([-1,1],repeat=3)),dtype=float)
    worst=0.
    for _ in range(250):
        x=rng.normal(size=3);x/=np.linalg.norm(x)
        X=(signs@x)**2
        for t in [.001,.01,.1,.3,1.,3.]:
            ratio=np.mean(np.exp(t*X))/(np.exp(3*t)/4+3*np.exp(t/3)/4)
            worst=max(worst,float(ratio))
            assert ratio<=1+1e-12
    return {'support_checks':results,'sampled_mgf_largest_ratio':worst}


def monte_carlo(d: int, trials: int, seed: int, ratios: list[float]) -> list:
    rng=np.random.default_rng(seed);N=2**d;out=[]
    C=exact_rate_checks()
    for k in [3,4]:
        threshold=C[f'C{k}_per_d']*d
        for ratio in ratios:
            m=max(1,round(ratio*threshold));success=0
            for _ in range(trials):
                counts=np.bincount(rng.integers(N,size=m),minlength=N)
                r=fwht(counts)/m
                delta=(delta3_from_correlations(r) if k==3 else plane_delta4_from_correlations(r))
                success+=delta<=.5+1e-12
            out.append({'d':d,'k':k,'m':m,'threshold_ratio':ratio,
                        'trials':trials,'successes':success,
                        'event':('full delta_3 <= 1/2' if k==3 else
                                 'delta_4 restricted to affine-plane supports <= 1/2; NOT full RIP')})
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seed',type=int,default=0)
    parser.add_argument('--mc-d',type=int,default=0)
    parser.add_argument('--trials',type=int,default=20)
    parser.add_argument('--out',type=Path,default=Path(__file__).with_name('sampling_verification.json'))
    args=parser.parse_args()
    if not 0<=args.mc_d<=10 or args.trials<1: parser.error('Use 0<=mc-d<=10 and trials>=1.')
    report={'utc':datetime.now(timezone.utc).isoformat(),'seed':args.seed,
            'status':'Finite verification passed; analytic asymptotic proof is separate.',
            'rates':exact_rate_checks(),'incidence':exact_incidence_checks(),
            'types':exact_type_checks(),'grams':exhaustive_gram_checks(args.seed)}
    if args.mc_d:
        report['monte_carlo']=monte_carlo(args.mc_d,args.trials,args.seed,[.55,.7,.85,1.0,1.15])
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'rates':report['rates'],
                      'output':str(args.out)},indent=2))

if __name__=='__main__': main()
