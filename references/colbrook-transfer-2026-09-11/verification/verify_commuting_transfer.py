"""Seeded diagnostics for the commuting finite-Schatten-p extension."""
from pathlib import Path
import json
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
rng=np.random.default_rng(20260912)
count=0;minimum=float('inf')
for n in [3,5,10,25]:
    for trial in range(1000):
        k=int(rng.integers(1,n));p=float(rng.choice([1,1.25,1.5,2,3,4,8]))
        a=np.sort(10**rng.uniform(-3,3,n))[::-1]
        S=rng.choice(n,k,replace=False);b=10**rng.uniform(-4,4,k)
        if trial%7==0:b[0]=0
        if trial%3==0:
            exponent=float(rng.uniform(.01,.99))
            f=lambda x: np.asarray(x)**exponent
        elif trial%3==1:
            scale=10**rng.uniform(-3,3)
            offset=float(rng.choice([0.,.1,1.]))
            f=lambda x: np.minimum(np.asarray(x),scale)+offset
        else:
            exponent=float(rng.uniform(.15,.85));freq=4.
            amplitude=.9*min(exponent,1-exponent)/freq
            def f(x):
                x=np.asarray(x);safe=np.maximum(x,1e-300)
                return np.where(x>0,safe**exponent*np.exp(amplitude*np.sin(freq*np.log(safe))),0.)
        tau=a[k];c=float(f(tau)/tau)
        LA=float(sum(a[:k]**p)-sum(a[S]**p));RA=float(sum(abs(a[S]-b)**p))
        LF=float(sum(f(a[:k])**p)-sum(f(a[S])**p));RF=float(sum(abs(f(a[S])-f(b))**p))
        lhs=LF+RF;rhs=2*c**p*(LA+RA)
        margin=(rhs-lhs)/(1+abs(rhs)+abs(lhs))
        assert margin>=-2e-12
        scalar=abs(f(a[S])-f(b))**p
        bound=c**p*(abs(a[S]-b)**p+np.maximum(tau**p-a[S]**p,0))
        assert np.all(scalar<=bound+2e-12*(1+abs(bound)))
        minimum=min(minimum,margin);count+=1
result={'status':'PASS','seed':20260912,'cases':count,'p_values':[1,1.25,1.5,2,3,4,8],
        'minimum_normalized_margin':minimum,
        'scope':'Common eigenbasis with a specified k-dimensional truncation; not the general noncommuting nuclear problem.'}
(ROOT/'results'/'commuting_transfer_verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
