"""Adversarial numerical checks for the scalar lemma and matrix transfer theorem."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
import sympy as sp

ROOT=Path(__file__).resolve().parents[1]
rng=np.random.default_rng(112609)
d,z=sp.symbols('d z', positive=True)
polynomial=2*(d+1)*z*z-(2*d+1)*z+d
assert sp.simplify(sp.discriminant(polynomial,z) - (1-4*d*(d+1))) == 0
# Check each algebraic factorization used in the proof.
low=2*d*d*z-2*z-d*d+1-d*(d-1)*(1-1/z)
mid=2*d*d-2*z-d*d+1-d*(d-1)*(1-1/z)
high=2*d*z-2*z-d*d+1-d*(d-1)*(1-1/z)
assert sp.simplify(low-(d-1)*polynomial/z)==0
assert sp.simplify(mid-(d-z)*(2*z+d-1)/z)==0
assert sp.simplify(high-(d-1)*(z-d)*(2*z-1)/z)==0

# Nonnegative mixtures of caps, plus a linear term and a positive intercept,
# generate a broad collection of nonsmooth non-operator-monotone concave maps.
def random_function():
    knots=10**rng.uniform(-4,4,6)
    weights=10**rng.uniform(-3,2,6)
    slope=float(10**rng.uniform(-4,0))
    intercept=float(10**rng.uniform(-5,2)) if rng.random()<.5 else 0.
    def f(x):
        x=np.asarray(x)
        return intercept+slope*x+np.sum(weights*np.minimum(x[...,None],knots),axis=-1)
    return f

scalar_min=1.0
scalar_tests=0
for _ in range(100):
    f=random_function()
    a,b,tau=10**rng.uniform(-5,5,(3,2000))
    c=f(tau)/tau
    fa,fb=f(a),f(b)
    h=np.maximum(c*c*a*a-fa*fa,0)
    lhs=h+2*fb*fa-2*c*c*b*a-fb*fb+c*c*b*b
    rhs=fb*np.maximum(fb-c*b,0)*(1-b/a)
    scale=1+np.abs(h)+2*np.abs(fb*fa)+2*np.abs(c*c*b*a)+fb*fb+c*c*b*b+np.abs(rhs)
    relative=(lhs-rhs)/scale
    assert np.min(relative)>-1e-12, (a[np.argmin(relative)],b[np.argmin(relative)],np.min(relative))
    scalar_min=min(scalar_min,float(np.min(relative)))
    scalar_tests+=len(a)

matrix_min=1.0
max_relative_transfer=0.0
matrix_tests=0
for n in [2,3,4,6,9,12]:
    for trial in range(700):
        a=np.sort(10**rng.uniform(-3,3,n))[::-1]
        A=np.diag(a)
        sqrtA=np.diag(np.sqrt(a))
        Q,_=np.linalg.qr(rng.standard_normal((n,n)))
        contractions=rng.uniform(0,1,n)
        if trial%3==0:
            contractions=1-10**rng.uniform(-9,-1,n)
            # Near-diagonal candidates make relative error close to one.
            X=np.eye(n)+10**rng.uniform(-8,-1)*rng.standard_normal((n,n))
            Q,_=np.linalg.qr(X)
        Ahat=sqrtA@Q@np.diag(contractions)@Q.T@sqrtA
        vals,vecs=np.linalg.eigh(Ahat)
        order=np.argsort(vals)[::-1]
        vals=np.maximum(vals[order],0);vecs=vecs[:,order]
        k=1+trial%(n-1)
        b=vals[:k];v=vecs[:,:k]
        B=(v*b)@v.T
        f=random_function()
        fA=np.diag(f(a)); C=(v*f(b))@v.T
        tau=a[k];c=float(f(tau)/tau)
        tailA=float(np.sum(a[k:]**2));tailf=float(np.sum(f(a[k:])**2))
        errA=float(np.linalg.norm(A-B)**2);errf=float(np.linalg.norm(fA-C)**2)
        left=errf-tailf;right=c*c*(errA-tailA)
        scale=1+abs(errf)+abs(tailf)+abs(c*c*errA)+abs(c*c*tailA)
        margin=(right-left)/scale
        assert margin>=-2e-12, (n,k,trial,margin)
        matrix_min=min(matrix_min,margin)
        max_relative_transfer=max(max_relative_transfer,(errf/tailf)/(errA/tailA))
        matrix_tests+=1

result={'seed':112609,'symbolic_factorizations':'passed','scalar_tests':scalar_tests,
        'minimum_scaled_scalar_margin':scalar_min,'matrix_tests':matrix_tests,
        'minimum_scaled_matrix_margin':matrix_min,
        'maximum_output_to_input_squared_relative_error_ratio':max_relative_transfer,
        'all_passed':True,
        'caveat':'Numerical checks do not replace the mathematical proof.'}
(ROOT/'results'/'frobenius_transfer_verification.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
