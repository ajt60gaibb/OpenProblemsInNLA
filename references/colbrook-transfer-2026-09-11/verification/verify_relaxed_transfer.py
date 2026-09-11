"""Numerical and symbolic audits of the sharp unordered Frobenius factor two.

The mathematical proof is in the manuscript. These tests are independently
reproducible diagnostics, not proof certificates for universally quantified claims.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
rng = np.random.default_rng(112610)

# Two endpoint identities in the only nontrivial scalar case.
a, b = sp.symbols('a b', real=True)
assert sp.expand((2*a*b-b*b) - (a*a-(a-b)**2)) == 0
assert sp.expand((-a*a-2*b*b+4*a*b) - (a*a-2*(a-b)**2)) == 0

def make_function(kind: int):
    if kind % 4 == 0:
        knots = 10.0**rng.uniform(-4, 4, 6)
        weights = 10.0**rng.uniform(-3, 2, 6)
        slope = 10.0**rng.uniform(-4, 0)
        intercept = 10.0**rng.uniform(-5, 2) if rng.random() < .5 else 0.
        def f(x):
            x = np.asarray(x)
            return intercept + slope*x + np.sum(weights*np.minimum(x[..., None], knots), axis=-1)
        return f, 'concave cap mixture'
    if kind % 4 == 1:
        p = rng.uniform(.005, .995)
        return lambda x: np.asarray(x)**p, 'operator-monotone power'
    if kind % 4 == 2:
        # Nonconcave maps in the larger monotone/subhomogeneous class.
        # d log f / d log x = p + alpha*omega*cos(omega*log x) lies in [0,1].
        p = rng.uniform(.15, .85)
        omega = rng.uniform(5., 60.)
        alpha = .95*min(p, 1-p)/omega
        def f(x):
            x = np.asarray(x)
            positive = np.maximum(x, np.finfo(float).tiny)
            out = positive**p * np.exp(alpha*np.sin(omega*np.log(positive)))
            return np.where(x > 0, out, 0.)
        return f, 'nonconcave monotone subhomogeneous'
    value = 10.0**rng.uniform(-3, 3)
    return lambda x: np.full_like(np.asarray(x), value, dtype=float), 'positive constant'

scalar_tests = 0
scalar_margin = 1.
for trial in range(160):
    f, _ = make_function(trial)
    a, b, tau = 10.0**rng.uniform(-5, 5, (3, 2000))
    c = f(tau)/tau
    fa, fb = f(a), f(b)
    left = fb**2 - 2*fb*fa - 2*c*c*b*b + 4*c*c*a*b
    right = np.maximum(2*c*c*a*a-fa*fa, f(tau)**2)
    scale = 1+fb**2+2*np.abs(fb*fa)+2*c*c*b*b+4*c*c*a*b+np.abs(right)
    margin = (right-left)/scale
    assert np.min(margin) >= -1e-12
    scalar_margin = min(scalar_margin, float(np.min(margin)))
    scalar_tests += a.size

matrix_tests = 0
matrix_margin = 1.
ordered_extra_tests = 0
ordered_margin = 1.
for n in [2, 3, 4, 6, 9, 12]:
    for trial in range(800):
        a = np.sort(10.0**rng.uniform(-3, 3, n))[::-1]
        A = np.diag(a)
        k = 1 + trial % (n-1)
        V, _ = np.linalg.qr(rng.standard_normal((n, k)))
        b = 10.0**rng.uniform(-3, 3, k)
        if trial % 4 == 0:
            # Near-optimal, arbitrarily oriented perturbations of a truncation.
            V, _ = np.linalg.qr(np.eye(n, k)+10.0**rng.uniform(-7, -.5)*rng.standard_normal((n,k)))
            b = a[:k] * (1+10.0**rng.uniform(-7, -.5)*rng.standard_normal(k))
            b = np.maximum(b, 0.)
        f, _ = make_function(trial)
        B = (V*b)@V.T
        C = (V*f(b))@V.T
        fA = np.diag(f(a))
        tau = a[k]
        c = f(tau)/tau
        ta = np.sum(a[k:]**2)
        tf = np.sum(f(a[k:])**2)
        ea = np.linalg.norm(A-B)**2
        ef = np.linalg.norm(fA-C)**2
        margin = (2*c*c*(ea-ta)-(ef-tf))/(1+2*c*c*(ea+ta)+ef+tf)
        assert margin >= -2e-12, (n, k, trial, margin)
        matrix_margin = min(matrix_margin, float(margin))
        matrix_tests += 1
        if trial % 4 == 2:
            # Independently audit the larger function class for the ordered theorem.
            Q, _ = np.linalg.qr(rng.standard_normal((n, n)))
            Ah = (np.sqrt(a)[:,None]*Q)@np.diag(rng.uniform(0,1,n))@(Q.T*np.sqrt(a)[None,:])
            bv, U = np.linalg.eigh(Ah)
            V = U[:,-k:]; b = np.maximum(bv[-k:],0.)
            B = (V*b)@V.T; C = (V*f(b))@V.T
            ea = np.linalg.norm(A-B)**2; ef = np.linalg.norm(fA-C)**2
            margin = (c*c*(ea-ta)-(ef-tf))/(1+c*c*(ea+ta)+ef+tf)
            assert margin >= -2e-12
            ordered_margin = min(ordered_margin,float(margin))
            ordered_extra_tests += 1

sharpness = []
for L in [10, 100, 1000, 10000]:
    # A has N+1 unit eigenvalues and one zero; no large matrix needs allocation.
    N = L
    logb = -float(L)
    p = 1./L**2
    b2 = np.exp(2*logb)
    b2p = np.exp(2*p*logb)
    # Stable evaluation of sqrt(1+x)-1.
    def excess(x):
        return x/(np.sqrt(1+x)+1)
    norm_ratio = excess((1+b2p)/N)/excess((1+b2)/N)
    sharpness.append({'L':L, 'squared_excess_ratio':float((1+b2p)/(1+b2)),
                      'norm_relative_excess_ratio':float(norm_ratio)})
assert sharpness[-1]['norm_relative_excess_ratio'] > 1.999

result = {'seed':112610, 'symbolic_identities':'passed',
          'scalar_tests':scalar_tests,'minimum_scaled_scalar_margin':scalar_margin,
          'unordered_matrix_tests':matrix_tests,'minimum_scaled_matrix_margin':matrix_margin,
          'additional_ordered_nonconcave_tests':ordered_extra_tests,
          'minimum_scaled_additional_ordered_margin':ordered_margin,
          'sharpness_examples':sharpness,'all_passed':True,
          'caveat':'Numerical tests are diagnostics; the universal claims require the manuscript proofs.'}
(ROOT/'results'/'relaxed_transfer_verification.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
