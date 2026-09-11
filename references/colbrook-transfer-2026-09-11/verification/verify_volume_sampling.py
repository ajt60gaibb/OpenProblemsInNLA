"""Exact and numerical diagnostics for volume-sampling convexity.

Run from any working directory. The proof is in manuscript 01; these tests
verify its algebra and examples, not the universal quantifier by sampling.
"""
from __future__ import annotations
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import json
import math
import numpy as np
import scipy.optimize as opt
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]

def elementary(values: list[Fraction]) -> list[Fraction]:
    e = [Fraction(1)] + [Fraction(0)] * len(values)
    for i, value in enumerate(values):
        for j in range(i + 1, 0, -1):
            e[j] += value * e[j - 1]
    return e

def main() -> None:
    rng = np.random.default_rng(20260911)
    s1, s2, s3 = sp.symbols('s1 s2 s3', positive=True)
    difference = s1 - 2*(s1*s1-s2)/s1 + (s1**3-3*s1*s2+2*s3)/(s1*s1-s2)
    certificate = 2*(s1*s3-s2*s2)/(s1*(s1*s1-s2))
    assert sp.cancel(difference-certificate) == 0
    m = sp.symbols('m0:5', positive=True)
    assert sp.expand(sum(m)*sum(x**3 for x in m)-sum(x*x for x in m)**2
                     -sum(m[i]*m[j]*(m[i]-m[j])**2 for i in range(5) for j in range(i+1,5))) == 0
    exact_cases = 0
    for n in range(1, 17):
        for trial in range(80):
            lam = [Fraction(int(rng.integers(1, 101)), int(rng.integers(1, 101))) for _ in range(n)]
            if trial % 16 == 0:
                lam = [Fraction(7, 3)]*n
            e = elementary(lam)
            F = [(j+1)*e[j+1]/e[j] for j in range(n)] + [Fraction(0)]
            assert all(F[j] > F[j+1] for j in range(n))
            assert all(F[j-1]-2*F[j]+F[j+1] >= 0 for j in range(1,n))
            if trial % 16 == 0:
                assert all(F[j] == (n-j)*lam[0] for j in range(n+1))
            exact_cases += 1

    # Explicit enumeration of determinantal probabilities and projection errors.
    dpp_cases = 0
    max_relative_identity_error = 0.0
    for n in range(2, 9):
        for trial in range(12):
            A = rng.standard_normal((n+2,n))
            if trial % 4 == 0 and n >= 3:
                A[:,-1] = A[:,0] + A[:,1]
            G = A.T@A
            lam = np.linalg.eigvalsh(G)
            rank = np.linalg.matrix_rank(A)
            alpha = 10.0**rng.uniform(-1,1)
            z = np.linalg.det(np.eye(n)+G/alpha)
            prob_sum = mean_k = mean_err = 0.0
            numer = np.zeros(rank+1); denom = np.zeros(rank+1)
            for k in range(rank+1):
                for S in combinations(range(n),k):
                    det = 1.0 if k == 0 else max(0.0,float(np.linalg.det(G[np.ix_(S,S)])))
                    if det < 1e-13 and k:
                        continue
                    if k:
                        AS = A[:,S]
                        residual = A-AS@np.linalg.lstsq(AS,A,rcond=None)[0]
                    else:
                        residual = A
                    err = float(np.linalg.norm(residual,'fro')**2)
                    p = det/alpha**k/z
                    prob_sum += p; mean_k += k*p; mean_err += err*p
                    denom[k] += det; numer[k] += det*err
            mu = float(np.sum(lam/(lam+alpha)))
            assert abs(prob_sum-1) < 2e-9
            assert abs(mean_k-mu) < 2e-9*(1+mu)
            assert abs(mean_err-alpha*mu) < 2e-8*(1+mean_err)
            for k in range(rank):
                fixed = numer[k]/denom[k]
                formula = (k+1)*denom[k+1]/denom[k]
                rel = abs(fixed-formula)/(1+abs(formula))
                max_relative_identity_error=max(max_relative_identity_error,rel)
                assert rel < 2e-8
            dpp_cases += 1

    bound_cases=0; minimum_bound_margin=math.inf
    for n in range(3,25):
        for trial in range(30):
            lam=np.sort(np.exp(rng.uniform(-3,3,n)))[::-1]
            # Coefficients in extended precision avoid unnecessary overflow.
            e=np.zeros(n+1,dtype=np.longdouble);e[0]=1
            for value in lam:
                for j in range(n,0,-1): e[j]+=value*e[j-1]
            for k in range(1,n):
                F=float((k+1)*e[k+1]/e[k]); tail=float(sum(lam[k:]))
                root=opt.brentq(lambda x: float(sum(lam/(lam+x)))-k,
                               1e-15, float(sum(lam))*2,xtol=1e-13)
                assert F <= root*k+2e-9*(1+F)
                for s in range(k):
                    ell=k-s;beta=lam[s]
                    sharp=k/(2*ell)*(1+np.sqrt(1+4*ell*beta/tail))
                    margin=sharp-F/tail
                    minimum_bound_margin=min(minimum_bound_margin,float(margin))
                    assert margin>=-2e-10*(1+sharp)
                    rs=float(sum(lam[s:])/beta);ts=s+rs
                    if k<ts:
                        psi=k/(2*ell)*(1+np.sqrt(1+4*ell/(ts-k)))
                        phi=k/ell*np.sqrt(1+2*ell/(ts-k))
                        assert sharp<=psi+1e-9*(1+psi)
                        assert psi<=phi+1e-9*(1+phi)
                    bound_cases+=1
    result={
        'status':'PASS', 'seed':20260911,
        'symbolic_second_difference_identity':True,
        'symbolic_pairwise_sum_identity':True,
        'exact_rational_spectra':exact_cases,
        'enumerated_dpp_matrices':dpp_cases,
        'maximum_dpp_identity_relative_error':max_relative_identity_error,
        'stable_rank_and_spectral_bound_checks':bound_cases,
        'minimum_sharp_bound_margin':minimum_bound_margin,
        'interpretation':'Diagnostics supplement the exact proof; random tests are not a proof.'
    }
    (ROOT/'results'/'volume_sampling_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
