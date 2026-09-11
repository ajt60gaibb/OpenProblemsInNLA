#!/usr/bin/env python3
"""Exact algebra checks and reproducible numerical diagnostics for round three.

These tests are not an independent proof, a formal verification, or a numerical
certification of the stated probability bound.  They exercise identities and
models used in the accompanying two manuscripts.
"""
from __future__ import annotations

import os
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")

import argparse
import json
import platform
from pathlib import Path

import numpy as np
import scipy
import scipy.linalg as la
from scipy.optimize import linear_sum_assignment
import sympy as sp

from odd_family import make_family, dense_matrix, spectral_summary

SEED = 401110


def match(reference: np.ndarray, candidate: np.ndarray) -> np.ndarray:
    rows, cols = linear_sum_assignment(np.abs(reference[:, None] - candidate[None, :]))
    out = np.empty_like(cols)
    out[rows] = cols
    return out


def pencil(z: np.ndarray, w: np.ndarray, k: int):
    S = z[:, None] ** np.arange(k)[None, :]
    G = S.conj().T @ (w[:, None] * S)
    F = S.conj().T @ ((w * z)[:, None] * S)
    return S, G, F


def exact_checks() -> dict[str, object]:
    t, z, x, y = sp.symbols("t z x y", real=True)
    G = sp.Matrix([[t + 2, t - 1], [t - 1, t + 2]])
    F = sp.Matrix([[t - 1, t - 1], [t + 2, t - 1]])
    p = sp.factor((z * G - F).det())
    target = 3 * ((2 * t + 1) * z**2 + (1 - t) * z + (1 - t))
    assert sp.expand(p - target) == 0
    disc = sp.factor(sp.discriminant(p, z))
    assert sp.expand(disc - 81 * (t - 1) * (t + sp.Rational(1, 3))) == 0
    p0, p1 = z*z + z + 1, 2*z*z - z - 1
    q = sp.expand(sp.im(p0.subs(z, x + sp.I*y) * sp.conjugate(p1.subs(z, x + sp.I*y))))
    assert sp.expand(q + 3*y*(x*x + 2*x + y*y)) == 0
    d, u = sp.symbols("d u")
    parabola_identity = sp.expand((2*d*u)**2-d*(1+d*u*u)**2+d*(1-d*u*u)**2)
    assert parabola_identity == 0
    assert 11**2 > 9*13
    assert 210**2 < 2*151**2
    assert sp.Rational(2, 361) + sp.Rational(3, 19) == sp.Rational(59, 361)
    return {"status": "passed", "pencil_determinant": str(p),
            "discriminant": str(disc), "root_locus_polynomial": str(sp.factor(q)),
            "threshold_square_comparison": [210**2, 2*151**2],
            "parabola_norm_polynomial_residual": str(parabola_identity),
            "positivity_threshold_comparison": [11**2, 9*13]}


def krylov_checks() -> dict[str, object]:
    rng = np.random.default_rng(SEED)
    counts = {"matrices": 0, "eigenpairs": 0, "physical_model_comparisons": 0,
              "finite_difference_eigenpairs": 0, "complex_pencil_tests": 0}
    maxima = dict(equal_modulus=0., sensitivity_identity=0., balanced_frobenius=0.,
                  balanced_condition_ratio=0., deterministic_bound_ratio=0.,
                  physical_model_error=0., finite_difference_relative_error=0.,
                  complex_pencil_max_radius=0.)
    for n in [3, 4, 5, 7, 10, 20, 40, 80]:
        z = np.exp(-2j * np.pi * np.arange(n) / n)
        d = 2*np.sin(np.pi/n)
        for k in sorted({2, max(2, n//2), n-1}):
            for rep in range(10):
                w = rng.exponential(size=n)
                S, G, F = pencil(z, w, k)
                ev, L, R = la.eig(F, G, left=True, right=True)
                derivatives = np.empty((k, n), dtype=complex)
                for i in range(k):
                    r, ell = S @ R[:, i], S @ L[:, i]
                    r /= np.sqrt(np.sum(w*np.abs(r)**2))
                    ell /= np.sqrt(np.sum(w*np.abs(ell)**2))
                    alpha = np.sum(w*ell.conj()*r)
                    kap = 1/abs(alpha)
                    deriv = (z-ev[i])*ell.conj()*r/alpha
                    derivatives[i] = deriv
                    moderr = np.max(np.abs(np.sqrt(w)*(abs(r)-abs(ell))))
                    lhs = np.sum(w*abs(deriv))
                    rhs = kap*np.sum(w*abs(r)**2*abs(z-ev[i]))
                    bound = max(2., (8/d)*lhs)
                    maxima["equal_modulus"] = max(maxima["equal_modulus"], float(moderr))
                    maxima["sensitivity_identity"] = max(maxima["sensitivity_identity"], float(abs(lhs-rhs)/(1+kap)))
                    maxima["deterministic_bound_ratio"] = max(maxima["deterministic_bound_ratio"], float(kap/bound))
                    counts["eigenpairs"] += 1
                E = np.sqrt(w)[:, None] * S
                Q, _ = la.qr(E, mode="economic")
                H = Q.conj().T @ (z[:, None]*Q)
                _, V = la.eig(H)
                V /= la.norm(V, axis=0)
                Vinv = la.inv(V)
                costs = la.norm(Vinv, axis=1)
                balanced = V*np.sqrt(costs)[None, :]
                balanced_inv = Vinv/np.sqrt(costs)[:, None]
                total = costs.sum()
                ferr = max(abs(la.norm(balanced, "fro")**2-total),
                           abs(la.norm(balanced_inv, "fro")**2-total))/(1+total)
                maxima["balanced_frobenius"] = max(maxima["balanced_frobenius"], float(ferr))
                ratio = la.norm(balanced, 2)*la.norm(balanced_inv, 2)/total
                maxima["balanced_condition_ratio"] = max(maxima["balanced_condition_ratio"], float(ratio))
                if rep == 0 and n <= 40:
                    phases = np.exp(2j*np.pi*rng.random(n))
                    b = np.fft.ifft(np.sqrt(w/w.sum())*phases, norm="ortho")
                    K = np.column_stack([np.roll(b, j) for j in range(k)])
                    Qp, _ = la.qr(K, mode="economic")
                    Hp = Qp.conj().T @ np.roll(Qp, 1, axis=0)
                    Qpf = np.fft.fft(Qp, axis=0, norm="ortho")
                    U = Q.conj().T @ (phases.conj()[:, None]*Qpf)
                    err = max(la.norm(U.conj().T@U-np.eye(k), 2),
                              la.norm(Hp-U.conj().T@H@U, 2))
                    maxima["physical_model_error"] = max(maxima["physical_model_error"], float(err))
                    counts["physical_model_comparisons"] += 1
                if rep == 0 and n <= 20:
                    j = int(rng.integers(n))
                    h = min(1e-6*max(1., w[j]), w[j]/10)
                    wp, wm = w.copy(), w.copy()
                    wp[j] += h; wm[j] -= h
                    _, Gp, Fp = pencil(z, wp, k)
                    _, Gm, Fm = pencil(z, wm, k)
                    ep, em = la.eigvals(Fp, Gp), la.eigvals(Fm, Gm)
                    fd = (ep[match(ev, ep)]-em[match(ev, em)])/(2*h)
                    err = np.max(abs(fd-derivatives[:, j])/(1+abs(derivatives[:, j])))
                    maxima["finite_difference_relative_error"] = max(maxima["finite_difference_relative_error"], float(err))
                    counts["finite_difference_eigenpairs"] += k
                if rep == 0 and n <= 12:
                    j = int(rng.integers(n)); t0 = w[j]
                    for theta in np.linspace(0, 2*np.pi, 9, endpoint=False):
                        wc = w.astype(complex)
                        wc[j] = t0 + .4*t0*np.exp(1j*theta)
                        _, Gc, Fc = pencil(z, wc, k)
                        radius = float(np.max(abs(la.eigvals(Fc, Gc))))
                        maxima["complex_pencil_max_radius"] = max(maxima["complex_pencil_max_radius"], radius)
                        counts["complex_pencil_tests"] += 1
                counts["matrices"] += 1
    assert maxima["equal_modulus"] < 2e-9
    assert maxima["sensitivity_identity"] < 2e-9
    assert maxima["balanced_frobenius"] < 2e-9
    assert maxima["balanced_condition_ratio"] <= 1+1e-9
    assert maxima["deterministic_bound_ratio"] <= 1+1e-9
    assert maxima["physical_model_error"] < 2e-9
    assert maxima["finite_difference_relative_error"] < 2e-5
    assert maxima["complex_pencil_max_radius"] <= 3+1e-9
    return {"status": "passed", "seed": SEED, "counts": counts, "maxima": maxima}


def root_path_checks() -> dict[str, object]:
    rng = np.random.default_rng(910336)
    records = []
    for n in [3, 4, 5, 8, 12]:
        z = np.exp(-2j*np.pi*np.arange(n)/n)
        for k in sorted({2, max(2, n//2), n-1}):
            w = rng.exponential(size=n) + .1
            j = int(rng.integers(n))
            path_length = 0.
            previous = None
            # A polygonal path is only a diagnostic, not a proof of arc length.
            for t in np.geomspace(1e-7, 1e7, 321):
                wt = w.copy(); wt[j] = t
                _, G, F = pencil(z, wt, k)
                current = la.eigvals(F, G)
                if previous is not None:
                    current = current[match(previous, current)]
                    path_length += float(np.sum(abs(current-previous)))
                previous = current
            assert path_length <= 8*k + 1e-7
            records.append({"n": n, "k": k, "coordinate": j,
                            "polygonal_total_length": path_length,
                            "analytic_upper_bound": 8*k})
    return {"status": "passed", "paths": len(records), "samples_per_path": 321,
            "warning": "Finite polygonal samples do not certify the continuous root-locus bound",
            "records": records}


def sign_family_checks() -> dict[str, object]:
    records = []
    largest_gauss_error = 0.
    dense_comparisons = 0
    for p in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 61, 101, 151, 251, 367, 601, 1009]:
        data = make_family(p)
        a, c, chi, d, eps, flips = (data.kernel, data.base_kernel, data.character,
                                  data.nonsquare, data.epsilon, data.flip_parameters)
        assert np.all((a == 1) | (a == -1))
        assert np.all(c[(2*d*flips) % p, (1+d*flips*flips) % p] == -eps)
        assert len(flips) == (p-1)//2
        assert int(a.sum(dtype=np.int64)) == eps*p
        t = np.arange(p, dtype=np.int64)
        assert np.all(c[(2*d*t) % p, (1+d*t*t) % p] == -eps)
        freq = np.fft.fft2(a)
        base_freq = np.fft.fft2(c)
        dual = (t[:, None]**2-pow(d, -1, p)*t[None, :]**2) % p
        predicted = (-eps*p)*chi[dual].astype(np.int64)
        gauss_error = float(np.max(abs(base_freq-predicted)))
        largest_gauss_error = max(largest_gauss_error, gauss_error)
        mixed_kernel = np.zeros((p, p))
        mixed_kernel[(2*d*t) % p, (1+d*t*t) % p] = chi
        mixed = np.fft.fft2(mixed_kernel); mixed[0, 0] = 0
        mixed_ratio = float(np.max(abs(mixed))/(2*np.sqrt(p)))
        err = 2+3*np.sqrt(p)
        assert gauss_error < 1e-7
        assert mixed_ratio <= 1+1e-7
        assert np.max(abs(freq)) <= p+err+1e-7
        assert np.min(abs(freq)) >= p-err-1e-7
        dense_error = None
        if p <= 11:
            A = dense_matrix(data).astype(float)
            singular = la.svdvals(A)
            fft_singular = np.sort(abs(freq).ravel())[::-1]
            dense_error = float(np.max(abs(singular-fft_singular)))
            assert dense_error < 1e-8
            dense_comparisons += 1
        result = spectral_summary(data)
        result.update(gauss_identity_error=gauss_error, mixed_bound_ratio=mixed_ratio,
                      dense_svd_error=dense_error)
        records.append(result)
    return {"status": "passed", "prime_count": len(records),
            "dense_svd_comparisons": dense_comparisons,
            "largest_gauss_identity_error": largest_gauss_error, "records": records,
            "warning": "FFT diagnostics are floating point; the uniform theorem uses the classical character-sum bound"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = {
        "verification_scope": "Exact identities plus numerical diagnostics, not independent or formal verification",
        "environment": {"python": platform.python_version(), "numpy": np.__version__,
                        "scipy": scipy.__version__, "sympy": sp.__version__},
        "exact_checks": exact_checks(),
        "krylov_checks": krylov_checks(),
        "root_path_checks": root_path_checks(),
        "sign_family_checks": sign_family_checks(),
        "overall": "all programmed checks passed",
    }
    text = json.dumps(result, indent=2, allow_nan=False)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text+"\n", encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
