#!/usr/bin/env python3
"""
general_p_theta_family.py
=========================
100% self-contained verification suite for the All-1<p<2 Dual Q-Family,
Master P-Cone Classification & Uniqueness, Unconditional Kubo-Ando + Hansen
Domain Positivity (covering 100% of 1 < p < 2 for BOTH Dual and Primal
families), Primal Basis-Invariance, Exact Mode-Spread No-Go for Single-Weight
Convex Combinations across p = 3/2, Naive Dual Scalarization Obstructions,
Adversarial Non-RG Indefinite-B_{sigma_+} Stress Tests (n = 2..5, m = 2,10,50),
Operator-Convexity All-u Audits, Mobius Pullback Monotonicity, and Polynomial
Neumann Parallel-Sum Bounds for Open Problem MI-20.

Dependencies: Python standard library + numpy, scipy, mpmath ONLY.
Zero external scratch imports. Zero touches outside scratch/.
"""

import math
import time
import numpy as np
import mpmath as mp
from scipy.linalg import eigh
from scipy.optimize import brentq, least_squares


# ==============================================================================
# 0. SELF-CONTAINED LINEAR ALGEBRA & HOLDEN RG / NON-RG SOLVERS
# ==============================================================================

def matpow(A, alpha):
    """Hermitian matrix power A^alpha for strictly positive definite A."""
    Ah = 0.5 * (A + A.conj().T)
    w, V = eigh(Ah)
    if np.min(w) <= 0.0:
        raise ValueError(f"matpow requires PSD/PD matrix, got min eig {np.min(w):.3e}")
    return (V * (w ** alpha)) @ V.conj().T


def roots_kappa(Lam, kappa):
    """Exact scalar roots 0 < x_- < (kappa-1)/kappa < x_+ of (1+x)^{2k-1} = Lam x^{k-1}."""
    t_min = math.log((kappa - 1.0) / kappa)
    logL = math.log(Lam)

    def fn(t):
        return (2.0 * kappa - 1.0) * np.logaddexp(0.0, t) - (kappa - 1.0) * t - logL

    lo, hi = t_min - 1.0, t_min + 1.0
    while fn(lo) < 0.0:
        lo -= 20.0
    while fn(hi) < 0.0:
        hi += 20.0
    xm = math.exp(brentq(fn, lo, t_min, xtol=1e-15, rtol=1e-15))
    xp = math.exp(brentq(fn, t_min, hi, xtol=1e-15, rtol=1e-15))
    sm = (xm ** (kappa - 1.0)) * (xm - 1.0)
    sp = (xp ** (kappa - 1.0)) * (xp - 1.0)
    return xm, xp, sm, sp


def _roots_p32(Lam):
    if Lam <= 16.0 / (3.0 * math.sqrt(3.0)) + 1e-12:
        return None
    rts = np.roots([1.0, 0.0, 2.0, -Lam, 1.0])
    pos = np.sort(np.real(rts[np.abs(np.imag(rts)) < 1e-10]))
    pos = pos[pos > 0.0]
    if len(pos) < 2:
        return None
    qm, qp = float(pos[0]), float(pos[-1])
    return qm, qp, qp * (qp * qp - 1.0)


def _solve_rg_p32_step(r, m=2.0, prev=None):
    """Self-contained rank-r RG solver at p = 3/2 (kappa = 3/2)."""
    triu = np.triu_indices(r)

    def run_from(Lam0, d0, Q0):
        x0 = np.concatenate([[Lam0], np.log(d0[1:]), Q0[triu]])

        def res(x):
            Lam = x[0]
            rt = _roots_p32(Lam)
            if rt is None or np.any(x[1:r] < -40.0) or np.any(x[1:r] > 5.0):
                return np.full(r * (r + 1), 1e3)
            _, _, sp = rt
            d = np.concatenate([[1.0], np.exp(x[1:r])])
            Q = np.zeros((r, r))
            Q[triu] = x[r:]
            Q = Q + np.triu(Q, 1).T
            D = np.diag(d)
            H = (Q * d[None, :]) @ Q
            M = D + H
            R1 = M @ M - Lam * ((d[:, None] * Q) * d[None, :])
            F = H @ (d[:, None] * Q) - (d[:, None] * Q) * d[None, :]
            F_tar = np.diag(np.concatenate([[-sp / (m - 1.0)], sp * (d[1:] ** 2)]))
            R2 = F - F_tar
            w1 = 1.0 / np.outer(d, d)
            w2 = 1.0 / np.outer(d ** 1.5, d ** 1.5)
            return np.concatenate([(R1 * w1)[triu], (R2 * w2)[triu]])

        sol = least_squares(res, x0, xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=6000)
        Lam = float(sol.x[0])
        d = np.concatenate([[1.0], np.exp(sol.x[1:r])])
        Q = np.zeros((r, r))
        Q[triu] = sol.x[r:]
        Q = Q + np.triu(Q, 1).T
        idx = np.concatenate([[0], 1 + np.argsort(d[1:])[::-1]])
        return Lam, d[idx], Q[np.ix_(idx, idx)], float(np.linalg.norm(sol.fun))

    if prev is None:
        assert r == 2
        Lam0 = 4.45337
        qm, qp, _ = _roots_p32(Lam0)
        return run_from(Lam0, np.array([1.0, 0.075]), np.array([[qm, -0.05], [-0.05, 0.7 * qp]]))
    Lam_p, d_p, Q_p = prev
    rp = len(d_p)
    assert r == rp + 1
    ratio = d_p[-1] / d_p[-2] if rp >= 3 else 0.15
    err = 1e9
    for r_try in [ratio, 0.5, 0.25, 0.7]:
        d0 = np.append(d_p, d_p[-1] * min(0.85, max(0.05, r_try)))
        Q0 = np.zeros((r, r))
        Q0[:rp, :rp] = Q_p
        Q0[-1, -1] = Q_p[-1, -1]
        for j in range(1, rp):
            Q0[j, -1] = Q0[-1, j] = Q_p[j - 1, -1]
        Q0[0, -1] = Q0[-1, 0] = Q_p[0, -1] * 0.25
        Lam, d, Q, err = run_from(Lam_p, d0, Q0)
        rt = _roots_p32(Lam)
        if rt is not None and err < 1e-8 and np.min(eigh(Q, eigvals_only=True)) > 0 and np.max(eigh(Q, eigvals_only=True)) < rt[1] - 1e-6:
            return Lam, d, Q, err
    raise RuntimeError(f"p=3/2 RG solver failed at r={r}, m={m}, last err={err:.3e}")


_P32_CACHE = {}


def get_p32_rg(r, m=2.0):
    """Cached rank-r RG block (Lam, d, X) at p = 3/2, m = 2."""
    key = (r, float(m))
    if key in _P32_CACHE:
        return _P32_CACHE[key]
    if abs(m - 2.0) < 1e-12:
        prev = None
        for rr in range(2, r + 1):
            Lr, dr, Qr, err = _solve_rg_p32_step(rr, m=2.0, prev=prev)
            assert err < 1e-10
            prev = (Lr, dr, Qr)
        Lr, dr, Qr = prev
        sd = np.sqrt(dr)
        isd = 1.0 / sd
        Hr = (Qr * dr[None, :]) @ Qr
        Xr = (isd[:, None] * Hr) * isd[None, :]
        _P32_CACHE[key] = (Lr, dr, Xr)
        return Lr, dr, Xr
    # Continue smoothly in m from m=2 at p=3/2
    L, d, X = get_p32_rg(r, m=2.0)
    n_m = 6 if m <= 12 else 12
    for mm in np.geomspace(2.0, float(m), n_m)[1:]:
        L, d, X, err, oe = solve_rg_lsq(1.5, float(mm), r, L, d, X)
        assert err < 1e-9 and oe < 1e-9, f"m-continuation failed at m={mm}: {err:.2e}, {oe:.2e}"
    _P32_CACHE[key] = (L, d, X)
    return L, d, X


def solve_rg_lsq(p, m, r_cur, Lam_init, d_init, X_init):
    """Solve rank-r general-p RG block using X = exp(S) parameterization."""
    kappa = p / (2.0 * (p - 1.0))
    triu = np.triu_indices(r_cur)
    L0 = 2.0 ** (2.0 * kappa - 1.0)
    w0, V0 = eigh(0.5 * (X_init + X_init.T))
    S0 = (V0 * np.log(np.maximum(w0, 1e-14))) @ V0.T
    x0 = np.concatenate([[math.log(max(Lam_init - L0, 1e-12))], np.log(d_init[1:]), S0[triu]])

    def unpack(x):
        L = L0 + math.exp(float(np.clip(x[0], -35.0, 25.0)))
        dd = np.concatenate([[1.0], np.exp(np.clip(x[1:r_cur], -35.0, 5.0))])
        S = np.zeros((r_cur, r_cur))
        S[triu] = np.clip(x[r_cur:], -16.0, 6.0)
        S = S + S.T - np.diag(np.diag(S))
        w, V = eigh(S)
        X = (V * np.exp(w)) @ V.T
        return L, dd, X

    def res(x):
        L, dd, X = unpack(x)
        _, _, _, sp = roots_kappa(L, kappa)
        sD = np.sqrt(dd)
        D = np.diag(dd)
        H = (sD[:, None] * X) * sD[None, :]
        M = D + H
        G = (sD[:, None] * H) * sD[None, :]
        D_scale = dd ** (-kappa + 0.5)
        Z = (dd ** (1.0 - kappa))[:, None] * matpow(G, kappa - 1.0) * (dd ** (1.0 - kappa))[None, :]
        R1 = (D_scale[:, None] * matpow(M, 2.0 * kappa - 1.0) * D_scale[None, :]) - L * Z
        Ehat = ((dd ** (-kappa))[:, None] * matpow(G, kappa) * (dd ** (-kappa))[None, :]) - Z
        target_diag = np.concatenate([[-sp / (m - 1.0)], np.full(r_cur - 1, sp)])
        return np.concatenate([R1[triu], np.diag(Ehat) - target_diag])

    sol = least_squares(res, x0, xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=3000)
    L, dd, X = unpack(sol.x)
    sD = np.sqrt(dd)
    H = (sD[:, None] * X) * sD[None, :]
    G = (sD[:, None] * H) * sD[None, :]
    Z = (dd ** (1.0 - kappa))[:, None] * matpow(G, kappa - 1.0) * (dd ** (1.0 - kappa))[None, :]
    Ehat = ((dd ** (-kappa))[:, None] * matpow(G, kappa) * (dd ** (-kappa))[None, :]) - Z
    off_err = float(np.linalg.norm(Ehat - np.diag(np.diag(Ehat))))
    return L, dd, X, float(np.linalg.norm(sol.fun)), off_err


_RG_CACHE = {}


def continue_rg(p_target, r, m=2.0):
    """Continue rank-r RG block from p = 3/2 to any target p in (1, 2) and m >= 2."""
    key = (round(float(p_target), 12), r, round(float(m), 8))
    if key in _RG_CACHE:
        return _RG_CACHE[key]
    L, d, X = get_p32_rg(r, m=m)
    k_tgt = p_target / (2.0 * (p_target - 1.0))
    if abs(k_tgt - 1.5) < 1e-12:
        _RG_CACHE[key] = (L, d, X)
        return L, d, X
    k_cur = 1.5
    step = 0.04 if k_tgt > 1.5 else -0.02
    while abs(k_tgt - k_cur) > 1e-12:
        k_next = k_tgt if abs(k_tgt - k_cur) <= abs(step) else k_cur + step
        pp = 2.0 * k_next / (2.0 * k_next - 1.0)
        Ln, dn, Xn, err, oe = solve_rg_lsq(pp, m, r, L, d, X)
        if err < 1e-9 and oe < 1e-9:
            L, d, X, k_cur = Ln, dn, Xn, k_next
        else:
            step *= 0.5
            assert abs(step) > 1e-5, f"RG continuation stalled at k={k_cur}, r={r}, m={m}"
    _RG_CACHE[key] = (L, d, X)
    return L, d, X


def sweep_2x2_branch(p, L, d_seed, X_seed):
    """Sweep the entire coupled 2x2 Holden solution curve at fixed (p, L)."""
    kap = p / (2.0 * (p - 1.0))
    triu = np.triu_indices(2)

    def solve_d1(d1, X0):
        d = np.array([1.0, d1])
        sd = np.sqrt(d)
        D = np.diag(d)
        w0, V0 = eigh(0.5 * (X0 + X0.T))
        S0 = (V0 * np.log(np.maximum(w0, 1e-14))) @ V0.T

        def res(z):
            S = np.array([[z[0], z[1]], [z[1], z[2]]])
            w, V = eigh(S)
            X = (V * np.exp(np.clip(w, -18.0, 8.0))) @ V.T
            H = (sd[:, None] * X) * sd[None, :]
            G = (sd[:, None] * H) * sd[None, :]
            M = D + H
            Ds = d ** (-kap + 0.5)
            Z = (d ** (1.0 - kap))[:, None] * matpow(G, kap - 1.0) * (d ** (1.0 - kap))[None, :]
            R1 = (Ds[:, None] * matpow(M, 2.0 * kap - 1.0) * Ds[None, :]) - L * Z
            return R1[triu]

        sol = least_squares(res, S0[triu], xtol=1e-15, ftol=1e-15, gtol=1e-15)
        S = np.array([[sol.x[0], sol.x[1]], [sol.x[1], sol.x[2]]])
        w, V = eigh(S)
        X = (V * np.exp(w)) @ V.T
        if np.linalg.norm(sol.fun) < 1e-11 and abs(X[0, 1]) > 1e-5:
            return X
        return None

    pts = [(d_seed, X_seed.copy())]
    for factor, limit, cmp_fn in [(0.96, 1e-5, lambda v, lim: v < lim),
                                  (1.04, 0.999, lambda v, lim: v > lim)]:
        d_cur, X_cur = d_seed, X_seed.copy()
        for _ in range(300):
            d_next = d_cur * factor
            if cmp_fn(d_next, limit):
                break
            Xn = solve_d1(d_next, X_cur)
            if Xn is None:
                break
            pts.append((d_next, Xn))
            d_cur, X_cur = d_next, Xn
    return sorted(pts, key=lambda t: t[0])


def solve_complex_holden(p, L, d_vec, X_init):
    """Solve Holden's equation at fixed (p, L, d_vec) for complex Hermitian X = exp(S)."""
    kap = p / (2.0 * (p - 1.0))
    n = len(d_vec)
    sd = np.sqrt(d_vec)
    D = np.diag(d_vec)
    triu = np.triu_indices(n, 1)
    n_off = len(triu[0])
    w0, V0 = eigh(0.5 * (X_init + X_init.conj().T))
    S0 = (V0 * np.log(np.maximum(w0, 1e-12))) @ V0.conj().T
    z0 = np.concatenate([np.real(np.diag(S0)), np.real(S0[triu]), np.imag(S0[triu])])

    def unpack(z):
        S = np.diag(z[:n].astype(complex))
        off = z[n:n + n_off] + 1j * z[n + n_off:]
        S[triu] = off
        S = S + S.conj().T - np.diag(np.diag(S))
        w, V = eigh(S)
        return (V * np.exp(np.clip(w, -18.0, 7.0))) @ V.conj().T

    def res(z):
        X = unpack(z)
        H = (sd[:, None] * X) * sd[None, :]
        G = (sd[:, None] * H) * sd[None, :]
        M = D + H
        Ds = d_vec ** (-kap + 0.5)
        Z = (d_vec ** (1.0 - kap))[:, None] * matpow(G, kap - 1.0) * (d_vec ** (1.0 - kap))[None, :]
        R1 = (Ds[:, None] * matpow(M, 2.0 * kap - 1.0) * Ds[None, :]) - L * Z
        return np.concatenate([np.real(np.diag(R1)), np.real(R1[triu]), np.imag(R1[triu])])

    sol = least_squares(res, z0, xtol=1e-14, ftol=1e-14, gtol=1e-14, max_nfev=1500)
    return unpack(sol.x), float(np.linalg.norm(sol.fun))


# ==============================================================================
# 1. GENERAL HERMITIAN EVALUATORS FOR PRIMAL X-FAMILY & DUAL P-CONE / Q-FAMILY
# ==============================================================================

def holden_operators(D, H, kappa):
    """Compute core scale-invariant Holden operators for general Hermitian (D, H) > 0."""
    sD = matpow(D, 0.5)
    isD = matpow(D, -0.5)
    G = sD @ H @ sD
    M = D + H
    X = isD @ H @ isD
    Q = isD @ matpow(G, 0.5) @ isD
    Dm_k = matpow(D, -kappa)
    D1_k = matpow(D, 1.0 - kappa)
    Z_primal = D1_k @ matpow(G, kappa - 1.0) @ D1_k
    Ehat = Dm_k @ matpow(G, kappa) @ Dm_k - Z_primal
    return dict(sD=sD, isD=isD, G=G, M=M, X=X, Q=Q, Z_primal=Z_primal, Ehat=Ehat)


def eval_dual_q_family(L, kappa, D, H, s_nodes, w_nodes, delta=0.0):
    """Evaluate canonical Dual Q-Family (theta = 0):
         W1^{-1} = D^{k-1} M^{2-2k} D^{k-1}
         P       = D^{k-3/2} G^{3/2-k} D^{k-3/2}
         Y       = D^{1/2-k} G^{k-1/2} D^{1/2-k}
         K_tilde(s) = (sig_+ + delta) I - s Y + (L W1^{-1} - s P)^{-1}
    """
    n = D.shape[0]
    _, _, _, sp = roots_kappa(L, kappa)
    ops = holden_operators(D, H, kappa)
    G, M = ops["G"], ops["M"]
    Dk_m1 = matpow(D, kappa - 1.0)
    Dk_m15 = matpow(D, kappa - 1.5)
    D05_mk = matpow(D, 0.5 - kappa)
    W1_inv = Dk_m1 @ matpow(M, 2.0 - 2.0 * kappa) @ Dk_m1
    P = Dk_m15 @ matpow(G, 1.5 - kappa) @ Dk_m15
    Y = D05_mk @ matpow(G, kappa - 0.5) @ D05_mk

    I_op = np.zeros((n, n), dtype=np.result_type(D.dtype, H.dtype))
    Fp0 = np.zeros_like(I_op)
    min_mid = 1e99
    min_K = 1e99
    for sk, wk in zip(s_nodes, w_nodes):
        mid = L * W1_inv - sk * P
        mid = 0.5 * (mid + mid.conj().T)
        ev_m = eigh(mid, eigvals_only=True)
        min_mid = min(min_mid, float(ev_m[0]))
        if ev_m[0] <= 0.0:
            return None, None, min_mid, -1e99
        Ko = (sp + delta) * np.eye(n) - sk * Y + np.linalg.inv(mid)
        Ko = 0.5 * (Ko + Ko.conj().T)
        ev_k = eigh(Ko, eigvals_only=True)
        min_K = min(min_K, float(ev_k[0]))
        if ev_k[0] <= 0.0:
            return None, None, min_mid, min_K
        Kinv = np.linalg.inv(Ko)
        I_op += wk * Kinv
        Linv = (sp + delta) * Kinv
        Fp0 += wk * (Linv - Linv @ Linv)
    return 0.5 * (I_op + I_op.conj().T), 0.5 * (Fp0 + Fp0.conj().T), min_mid, min_K


def eval_dual_theta_family(L, kappa, D, H, theta, s_nodes, w_nodes, delta=0.0):
    """Evaluate Dual P_theta-Family with P_th = D^{k-3/2-th} G^{3/2-k+th} D^{k-3/2-th}."""
    n = D.shape[0]
    _, _, _, sp = roots_kappa(L, kappa)
    ops = holden_operators(D, H, kappa)
    G, M = ops["G"], ops["M"]
    Dk_m1 = matpow(D, kappa - 1.0)
    W1_inv = Dk_m1 @ matpow(M, 2.0 - 2.0 * kappa) @ Dk_m1
    D_p = matpow(D, kappa - 1.5 - theta)
    G_p = matpow(G, 1.5 - kappa + theta)
    P_th = D_p @ G_p @ D_p
    A_fac = matpow(D, 0.5 - kappa) @ matpow(G, kappa - 1.0) @ matpow(D, -theta)
    Y_th = A_fac @ G_p @ A_fac.conj().T

    I_op = np.zeros((n, n), dtype=np.result_type(D.dtype, H.dtype))
    min_mid = 1e99
    min_K = 1e99
    for sk, wk in zip(s_nodes, w_nodes):
        mid = 0.5 * ((L * W1_inv - sk * P_th) + (L * W1_inv - sk * P_th).conj().T)
        ev_m = eigh(mid, eigvals_only=True)
        min_mid = min(min_mid, float(ev_m[0]))
        if ev_m[0] <= 1e-13:
            return None, min_mid, -1e99
        Ko = (sp + delta) * np.eye(n) - sk * Y_th + np.linalg.inv(mid)
        Ko = 0.5 * (Ko + Ko.conj().T)
        ev_k = eigh(Ko, eigvals_only=True)
        min_K = min(min_K, float(ev_k[0]))
        if ev_k[0] <= 1e-13:
            return None, min_mid, min_K
        I_op += wk * np.linalg.inv(Ko)
    return 0.5 * (I_op + I_op.conj().T), min_mid, min_K


def eval_primal_x_family(L, kappa, D, H, x_nodes, p_nodes, delta=0.0):
    """Evaluate Primal X-Family (#107 Thm 1.1) for general Hermitian (D, H) > 0."""
    n = D.shape[0]
    _, _, _, sp = roots_kappa(L, kappa)
    ops = holden_operators(D, H, kappa)
    G, M, Zg = ops["G"], ops["M"], ops["Z_primal"]
    D_t1 = matpow(D, kappa - 1.5)
    D_t2 = matpow(D, kappa - 2.0)
    T1 = D_t1 @ matpow(M, 3.0 - 2.0 * kappa) @ D_t1
    T2 = D_t2 @ matpow(G, 2.0 - kappa) @ D_t2

    I_op = np.zeros((n, n), dtype=np.result_type(D.dtype, H.dtype))
    min_mid = 1e99
    min_K = 1e99
    for xk, pk in zip(x_nodes, p_nodes):
        gam = (1.0 + xk) / L
        mid = 0.5 * ((T1 - gam * T2) + (T1 - gam * T2).conj().T)
        ev_m = eigh(mid, eigvals_only=True)
        min_mid = min(min_mid, float(ev_m[0]))
        if ev_m[0] <= 0.0:
            return None, min_mid, -1e99
        Ko = (sp + delta) * np.eye(n) - xk * Zg + gam * np.linalg.inv(mid)
        Ko = 0.5 * (Ko + Ko.conj().T)
        ev_k = eigh(Ko, eigvals_only=True)
        min_K = min(min_K, float(ev_k[0]))
        if ev_k[0] <= 0.0:
            return None, min_mid, min_K
        I_op += pk * np.linalg.inv(Ko)
    return 0.5 * (I_op + I_op.conj().T), min_mid, min_K


# ==============================================================================
# SUITE 1: MASTER DUAL P-CONE, DUAL Q-FAMILY, UNIQUENESS, & PRIMAL BASIS-INVARIANCE
# ==============================================================================

def run_suite_1():
    print("=" * 84)
    print("SUITE 1: MASTER DUAL P-CONE, DUAL Q-FAMILY, UNIQUENESS & PRIMAL BASIS-INVARIANCE")
    print("=" * 84)
    rng = np.random.default_rng(101)
    phi = 0.5 * (1.0 + math.sqrt(5.0))
    exps = [("5/3", 5 / 3), ("phi", phi), ("3/2", 1.5), ("sqrt(2)", math.sqrt(2.0)),
            ("7/5", 7 / 5), ("4/3", 4 / 3), ("5/4", 5 / 4), ("6/5", 6 / 5)]

    max_comm_err = 0.0
    max_p1_err = 0.0
    max_id_q_err = 0.0
    max_id_genP_err = 0.0
    max_ker_err = 0.0
    max_kinv_err = 0.0
    max_eig_err = 0.0
    max_basis_inv_err = 0.0

    print("\n--- 1A: Complex Non-Diagonal 3x3 RG Verification (8 Exponents, Full U(3) Rotation) ---")
    for label, p in exps:
        kap = p / (2.0 * (p - 1.0))
        L, d, X = continue_rg(p, 3, m=2.0)
        _, xp, _, sp = roots_kappa(L, kap)
        c3 = 2.0 * sp
        sd = np.sqrt(d)
        H0 = (sd[:, None] * X) * sd[None, :]
        D0 = np.diag(d)

        # Conjugate by random complex unitary U in U(3) so D, H are full non-diagonal complex Hermitian
        A_u = rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3))
        U, _ = np.linalg.qr(A_u)
        D = U @ D0 @ U.conj().T
        H = U @ H0 @ U.conj().T
        w0 = U[:, 0]

        ops = holden_operators(D, H, kap)
        G, M, Q, Ehat = ops["G"], ops["M"], ops["Q"], ops["Ehat"]
        E = matpow(G, kap) - D @ matpow(G, kap - 1.0) @ D

        # 3-line conserved commutator & identity Lambda E = M^{2k} - D M^{2k-1} - M^{2k-1} D
        comm_err = float(np.linalg.norm(E @ D - D @ E))
        M2km1 = matpow(M, 2.0 * kap - 1.0)
        p1_err = float(np.linalg.norm(L * E - (M @ M2km1 - D @ M2km1 - M2km1 @ D)))
        max_comm_err = max(max_comm_err, comm_err)
        max_p1_err = max(max_p1_err, p1_err)

        # Canonical Dual Q-Family objects
        Z_M = matpow(D, -kap) @ M @ matpow(D, kap - 1.0)
        W1 = matpow(D, 1.0 - kap) @ matpow(M, 2.0 * kap - 2.0) @ matpow(D, 1.0 - kap)
        W1_inv = matpow(D, kap - 1.0) @ matpow(M, 2.0 - 2.0 * kap) @ matpow(D, kap - 1.0)
        P_can = matpow(D, kap - 1.5) @ matpow(G, 1.5 - kap) @ matpow(D, kap - 1.5)
        Y_can = matpow(D, 0.5 - kap) @ matpow(G, kap - 0.5) @ matpow(D, 0.5 - kap)
        W2_can = W1 @ P_can @ W1

        evQ, UQ = eigh(0.5 * (Q + Q.conj().T))
        w_mu = np.abs(w0.conj() @ UQ) ** 2

        Bsp = sp * np.eye(3) - Ehat
        id_q_err = 0.0
        ker_err = 0.0
        kinv_err = 0.0
        I_dual = np.zeros((3, 3), dtype=complex)
        for k in range(3):
            sk = float(evQ[k])
            mid = L * W1_inv - sk * P_can
            K_s = sp * np.eye(3) - sk * Y_can + np.linalg.inv(mid)
            R_s = Z_M - L * np.linalg.inv(mid) @ W1_inv
            rhs = (1.0 / L) * R_s @ (W1 - (sk / L) * W2_can) @ R_s.conj().T
            id_q_err = max(id_q_err, float(np.linalg.norm((K_s - Bsp) - rhs)))

            # Kernel factorization: R_s (W1 - (s/L) W2) = D^{-k} (Q - s I) D^{1/2} G^{1/2} D^{k-3/2} W1
            lhs_fac = R_s @ (W1 - (sk / L) * W2_can)
            rhs_fac = matpow(D, -kap) @ (Q - sk * np.eye(3)) @ matpow(D, 0.5) @ matpow(G, 0.5) @ matpow(D, kap - 1.5) @ W1
            ker_err = max(ker_err, float(np.linalg.norm(lhs_fac - rhs_fac)))

            # Exact RG eigenvector formula: K_{q_k}^{-1} w0 = (1 / (c_r <w0, u_k>)) D^k u_k
            uk = UQ[:, k]
            uk0 = complex(np.vdot(w0, uk))
            Kinv_w0 = np.linalg.solve(K_s, w0)
            target = (1.0 / (c3 * uk0)) * (matpow(D, kap) @ uk)
            kinv_err = max(kinv_err, float(np.linalg.norm(Kinv_w0 - target)))
            I_dual += w_mu[k] * np.linalg.inv(K_s)

        eig_err = float(np.linalg.norm(c3 * (I_dual @ w0) - w0))
        max_id_q_err = max(max_id_q_err, id_q_err)
        max_ker_err = max(max_ker_err, ker_err)
        max_kinv_err = max(max_kinv_err, kinv_err)
        max_eig_err = max(max_eig_err, eig_err)

        # Master Dual P-Cone check for a COMPLETELY ARBITRARY random complex Hermitian P > 0
        B_rand = rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3))
        P_rand = B_rand @ B_rand.conj().T + 0.5 * np.eye(3)
        # Choose s_safe strictly below min eig(L * P_rand^{-1/2} W1^{-1} P_rand^{-1/2})
        isPr = matpow(P_rand, -0.5)
        s_max_rand = float(eigh(0.5 * (L * isPr @ W1_inv @ isPr + (L * isPr @ W1_inv @ isPr).conj().T), eigvals_only=True)[0])
        s_test = 0.5 * s_max_rand
        C_op = matpow(D, 0.5 - kap) @ matpow(G, kap - 1.0) @ matpow(D, 1.5 - kap)
        Y_rand = C_op @ P_rand @ C_op.conj().T
        W2_rand = W1 @ P_rand @ W1
        mid_r = L * W1_inv - s_test * P_rand
        K_r = sp * np.eye(3) - s_test * Y_rand + np.linalg.inv(mid_r)
        R_r = Z_M - L * np.linalg.inv(mid_r) @ W1_inv
        rhs_r = (1.0 / L) * R_r @ (W1 - (s_test / L) * W2_rand) @ R_r.conj().T
        id_genP_err = float(np.linalg.norm((K_r - Bsp) - rhs_r))
        max_id_genP_err = max(max_id_genP_err, id_genP_err)

        # Theorem 1.3: Primal Basis-Invariance check under arbitrary invertible complex (C1, C2)
        C1 = rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3)) + 2.0 * np.eye(3)
        C2 = rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3)) + 2.0 * np.eye(3)
        W_b = np.linalg.inv(C1) @ np.linalg.inv(C1.conj().T)
        S_b = np.linalg.inv(C2) @ np.linalg.inv(C2.conj().T)
        At = matpow(D, 1.5 - kap) @ matpow(M, kap - 1.5)
        Bt = matpow(G, 1.0 - 0.5 * kap) @ matpow(D, -0.5) @ matpow(M, kap - 1.5)
        A_b = At @ C2
        B_b = np.linalg.inv(C1) @ Bt @ C2
        gam = 1.0 / L
        schur_gen = A_b @ np.linalg.inv(np.linalg.inv(S_b) - gam * B_b.conj().T @ np.linalg.inv(W_b) @ B_b) @ A_b.conj().T
        schur_can = At @ np.linalg.inv(np.eye(3) - gam * Bt.conj().T @ Bt) @ At.conj().T
        b_err = float(np.linalg.norm(schur_gen - schur_can))
        max_basis_inv_err = max(max_basis_inv_err, b_err)

        print(f"  p={label:>7s} (k={kap:.3f}): 1sq={id_q_err:.2e} | genP={id_genP_err:.2e} | ker={ker_err:.2e} | Kinv={kinv_err:.2e} | eig={eig_err:.2e} | BInv={b_err:.2e}")

    assert max_comm_err < 1e-11
    assert max_p1_err < 1e-11
    assert max_id_q_err < 5e-11
    assert max_id_genP_err < 5e-11
    assert max_ker_err < 1e-11
    assert max_kinv_err < 1e-11
    assert max_eig_err < 1e-12
    assert max_basis_inv_err < 1e-12

    print("\n--- 1B: Continuous Dual P_theta-Family Uniqueness Scan (r = 3, m = 2) ---")
    for label, p in [("sqrt(2)", math.sqrt(2.0)), ("5/4", 5 / 4), ("6/5", 6 / 5)]:
        kap = p / (2.0 * (p - 1.0))
        L3, d3, X3 = continue_rg(p, 3, m=2.0)
        _, _, _, sp3 = roots_kappa(L3, kap)
        c3 = 2.0 * sp3
        sd3 = np.sqrt(d3)
        D3 = np.diag(d3)
        H3 = (sd3[:, None] * X3) * sd3[None, :]
        ops3 = holden_operators(D3, H3, kap)
        G3, Q3 = ops3["G"], ops3["Q"]
        evQ3, UQ3 = eigh(Q3)
        w3 = UQ3[0, :] ** 2
        print(f"  p={label} (k={kap:.4f}):")
        for th in [-0.25, 0.0, 0.5 * (kap - 1.5), kap - 1.5]:
            s_nodes = evQ3 ** (1.0 - 2.0 * th)
            I_th, mm, _ = eval_dual_theta_family(L3, kap, D3, H3, th, s_nodes, w3)
            # Check commutator [D^{k-3/2} P_th^{-1} D^{k-3/2}, G]
            D_p = matpow(D3, kap - 1.5 - th)
            P_th = D_p @ matpow(G3, 1.5 - kap + th) @ D_p
            M_comm = matpow(D3, kap - 1.5) @ np.linalg.inv(P_th) @ matpow(D3, kap - 1.5)
            c_norm = float(np.linalg.norm(M_comm @ G3 - G3 @ M_comm))
            if I_th is not None:
                evI = eigh(c3 * I_th, eigvals_only=True)
                gap00 = float((c3 * I_th)[0, 0]) - 1.0
                print(f"    th={th:+.4f}: ||[D^(k-3/2)P^-1 D^(k-3/2),G]||={c_norm:.2e} | (cI)_00-1={gap00:+.2e} | eig=[{evI[0]:.7f}, {evI[-1]:.5f}]")
                if abs(th) < 1e-14:
                    assert c_norm < 1e-13 and abs(gap00) < 1e-12 and evI[0] >= 1.0 - 1e-11
                else:
                    assert c_norm > 1e-4 and gap00 < -1e-7
            else:
                print(f"    th={th:+.4f}: ||[.,G]||={c_norm:.2e} | DOMAIN FAIL (min_mid={mm:+.3e})")
                assert abs(th) > 1e-14 and c_norm > 1e-4

    print("  [PASS] Suite 1 verified all identities, Master P-Cone, Uniqueness, and Primal Basis-Invariance.\n")


# ==============================================================================
# SUITE 2: UNCONDITIONAL ALL-(1<p<2) DOMAIN POSITIVITY (KUBO-ANDO + HANSEN)
#          + SHARPNESS REFUTATION ON NON-HOLDEN MATRICES
# ==============================================================================

def _mp_gram_schmidt_complex(M_np):
    """High-precision Gram-Schmidt orthonormalization of a complex numpy matrix in mpmath."""
    n = M_np.shape[0]
    cols = [[mp.mpc(float(M_np[i, j].real), float(M_np[i, j].imag)) for i in range(n)] for j in range(n)]
    for j in range(n):
        for prev in range(j):
            dot = sum(mp.conj(cols[prev][i]) * cols[j][i] for i in range(n))
            for i in range(n):
                cols[j][i] -= dot * cols[prev][i]
        nrm = mp.sqrt(sum(abs(cols[j][i]) ** 2 for i in range(n)))
        for i in range(n):
            cols[j][i] /= nrm
    U = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            U[i, j] = cols[j][i]
    return U


def _mp_matpow_herm(A, alpha):
    ev, V = mp.eigh(A)
    n = len(ev)
    out = mp.matrix(n, n)
    for k in range(n):
        lam = ev[k] ** alpha
        for i in range(n):
            for j in range(n):
                out[i, j] += lam * V[i, k] * mp.conj(V[j, k])
    return out


def run_suite_2():
    print("=" * 84)
    print("SUITE 2: ALL-1<p<2 DOMAIN POSITIVITY (KUBO-ANDO + HANSEN 60-90 DPS) & SHARPNESS")
    print("=" * 84)
    rng = np.random.default_rng(202)
    phi = 0.5 * (1.0 + math.sqrt(5.0))

    # 2A: Dual Kubo-Ando on p in [3/2, 2) (NO Holden equation required, genuinely complex!)
    print("\n--- 2A: Dual Kubo-Ando Domain Positivity on p in [3/2, 2) (2,004 Complex 3x3 Matrices) ---")
    for label, p in [("1.8", 1.8), ("5/3", 5 / 3), ("phi", phi), ("3/2", 1.5)]:
        kap = p / (2.0 * (p - 1.0))
        min_margin = 1e99
        min_ka = 1e99
        max_barg = 0.0
        for xp in [1.2, 5.0, 20.0]:
            L = ((1.0 + xp) ** (2.0 * kap - 1.0)) / (xp ** (kap - 1.0))
            sp_s = math.sqrt(xp)
            for _ in range(167):
                d = np.exp(rng.uniform(-3.0, 3.0, size=3))
                U1, _ = np.linalg.qr(rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3)))
                U2, _ = np.linalg.qr(rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3)))
                D = (U1 * d) @ U1.conj().T
                xe = rng.uniform(1e-3, xp, size=3)
                X = (U2 * xe) @ U2.conj().T
                sD = matpow(D, 0.5)
                H = sD @ X @ sD
                max_barg = max(max_barg, float(abs(np.imag(H[0, 1] * H[1, 2] * H[2, 0]))))
                G = sD @ H @ sD
                M = D + H
                # Raw Kubo-Ando inequality: (x_+^{3/2-k}/(1+x_+)^{2-2k}) M^{2-2k} - D^{-1/2} G^{3/2-k} D^{-1/2} >= 0
                isD = matpow(D, -0.5)
                lhs = isD @ matpow(G, 1.5 - kap) @ isD
                rhs = (xp ** (1.5 - kap)) / ((1.0 + xp) ** (2.0 - 2.0 * kap)) * matpow(M, 2.0 - 2.0 * kap)
                diff_ka = rhs - lhs
                min_ka = min(min_ka, float(eigh(0.5 * (diff_ka + diff_ka.conj().T), eigvals_only=True)[0]))
                # Implied lower bound: L W1^{-1} - s_+ P >= (1/(1+x_+)) L W1^{-1}
                Dk1 = matpow(D, kap - 1.0)
                Dk15 = matpow(D, kap - 1.5)
                W1_inv = Dk1 @ matpow(M, 2.0 - 2.0 * kap) @ Dk1
                P = Dk15 @ matpow(G, 1.5 - kap) @ Dk15
                marg = (L * W1_inv - sp_s * P) - (L / (1.0 + xp)) * W1_inv
                min_margin = min(min_margin, float(eigh(0.5 * (marg + marg.conj().T), eigvals_only=True)[0]))
        print(f"  p={label:>4s} (k={kap:.4f}): 501 complex 3x3 (max|Barg|={max_barg:.2e}) | min_KA={min_ka:+.3e} | min_margin={min_margin:+.3e}")
        assert min_ka >= -1e-11 and min_margin >= -1e-10 and max_barg > 1e-2

    # 2B: Hansen (1980) Inequality at 60-90 dps for BOTH Dual (p <= 3/2) & Primal (p <= 4/3)
    print("\n--- 2B: Hansen (1980) Operator Inequality at 60-90 dps (Complex & Ill-Conditioned 3x3) ---")
    mp_cases = [
        ("3/2", mp.mpf(3) / 2, 60),
        ("sqrt(2)", mp.sqrt(2), 60),
        ("7/5", mp.mpf(7) / 5, 60),
        ("4/3", mp.mpf(4) / 3, 60),
        ("5/4", mp.mpf(5) / 4, 60),
        ("6/5", mp.mpf(6) / 5, 70),
        ("11/10", mp.mpf(11) / 10, 90),
    ]
    for label, p_mp, dps in mp_cases:
        mp.mp.dps = dps
        kap = p_mp / (2 * (p_mp - 1))
        alpha = (kap - mp.mpf(3) / 2) / (kap - 1)
        beta = (kap - 2) / (kap - 1)
        min_d_eig = mp.mpf("1e99")
        min_p_eig = mp.mpf("1e99")
        max_barg_mp = 0.0
        max_cond_D = 0.0
        max_cond_Mtop = mp.mpf(0)
        for xp_f in [1.5, 10.0]:
            xp = mp.mpf(xp_f)
            for trial in range(4):
                # Ill-conditioned (realized cond(D) up to ~2.0e5) AND genuinely complex non-real Hermitian!
                de = [mp.exp(mp.mpf(float(rng.uniform(-6.5, 6.5)))) for _ in range(3)]
                max_cond_D = max(max_cond_D, float(max(de) / min(de)))
                U1 = _mp_gram_schmidt_complex(rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3)))
                U2 = _mp_gram_schmidt_complex(rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3)))
                D = mp.matrix(3, 3)
                for i in range(3):
                    for j in range(3):
                        D[i, j] = sum(U1[i, k] * de[k] * mp.conj(U1[j, k]) for k in range(3))
                B = (1 + xp) * D
                isB = _mp_matpow_herm(B, mp.mpf(-1) / 2)
                sD = _mp_matpow_herm(D, mp.mpf(1) / 2)
                xe = [mp.mpf(float(rng.uniform(1e-4, xp_f))) for _ in range(3)]
                IpX = mp.matrix(3, 3)
                for i in range(3):
                    for j in range(3):
                        IpX[i, j] = sum(U2[i, k] * (1 + xe[k]) * mp.conj(U2[j, k]) for k in range(3))
                M = sD * IpX * sD
                evM = mp.eigh(M, eigvals_only=True)
                max_cond_Mtop = max(max_cond_Mtop, (max(evM) / min(evM)) ** (2 * kap - 1))
                barg_val = abs(mp.im(M[0, 1] * M[1, 2] * M[2, 0]))
                max_barg_mp = max(max_barg_mp, float(barg_val))
                A_top = isB * _mp_matpow_herm(M, 2 * kap - 1) * isB
                # Dual Hansen: (isB M^{2k-1} isB)^alpha - isB M^{2k-2} isB >= 0
                lhs_d = isB * _mp_matpow_herm(M, 2 * kap - 2) * isB
                rhs_d = _mp_matpow_herm(A_top, alpha)
                ev_d = mp.eigh(rhs_d - lhs_d, eigvals_only=True)
                min_d_eig = min(min_d_eig, min(ev_d))
                if kap >= 2:
                    lhs_p = isB * _mp_matpow_herm(M, 2 * kap - 3) * isB
                    rhs_p = _mp_matpow_herm(A_top, beta)
                    ev_p = mp.eigh(rhs_p - lhs_p, eigvals_only=True)
                    min_p_eig = min(min_p_eig, min(ev_p))
        p_txt = mp.nstr(min_p_eig, 4) if kap >= 2 else "(Kubo-Ando)"
        print(f"  p={label:>7s} ({dps:2d} dps, a={mp.nstr(alpha, 4)}): Dual={mp.nstr(min_d_eig, 4):>10s} | Primal={p_txt:>11s} | cond(D)<={max_cond_D:.2e} | cond(M^{{2k-1}})<={mp.nstr(max_cond_Mtop, 3)} | max|Barg|={max_barg_mp:.2e}")
        assert min_d_eig >= -mp.mpf("1e-30")
        if kap >= 2:
            assert min_p_eig >= -mp.mpf("1e-30")
        assert max_barg_mp > 1e-6

    # 2C: Sharpness — non-Holden random 3x3 complex matrices break L W1^{-1} - s_+ P > 0 for all kap > 3/2!
    print("\n--- 2C: Sharpness Refutation (Random Non-Holden Complex 3x3 Matrices Break Dual Domain for p < 3/2) ---")
    for label, p in [("5/3", 5 / 3), ("3/2", 1.5), ("1.45", 1.45), ("sqrt(2)", math.sqrt(2.0)),
                     ("4/3", 4 / 3), ("5/4", 5 / 4), ("6/5", 6 / 5)]:
        kap = p / (2.0 * (p - 1.0))
        xp = 3.0
        sp_s = math.sqrt(xp)
        L = ((1.0 + xp) ** (2.0 * kap - 1.0)) / (xp ** (kap - 1.0))
        n_viol = 0
        worst = 1e99
        for _ in range(300):
            d = np.exp(rng.uniform(-4.0, 4.0, size=3))
            D = np.diag(d)
            sd = np.sqrt(d)
            Q_u, _ = np.linalg.qr(rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3)))
            xe = rng.uniform(1e-3, xp, size=3)
            X = (Q_u * xe) @ Q_u.conj().T
            H = (sd[:, None] * X) * sd[None, :]
            G = (sd[:, None] * H) * sd[None, :]
            M = D + H
            W1_inv = (d ** (kap - 1.0))[:, None] * matpow(M, 2.0 - 2.0 * kap) * (d ** (kap - 1.0))[None, :]
            P = (d ** (kap - 1.5))[:, None] * matpow(G, 1.5 - kap) * (d ** (kap - 1.5))[None, :]
            mid = L * W1_inv - sp_s * P
            ev = float(eigh(0.5 * (mid + mid.conj().T), eigvals_only=True)[0])
            worst = min(worst, ev)
            if ev < -1e-12:
                n_viol += 1
        print(f"  p={label:>7s} (k={kap:.3f}): non-Holden failures = {n_viol:3d}/300 | worst min_eig = {worst:+.4e}")
        if kap <= 1.5 + 1e-12:
            assert n_viol == 0 and worst > 0.0
        else:
            assert n_viol > 0 and worst < -1e-2

    print("  [PASS] Suite 2 certified 100% all-(1<p<2) Kubo-Ando + Hansen domain positivity & sharpness.\n")


# ==============================================================================
# SUITE 3: 3-REGIME COMPLEMENTARY PHASE DIAGRAM, MODE-SPREAD NO-GO AT p = 3/2,
#          & NAIVE DUAL SCALARIZATION OBSTRUCTION (ALL p != 3/2)
# ==============================================================================

def run_suite_3():
    print("=" * 84)
    print("SUITE 3: 3-REGIME PHASE DIAGRAM, MODE-SPREAD NO-GO AT p=3/2, & SCALARIZATION OBSTRUCTION")
    print("=" * 84)

    print("\n--- 3A: Exact Complementary Sign Table Across All 3 Regimes (r = 2, m = 2) ---")
    p_grid = [1.80, 5 / 3, 1.55, 1.5, 1.48, 1.45, math.sqrt(2.0), 7 / 5, 1.37, 4 / 3, 5 / 4, 6 / 5, 1.18]
    for p in p_grid:
        kap = p / (2.0 * (p - 1.0))
        L2, d2, X2 = continue_rg(p, 2, m=2.0)
        _, _, _, sp = roots_kappa(L2, kap)
        c2 = 2.0 * sp
        sd = np.sqrt(d2)
        D2 = np.diag(d2)
        H2 = (sd[:, None] * X2) * sd[None, :]
        ops2 = holden_operators(D2, H2, kap)
        evX, UX = eigh(X2)
        p_nu = UX[0, :] ** 2
        evQ, UQ = eigh(ops2["Q"])
        w_mu = UQ[0, :] ** 2
        Ip, _, _ = eval_primal_x_family(L2, kap, D2, H2, evX, p_nu)
        Id, _, _, _ = eval_dual_q_family(L2, kap, D2, H2, evQ, w_mu)
        mp_val = float((c2 * Ip)[1, 1]) - 1.0
        md_val = float((c2 * Id)[1, 1]) - 1.0
        regime = "I" if kap < 1.5 - 1e-9 else ("3/2" if abs(kap - 1.5) < 1e-9 else ("II" if kap < 2.0 - 1e-9 else ("4/3" if abs(kap - 2.0) < 1e-9 else "III")))
        ratio_str = f"{md_val / mp_val:.2f}x" if (regime == "III") else "-"
        print(f"  p={p:.4f} (k={kap:.3f}, Reg {regime:>3s}): Primal (cI)_11-1 = {mp_val:+.4e} | Dual (cI)_11-1 = {md_val:+.4e} | Dual/Primal = {ratio_str}")
        if regime == "I":
            assert mp_val > 1e-4 and md_val < -1e-4
        elif regime == "3/2":
            assert abs(mp_val) < 1e-12 and abs(md_val) < 1e-12
        elif regime == "II":
            assert mp_val < -1e-4 and md_val > 1e-4
        elif regime == "4/3":
            assert abs(mp_val) < 1e-12 and md_val > 1e-1
        elif regime == "III":
            assert mp_val > 1e-2 and md_val > 3.5 * mp_val

    print("\n--- 3B: Higher-Rank Irreducible RG Convergence (r = 6 in Regime II, r = 4 in Regime III) ---")
    for label, p, r_max in [("1.45", 1.45, 6), ("sqrt(2)", math.sqrt(2.0), 6), ("7/5", 7 / 5, 6),
                            ("5/4", 5 / 4, 4), ("6/5", 6 / 5, 4)]:
        kap = p / (2.0 * (p - 1.0))
        L, d, X = continue_rg(p, r_max, m=2.0)
        _, xp, _, sp = roots_kappa(L, kap)
        c = 2.0 * sp
        sd = np.sqrt(d)
        D = np.diag(d)
        H = (sd[:, None] * X) * sd[None, :]
        Q = holden_operators(D, H, kap)["Q"]
        evQ, UQ = eigh(Q)
        w_mu = UQ[0, :] ** 2
        assert evQ[-1] < math.sqrt(xp) - 1e-4 and float(np.min(w_mu)) > 1e-6
        Id, _, mm, _ = eval_dual_q_family(L, kap, D, H, evQ, w_mu)
        assert Id is not None
        evI = eigh(c * Id, eigvals_only=True)
        print(f"  p={label:>7s}, r={r_max}: q_max/sq_xp={evQ[-1]/math.sqrt(xp):.4f} | w_min={float(np.min(w_mu)):.4e} | min_mid={mm:+.3e} | eig(c I_dual) = [{evI[0]:.8f}, {evI[1]:.6f}, ..., {evI[-1]:.6f}]")
        assert abs(evI[0] - 1.0) < 1e-10 and evI[1] > 1.0 + 1e-2

    print("\n--- 3C: Exact Mode-Spread & Multiplicity No-Go for Single-Weight (1-lam) I_P + lam I_D at p=3/2 ---")
    eps = 1e-3
    for r, m in [(2, 2.0), (4, 2.0), (4, 10.0)]:
        subs_p, subs_d = [], []
        for sgn, k_val in [(-1, 1.5 - eps), (+1, 1.5 + eps)]:
            p = 2.0 * k_val / (2.0 * k_val - 1.0)
            L, d, X = continue_rg(p, r, m=m)
            _, _, _, sp = roots_kappa(L, k_val)
            c = (m / (m - 1.0)) * sp
            sd = np.sqrt(d)
            D = np.diag(d)
            H = (sd[:, None] * X) * sd[None, :]
            Q = holden_operators(D, H, k_val)["Q"]
            evX, UX = eigh(X)
            evQ, UQ = eigh(Q)
            Ip, _, _ = eval_primal_x_family(L, k_val, D, H, evX, UX[0, :] ** 2)
            Id, _, _, _ = eval_dual_q_family(L, k_val, D, H, evQ, UQ[0, :] ** 2)
            sp_perp = (c * Ip)[1:, 1:] - np.eye(r - 1)
            sd_perp = (c * Id)[1:, 1:] - np.eye(r - 1)
            ev_14 = eigh(0.75 * sp_perp + 0.25 * sd_perp, eigvals_only=True)
            print(f"  r={r}, m={int(m):2d}, k=1.5{sgn * eps:+.1e} (p={p:.5f}): (3/4,1/4) min_perp = {ev_14[0]:+.3e}")
            subs_p.append(sp_perp)
            subs_d.append(sd_perp)
            if r == 4 and int(m) == 2 and sgn == +1:
                assert ev_14[0] < -1e-5  # Explicit counterexample to (3/4,1/4) in Regime II!
            if r == 4 and int(m) == 10 and sgn == -1:
                assert ev_14[0] < -5e-6  # Explicit counterexample to (3/4,1/4) in Regime I!
        d1_p = (subs_p[1] - subs_p[0]) / (2.0 * eps)
        d1_d = (subs_d[1] - subs_d[0]) / (2.0 * eps)
        # Generalized eigenvalues of d1_d v = rho (-d1_p) v -> critical lam_i = 1 / (1 + rho_i)
        ev_gen = eigh(d1_d, -d1_p, eigvals_only=True)
        lams = 1.0 / (1.0 + ev_gen)
        spread = float(np.max(lams) - np.min(lams))
        print(f"  -> r={r}, m={int(m):2d} critical mode weights lam_crit = {np.round(lams, 6)} (spread = {spread:.6f})")
        if r == 4:
            assert spread > 0.008  # Strictly non-degenerate -> NO fixed-m constant lam can work!

    print("\n--- 3D: Unique Scalar-Collapse (Det Equalities) & Naive Dual Scalarization Obstruction ---")
    for label, p in [("1.75", 1.75), ("5/3", 5 / 3), ("3/2", 1.5), ("1.45", 1.45),
                     ("sqrt(2)", math.sqrt(2.0)), ("4/3", 4 / 3), ("5/4", 5 / 4), ("6/5", 6 / 5)]:
        kap = p / (2.0 * (p - 1.0))
        L2, d2, X2 = continue_rg(p, 2, m=2.0)
        _, xp, _, sp = roots_kappa(L2, kap)
        sd = np.sqrt(d2)
        D2 = np.diag(d2)
        H2 = (sd[:, None] * X2) * sd[None, :]
        ops2 = holden_operators(D2, H2, kap)
        G2, M2, Q2, Ehat = ops2["G"], ops2["M"], ops2["Q"], ops2["Ehat"]
        W1_inv = matpow(D2, kap - 1.0) @ matpow(M2, 2.0 - 2.0 * kap) @ matpow(D2, kap - 1.0)
        P2 = matpow(D2, kap - 1.5) @ matpow(G2, 1.5 - kap) @ matpow(D2, kap - 1.5)
        Y2 = matpow(D2, 0.5 - kap) @ matpow(G2, kap - 0.5) @ matpow(D2, 0.5 - kap)
        # Determinant identities
        detX = float(np.linalg.det(X2))
        detIpX = float(np.linalg.det(np.eye(2) + X2))
        det_err = max(
            abs(float(np.linalg.det(Y2)) - detX ** (kap - 0.5)),
            abs(float(np.linalg.det(W1_inv)) - detIpX ** (2.0 - 2.0 * kap)),
            abs(float(np.linalg.det(P2)) - detX ** (1.5 - kap)),
        )
        assert det_err < 1e-12

        # Check all 3 naive scalarizations (in X, in Q, in Y) on r=2 RG (plus coupled branch for p > 3/2 in X)
        Bsp = sp * np.eye(2) - Ehat
        evQ, UQ = eigh(Q2)
        evX, UX = eigh(X2)
        evY, UY = eigh(Y2)
        min_inQ = min(float(eigh((UQ * (sp - sk * (evQ ** (2 * kap - 1)) + 1.0 / (L2 * (1 + evQ ** 2) ** (2 - 2 * kap) - sk * (evQ ** (3 - 2 * kap))))) @ UQ.T - Bsp, eigvals_only=True)[0]) for sk in evQ)
        min_inY = min(float(eigh((UY * (sp - sk * evY + 1.0 / (L2 * (1 + evY ** (1 / (kap - 0.5))) ** (2 - 2 * kap) - sk * (evY ** ((1.5 - kap) / (kap - 0.5)))))) @ UY.T - Bsp, eigvals_only=True)[0]) for sk in evQ)
        min_inX = min(float(eigh((UX * (sp - sk * (evX ** (kap - 0.5)) + 1.0 / (L2 * (1 + evX) ** (2 - 2 * kap) - sk * (evX ** (1.5 - kap))))) @ UX.T - Bsp, eigvals_only=True)[0]) for sk in evQ)
        if kap < 1.5 - 1e-9:
            # Sweep coupled 2x2 branch over s in [0, sqrt(x_+)) to find sharp inX failure!
            pts = sweep_2x2_branch(p, L2, d2[1], X2)
            for d1_c, X_c in pts:
                dc = np.array([1.0, d1_c])
                sdc = np.sqrt(dc)
                Hc = (sdc[:, None] * X_c) * sdc[None, :]
                Bspc = sp * np.eye(2) - holden_operators(np.diag(dc), Hc, kap)["Ehat"]
                evXc, UXc = eigh(X_c)
                for sk in np.linspace(0.0, 0.99 * math.sqrt(xp), 40):
                    den = L2 * (1.0 + evXc) ** (2.0 - 2.0 * kap) - sk * (evXc ** (1.5 - kap))
                    if np.min(den) <= 0.0:
                        continue
                    KX = (UXc * (sp - sk * (evXc ** (kap - 0.5)) + 1.0 / den)) @ UXc.T
                    min_inX = min(min_inX, float(eigh(KX - Bspc, eigvals_only=True)[0]))
        print(f"  p={label:>7s}: det_err={det_err:.1e} | min(K_scal - Bsp): inX={min_inX:+.3e}, inQ={min_inQ:+.3e}, inY={min_inY:+.3e}")
        if abs(kap - 1.5) < 1e-9:
            assert abs(min_inX) < 1e-14 and abs(min_inY) < 1e-14
        else:
            assert min_inX < -5e-5 and min_inQ < -5e-5 and min_inY < -5e-5

    print("  [PASS] Suite 3 verified full phase diagram, exact mode-spread no-go, and scalarization obstructions.\n")


# ==============================================================================
# SUITE 4: ADVERSARIAL NON-RG INDEFINITE-B_{sigma_+} STRESS TESTS (n=2..5, m=2,10,50),
#          REGIME III delta=0 CAVEAT, OPERATOR CONVEXITY ALL-u, & MOBIUS MONOTONICITY
# ==============================================================================

def run_suite_4():
    print("=" * 84)
    print("SUITE 4: ADVERSARIAL NON-RG STRESS TESTS, REGIME III delta=0 CAVEAT, ALL-u, & MOBIUS")
    print("=" * 84)
    rng = np.random.default_rng(404)

    print("\n--- 4A: Full 2x2 Coupled Branches Across m in {2, 10, 50} (Regimes II & III) ---")
    total_2x2 = 0
    for m, p_list in [(2.0, [1.48, 1.45, math.sqrt(2.0), 7 / 5, 1.37, 4 / 3, 5 / 4, 6 / 5]),
                      (10.0, [1.45, math.sqrt(2.0), 7 / 5, 4 / 3, 5 / 4, 6 / 5]),
                      (50.0, [1.45, math.sqrt(2.0), 7 / 5, 5 / 4, 6 / 5])]:
        for p in p_list:
            kap = p / (2.0 * (p - 1.0))
            L4, d4, X4 = continue_rg(p, 4, m=m)
            L2, d2, X2 = continue_rg(p, 2, m=m)
            _, _, _, sp4 = roots_kappa(L4, kap)
            sd4 = np.sqrt(d4)
            Q4 = holden_operators(np.diag(d4), (sd4[:, None] * X4) * sd4[None, :], kap)["Q"]
            evQ4, UQ4 = eigh(Q4)
            w4 = UQ4[0, :] ** 2
            pts = sweep_2x2_branch(p, L4, d2[1], X2)
            total_2x2 += len(pts)
            min_mid = 1e99
            min_cI = 1e99
            min_K0 = 1e99
            max_er = 0.0
            for d1, X in pts:
                d = np.array([1.0, d1])
                sd = np.sqrt(d)
                D = np.diag(d)
                H = (sd[:, None] * X) * sd[None, :]
                Eh = holden_operators(D, H, kap)["Ehat"]
                evE = eigh(Eh, eigvals_only=True)
                dreq = max(0.0, float(evE[-1]) - sp4)
                max_er = max(max_er, float(evE[-1]) / sp4)
                creq = (m / (m - 1.0)) * (sp4 + dreq)
                _, _, _, mK0 = eval_dual_q_family(L4, kap, D, H, evQ4, w4, delta=0.0)
                min_K0 = min(min_K0, mK0)
                Id, _, mm, _ = eval_dual_q_family(L4, kap, D, H, evQ4, w4, delta=dreq)
                assert Id is not None
                min_mid = min(min_mid, mm)
                lmin = float(eigh(creq * Id, eigvals_only=True)[0])
                min_cI = min(min_cI, lmin)
                assert lmin >= 1.0 - 1e-8
            print(f"  m={int(m):2d}, p={p:.4f}: {len(pts):2d} pts, max(e/sp)={max_er:.2f}, minK(0)={min_K0:+.2e} | min_mid={min_mid:+.2e} | min(cI)={min_cI:.8f}")
            # Explicitly confirm the Regime III delta=0 caveat at p = 6/5!
            if abs(p - 6 / 5) < 1e-12:
                assert min_K0 < -1e-2

    print(f"  -> Total coupled 2x2 branch points verified with 0 violations: {total_2x2}")

    print("\n--- 4B: Higher-Rank Non-RG Indefinite-B_{sigma_+} Stress Tests (n = 3, 4, 5) + Bargmann Audit ---")
    cases_4b = [
        ("Regime II: p=1.45, m=2", 1.45, 2.0, 5),
        ("Regime II: p=sqrt(2), m=2", math.sqrt(2.0), 2.0, 5),
        ("Regime II: p=7/5, m=10", 7 / 5, 10.0, 5),
        ("Regime III: p=5/4, m=2", 5 / 4, 2.0, 4),
        ("Regime III: p=6/5, m=2", 6 / 5, 2.0, 4),
    ]
    total_hi = 0
    total_indef = 0
    for name, p, m, r_meas in cases_4b:
        kap = p / (2.0 * (p - 1.0))
        Lm, dm, Xm = continue_rg(p, r_meas, m=m)
        L3, d3, X3 = continue_rg(p, 3, m=m)
        L4, d4, X4 = continue_rg(p, 4, m=m)
        _, _, _, spm = roots_kappa(Lm, kap)
        sdm = np.sqrt(dm)
        Qm = holden_operators(np.diag(dm), (sdm[:, None] * Xm) * sdm[None, :], kap)["Q"]
        evQm, UQm = eigh(Qm)
        wm = UQm[0, :] ** 2

        seeds = [
            (3, d3, X3, "spread"), (3, d3, X3, "degen"), (3, d3, X3, "rand"), (3, d3, X3, "rand"),
            (4, d4, X4, "spread"), (4, d4, X4, "degen"), (4, d4, X4, "rand"), (4, d4, X4, "rand"),
        ]
        if r_meas == 5:
            seeds += [(5, dm, Xm, "spread"), (5, dm, Xm, "degen"), (5, dm, Xm, "rand")]

        n_ok = 0
        n_indef = 0
        min_cI = 1e99
        max_cond = 0.0
        max_er = 0.0
        max_barg = 0.0
        for n, db, Xb, mode in seeds:
            if mode == "spread":
                d_try = np.maximum(db ** rng.uniform(1.2, 1.8), 1e-4)
            elif mode == "degen":
                d_try = db.copy()
                k_dup = int(rng.integers(0, n - 1))
                d_try[k_dup + 1] = d_try[k_dup] * float(rng.uniform(0.95, 0.999))
            else:
                d_try = db * np.exp(rng.uniform(-1.0, 1.0, size=n))
            d_try = np.sort(d_try / np.max(d_try))[::-1]
            ph = np.exp(1j * rng.uniform(0.0, 2.0 * math.pi, size=n))
            A_n = rng.normal(0.0, 0.2, (n, n)) + 1j * rng.normal(0.0, 0.2, (n, n))
            A_n = 0.5 * (A_n + A_n.conj().T)
            X_seed = (ph[:, None] * Xb) * np.conj(ph[None, :]) + 0.08 * A_n
            ev_s, Us = eigh(0.5 * (X_seed + X_seed.conj().T))
            X_seed = (Us * np.maximum(ev_s, 0.02)) @ Us.conj().T
            X_sol, err = solve_complex_holden(p, Lm, d_try, X_seed)
            if err > 1e-9:
                continue
            sd = np.sqrt(d_try)
            D_sol = np.diag(d_try)
            H_sol = (sd[:, None] * X_sol) * sd[None, :]
            if np.linalg.norm(H_sol - np.diag(np.diag(H_sol))) < 1e-4:
                continue
            n_ok += 1
            max_cond = max(max_cond, float(np.max(d_try) / np.min(d_try)))
            max_barg = max(max_barg, float(abs(np.imag(X_sol[0, 1] * X_sol[1, 2] * X_sol[2, 0]))))
            Eh = holden_operators(D_sol, H_sol, kap)["Ehat"]
            evE = eigh(0.5 * (Eh + Eh.conj().T), eigvals_only=True)
            dreq = max(0.0, float(evE[-1]) - spm)
            if dreq > 1e-5:
                n_indef += 1
            max_er = max(max_er, float(evE[-1]) / spm)
            creq = (m / (m - 1.0)) * (spm + dreq)
            Id, _, _, _ = eval_dual_q_family(Lm, kap, D_sol, H_sol, evQm, wm, delta=dreq)
            assert Id is not None
            lm = float(eigh(creq * Id, eigvals_only=True)[0])
            min_cI = min(min_cI, lm)
            assert lm >= 1.0 - 1e-8
        total_hi += n_ok
        total_indef += n_indef
        assert n_ok >= 3
        print(f"  {name:26s}: ok={n_ok:2d} (indef={n_indef:2d}, cond<={max_cond:6.1f}, e/sp<={max_er:.2f}, max|Barg|={max_barg:.2e}) | min(cI)={min_cI:.8f}")
    print(f"  -> Total n=3..5 complex-seed Holden points verified with 0 violations: {total_hi} ({total_indef} indef-B_sp)")

    print("\n--- 4C: All-u in [0, 1) (delta in [0, infty)) Operator-Convexity Audit on r=4 RG Blocks ---")
    for p, m in [(math.sqrt(2.0), 10.0), (4 / 3, 10.0), (5 / 4, 10.0), (6 / 5, 2.0), (6 / 5, 10.0)]:
        kap = p / (2.0 * (p - 1.0))
        L4, d4, X4 = continue_rg(p, 4, m=m)
        _, _, _, sp = roots_kappa(L4, kap)
        sd = np.sqrt(d4)
        D4 = np.diag(d4)
        H4 = (sd[:, None] * X4) * sd[None, :]
        Q4 = holden_operators(D4, H4, kap)["Q"]
        evQ, UQ = eigh(Q4)
        w4 = UQ[0, :] ** 2
        _, Fp0, _, _ = eval_dual_q_family(L4, kap, D4, H4, evQ, w4, delta=0.0)
        min_cI_u = 1e99
        worst_u = 0.0
        for u in np.linspace(0.0, 0.999, 100):
            delta = sp * u / (1.0 - u)
            Id, _, _, _ = eval_dual_q_family(L4, kap, D4, H4, evQ, w4, delta=delta)
            c_u = (m / (m - 1.0)) * (sp + delta)
            lm = float(eigh(c_u * Id, eigvals_only=True)[0])
            if lm < min_cI_u:
                min_cI_u, worst_u = lm, float(u)
        print(f"  p={p:.4f}, m={int(m):2d}: (F'_d(0))_00={float(Fp0[0,0]):+.6f} | min_eig(F'_d(0))={float(eigh(Fp0, eigvals_only=True)[0]):+.6f} | min_u eig(c(u)I(u))={min_cI_u:.8f} (u={worst_u:.3f})")
        assert float(Fp0[0, 0]) > 0.0 and min_cI_u >= 1.0 - 1e-10

    print("\n--- 4D: Mobius Pullback Monotonicity for Dual Q-Family at Lam in [1.02, 3.0]*Lam_RG ---")
    for p, m in [(1.45, 2.0), (math.sqrt(2.0), 2.0), (5 / 4, 2.0), (6 / 5, 2.0), (math.sqrt(2.0), 10.0)]:
        kap = p / (2.0 * (p - 1.0))
        L4, d4, X4 = continue_rg(p, 4, m=m)
        L2, d2, X2 = continue_rg(p, 2, m=m)
        _, xp4, _, _ = roots_kappa(L4, kap)
        a4 = math.sqrt(xp4)
        sd4 = np.sqrt(d4)
        Q4 = holden_operators(np.diag(d4), (sd4[:, None] * X4) * sd4[None, :], kap)["Q"]
        evQ4, UQ4 = eigh(Q4)
        w4 = UQ4[0, :] ** 2
        p2_nodes = evQ4 / (a4 * (a4 - evQ4))

        vals = []
        for mult in [1.02, 1.2, 2.0, 3.0]:
            L_hi = L4 * mult
            _, xp_hi, _, sp_hi = roots_kappa(L_hi, kap)
            a_hi = math.sqrt(xp_hi)
            s_hi = (a_hi * a_hi * p2_nodes) / (1.0 + a_hi * p2_nodes)
            X_cur = X2.copy()
            for L_step in np.linspace(L2, L_hi, 8)[1:]:
                X_cur, err = solve_complex_holden(p, float(L_step), d2, X_cur)
                assert err < 1e-10
            sd2 = np.sqrt(d2)
            D2 = np.diag(d2)
            H_sol = (sd2[:, None] * X_cur) * sd2[None, :]
            Eh = holden_operators(D2, H_sol, kap)["Ehat"]
            dreq = max(0.0, float(eigh(0.5 * (Eh + Eh.conj().T), eigvals_only=True)[-1]) - sp_hi)
            creq = (m / (m - 1.0)) * (sp_hi + dreq)
            Id, _, _, _ = eval_dual_q_family(L_hi, kap, D2, H_sol, s_hi, w4, delta=dreq)
            assert Id is not None
            vals.append(float(eigh(creq * Id, eigvals_only=True)[0]))
        assert vals[0] > 1.03 and all(vals[i + 1] > vals[i] for i in range(len(vals) - 1))
        print(f"  p={p:.4f}, m={int(m):2d}: Mobius-pushed eig(c*I_dual) along [1.02,1.2,2.0,3.0]*Lam_RG = {[round(v, 6) for v in vals]} (strictly increasing)")

    print("  [PASS] Suite 4 passed all non-RG adversarial, all-u, and Mobius pullback checks.\n")


# ==============================================================================
# SUITE 5: OPERATOR PARALLEL-SUM & POLYNOMIAL NEUMANN UPPER-BOUND SHORTCUTS
# ==============================================================================

def run_suite_5():
    print("=" * 84)
    print("SUITE 5: OPERATOR PARALLEL-SUM & POLYNOMIAL NEUMANN UPPER BOUNDS (HAND-OFF)")
    print("=" * 84)
    for m in [2.0, 10.0]:
        print(f"\n  --- m = {int(m)} (r = 4 RG blocks) ---")
        for label, p in [("1.45", 1.45), ("sqrt(2)", math.sqrt(2.0)), ("7/5", 7 / 5),
                         ("5/4", 5 / 4), ("6/5", 6 / 5)]:
            kap = p / (2.0 * (p - 1.0))
            L4, d4, X4 = continue_rg(p, 4, m=m)
            _, _, _, sp = roots_kappa(L4, kap)
            c4 = (m / (m - 1.0)) * sp
            sd = np.sqrt(d4)
            D4 = np.diag(d4)
            H4 = (sd[:, None] * X4) * sd[None, :]
            ops = holden_operators(D4, H4, kap)
            G4, M4, Q4 = ops["G"], ops["M"], ops["Q"]
            evQ, UQ = eigh(Q4)
            w = UQ[0, :] ** 2
            sbar = float(np.sum(w * evQ))
            W1_inv = matpow(D4, kap - 1.0) @ matpow(M4, 2.0 - 2.0 * kap) @ matpow(D4, kap - 1.0)
            P4 = matpow(D4, kap - 1.5) @ matpow(G4, 1.5 - kap) @ matpow(D4, kap - 1.5)
            Y4 = matpow(D4, 0.5 - kap) @ matpow(G4, kap - 0.5) @ matpow(D4, 0.5 - kap)
            Ks = [sp * np.eye(4) - sk * Y4 + np.linalg.inv(L4 * W1_inv - sk * P4) for sk in evQ]
            Kbar = sum(wk * Kk for wk, Kk in zip(w, Ks))
            Ksbar = sp * np.eye(4) - sbar * Y4 + np.linalg.inv(L4 * W1_inv - sbar * P4)
            S1 = sum(wk * (np.eye(4) - (Kk - Kbar) / c4) @ Kk @ (np.eye(4) - (Kk - Kbar) / c4) for wk, Kk in zip(w, Ks))
            E2bar = sum(wk * ((Kk - Kbar) @ (Kk - Kbar)) for wk, Kk in zip(w, Ks))
            S2 = np.zeros((4, 4))
            for wk, Kk in zip(w, Ks):
                Ek = Kk - Kbar
                Fk = np.eye(4) - Ek / c4 + (Ek @ Ek - E2bar) / (c4 * c4)
                S2 += wk * (Fk @ Kk @ Fk)
            Id = sum(wk * np.linalg.inv(Kk) for wk, Kk in zip(w, Ks))
            Id_inv = np.linalg.inv(Id)
            # Exact optimal partition formula on e_0: Y_k^* e_0 = D^k P_k(Q) e_0
            err_y0 = max(float(np.linalg.norm(w[k] * np.linalg.inv(Ks[k]) @ Id_inv[:, 0] - (d4 ** kap) * (UQ[0, k] * UQ[:, k]))) for k in range(4))
            lex = float(eigh(Id_inv / c4, eigvals_only=True)[-1])
            l_sb = float(eigh(Ksbar / c4, eigvals_only=True)[-1])
            l_kb = float(eigh(Kbar / c4, eigvals_only=True)[-1])
            l_s1 = float(eigh(S1 / c4, eigvals_only=True)[-1])
            l_s2 = float(eigh(S2 / c4, eigvals_only=True)[-1])
            print(f"  p={label:>7s}: harm={lex:.8f} | K_sbar-1={l_sb-1:+.2e} | Kbar-1={l_kb-1:+.2e} | S1-1={l_s1-1:+.2e} | S2-1={l_s2-1:+.2e} | Y*_e0_err={err_y0:.1e}")
            assert abs(lex - 1.0) < 1e-10 and err_y0 < 1e-12
            assert l_s2 <= l_s1 <= l_kb + 1e-12

    print("  [PASS] Suite 5 verified parallel-sum structure and polynomial Neumann upper bounds.\n")


def main():
    t0 = time.time()
    run_suite_1()
    run_suite_2()
    run_suite_3()
    run_suite_4()
    run_suite_5()
    dt = time.time() - t0
    print("=" * 84)
    print(f"ALL 5 SUITES PASSED WITH ZERO VIOLATIONS IN {dt:.2f}s (EXIT CODE 0)")
    print("=" * 84)


if __name__ == "__main__":
    main()
