r"""
adversarial_iop_stress.py
=========================
Adversarial High-Dimensional Stress-Test & Counterexample Audit Suite for General-p
Operator-Antitone Certificates in Open Problem MI-20 (1 < p < 2, m >= 2).

Tests BOTH:
  (A) Primal X-Kernel Operator Integral I_primal (#107, nc-operator-prover):
        K_op,x^(p)(D, H) = sig_+ I - x Z + gam_x (T1 - gam_x T2)^{-1},   gam_x = (1 + x) / Lam,
        I_primal(delta)  = int (K_op,x^(p)(D, H) + delta I)^{-1} d nu(x),  nu = spec_{e_0}(X_r)
  (B) Dual Q-Kernel Operator Integral I_dual (#119, general-p-theory):
        Ktilde_op,s^(p)(D, H) = sig_+ I - s Y + (Lam W1^{-1} - s P)^{-1},
        I_dual(delta)         = int (Ktilde_op,s^(p)(D, H) + delta I)^{-1} d mu(s), mu = spec_{e_0}(Q_r)
  (C) Continuous Dual theta-Family (#119):
        P_th = D^{k-3/2-th} G^{3/2-k+th} D^{k-3/2-th},
        Y_th = D^{1/2-k} G^{k-1} D^{-th} G^{3/2-k+th} D^{-th} G^{k-1} D^{1/2-k}
  (D) Constant-Weight Universal 2-Square Candidate U_{3/4} = (3/4) I_primal + (1/4) I_dual (#119).

Dependencies: Python stdlib + numpy, scipy, mpmath ONLY (zero external scratch imports).
Strict write-boundary: reads/writes NOTHING in /Users/marcio/Downloads/Core Rank.

Suites:
  Suite 1 — Exact U(3)-Complex 1-Square Identities & High-Rank RG Spectra (r = 2..8, m = 2..200)
            + Exact Finite-Rank Discretization Gap Separation (nu_2/mu_2 on X_8 at Lam_8).
  Suite 2 — 50-Digit mpmath Certified Counterexamples & Exact Slope-Ratio + Fixed-m Mode-Spread
            No-Go Theorem for Constant-Weight U_{3/4} = (3/4) I_primal + (1/4) I_dual (breaks on
            BOTH sides of p = 3/2!) + Dual theta-Family 1-Square Identity & Unique theta=0 Tangency.
  Suite 3 — Domain Positivity Audit Across All 3 Regimes (Non-Holden Catastrophic Failure vs
            Holden Unconditional Survival Matching #119's Hansen Bound rho <= x_+/(1+x_+)).
  Suite 4 — High-Dimensional (n = 3, 4, 5, 6, 8) Adversarial Nelder-Mead Minimization,
            Multi-Branch (1, n-1) & (2, 1) Irreducible Solutions, Forced Strongly-Indefinite B_{sig_+}
            (dreq / sig_+ up to 2.265) at Large m = 50, 200, delta_extra >= 0 Sweeps, n = 8 > r = 4
            at Lambda_UB = Lambda_8 * (1 + 1e-4), & 50-Digit mpmath Verification of Tightest Margins.
  Suite 5 — Coupled Multi-Block Holden Solutions (D, H_1, ..., H_m) with Exact sum E_j = 0
            (Complex Hermitian Kubo-Ando Multi-Block Tuples across N = 4, 6 and m = 2, 3, verifying
            Lam_KA <= Lam_RG, non-commuting ||[H_a, H_b]|| > 1e-3, and U(N)-rotated survival of all m
            colors polished onto the exact Holden manifold at Lam_UB = Lam_RG * (1 + 1e-4)).
  Suite 6 — Complex Non-Real Single-Block Holden Rigidity Investigation (Exact 4-Line Analytic
            Proof at p = 4/3 for n = 3, Multi-Start Gauge-Fixed Complex Searches for n = 3, 4,
            and Imaginary Jacobian SVDs Showing Exact (n - 1) Gauge Zeros + Nonzero Physical Modes).
"""

import time
import numpy as np
from scipy.linalg import eigh
from scipy.optimize import brentq, root, least_squares, minimize
import mpmath as mp

mp.mp.dps = 50
t_start = time.time()


# ==============================================================================
# Core Numeric & Exact-Precision Primitives
# ==============================================================================

def matpow(A, alpha):
    """Exact Hermitian matrix power A^alpha for A > 0 (real or complex)."""
    Ah = 0.5 * (A + A.conj().T)
    w, V = eigh(Ah)
    if np.min(w) <= 1e-300:
        raise ValueError(f"matpow received non-positive eigenvalue {np.min(w)}")
    return (V * (w ** alpha)) @ V.conj().T


def roots_kappa(Lam, kappa):
    """Exact scalar Holden roots x_- < (k-1)/k < x_+ of (1+x)^{2k-1} = Lam x^{k-1} and charges sig_-, sig_+."""
    t_min = np.log((kappa - 1.0) / kappa)
    logL = np.log(Lam)
    fn = lambda t: (2.0 * kappa - 1.0) * np.logaddexp(0.0, t) - (kappa - 1.0) * t - logL
    lo, hi = t_min - 1.0, t_min + 1.0
    while fn(lo) < 0.0:
        lo -= 20.0
    while fn(hi) < 0.0:
        hi += 20.0
    xm = float(np.exp(brentq(fn, lo, t_min, xtol=1e-15, rtol=1e-15)))
    xp = float(np.exp(brentq(fn, t_min, hi, xtol=1e-15, rtol=1e-15)))
    return xm, xp, (xm ** (kappa - 1.0)) * (xm - 1.0), (xp ** (kappa - 1.0)) * (xp - 1.0)


def scalar_1x1(kappa, m=2):
    """Exact 1x1 Holden threshold Lam_1(kappa, m)."""
    Lam0 = 2.0 ** (2.0 * kappa - 1.0)
    hi = max(Lam0 * 2.0, 2.0 * np.sqrt(m) + 4.0)
    while roots_kappa(hi, kappa)[3] + (m - 1.0) * roots_kappa(hi, kappa)[2] < 0.0:
        hi *= 2.0
    return float(brentq(
        lambda L: roots_kappa(L, kappa)[3] + (m - 1.0) * roots_kappa(L, kappa)[2],
        Lam0 + 1e-12, hi, xtol=1e-15, rtol=1e-15
    ))


def solve_rg_p32_Q(r_target):
    """Build exact rank-r RG anchors at p = 3/2, m = 2 up to r = r_target in Q-coordinates."""
    Lam1 = scalar_1x1(1.5, 2)
    xm1, _, _, _ = roots_kappa(Lam1, 1.5)
    Lam = Lam1 + 5e-4
    ds = np.array([1.0, 0.075])
    Q = np.array([[np.sqrt(xm1), -0.15], [-0.15, 0.50]])

    def solve_k(rk, L_in, d_in, Q_in):
        triu = np.triu_indices(rk)
        x0 = np.concatenate([[L_in], np.log(d_in[1:]), Q_in[triu]])

        def unpack(x):
            L = x[0]
            dd = np.concatenate([[1.0], np.exp(x[1:rk])])
            QQ = np.zeros((rk, rk))
            QQ[triu] = x[rk:]
            QQ = QQ + QQ.T - np.diag(np.diag(QQ))
            return L, dd, QQ

        def res(x):
            L, dd, QQ = unpack(x)
            _, _, _, sp = roots_kappa(L, 1.5)
            D = np.diag(dd)
            H = QQ @ D @ QQ
            R1 = (D + H) @ (D + H) - L * D @ QQ @ D
            F = QQ @ D @ QQ @ D @ QQ - D @ QQ @ D
            R2 = F - np.diag(np.concatenate([[-sp], sp * (dd[1:] ** 2)]))
            w = 1.0 / np.outer(dd, dd)
            return np.concatenate([(R1 * w)[triu], (R2 * w)[triu]])

        sol = least_squares(res, x0, xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=8000)
        L, dd, QQ = unpack(sol.x)
        assert float(np.linalg.norm(sol.fun)) < 1e-12
        return L, dd, QQ

    out = {}
    Lam, ds, Q = solve_k(2, Lam, ds, Q)
    for rk in range(2, r_target + 1):
        if rk > 2:
            ratio = ds[-1] / ds[-2]
            ds_n = np.concatenate([ds, [ds[-1] * max(0.15, ratio * 0.9)]])
            Q_n = np.zeros((rk, rk))
            Q_n[:rk - 1, :rk - 1] = Q
            _, xp_c, _, _ = roots_kappa(Lam, 1.5)
            Q_n[rk - 1, rk - 1] = min(0.97 * np.sqrt(xp_c), Q[-1, -1] + 0.10)
            Q_n[:rk - 1, rk - 1] = -0.015 * (0.35 ** np.arange(rk - 1)[::-1])
            Q_n[rk - 1, :rk - 1] = Q_n[:rk - 1, rk - 1]
            Lam, ds, Q = solve_k(rk, Lam, ds_n, Q_n)
        H = Q @ np.diag(ds) @ Q
        X = (ds ** (-0.5))[:, None] * H * (ds ** (-0.5))[None, :]
        out[rk] = (Lam, ds, X)
    return out


def solve_rg_square(p, m, r_cur, Lam_init, d_init, X_init):
    """Solve rank-r RG fixed-point system for any 1 < p < 2, any m >= 2."""
    kappa = p / (2.0 * (p - 1.0))
    triu = np.triu_indices(r_cur)
    L0 = 2.0 ** (2.0 * kappa - 1.0)
    w0, V0 = eigh(0.5 * (X_init + X_init.T))
    S0 = (V0 * np.log(np.maximum(w0, 1e-18))) @ V0.T
    x0 = np.concatenate([[np.log(max(Lam_init - L0, 1e-14))], np.log(d_init[1:]), S0[triu]])

    def unpack(x):
        L = L0 + np.exp(np.clip(x[0], -45.0, 30.0))
        dd = np.concatenate([[1.0], np.exp(np.clip(x[1:r_cur], -50.0, 5.0))])
        S = np.zeros((r_cur, r_cur))
        S[triu] = np.clip(x[r_cur:], -32.0, 12.0)
        S = S + S.T - np.diag(np.diag(S))
        w, V = eigh(S)
        return L, dd, (V * np.exp(w)) @ V.T

    def res(x):
        try:
            L, dd, X = unpack(x)
            _, _, _, sp = roots_kappa(L, kappa)
            sD = np.sqrt(dd)
            D = np.diag(dd)
            H = (sD[:, None] * X) * sD[None, :]
            M = D + H
            G = (sD[:, None] * H) * sD[None, :]
            Ds = dd ** (-kappa + 0.5)
            Z = (dd ** (1.0 - kappa))[:, None] * matpow(G, kappa - 1.0) * (dd ** (1.0 - kappa))[None, :]
            R1 = (Ds[:, None] * matpow(M, 2.0 * kappa - 1.0) * Ds[None, :]) - L * Z
            Ehat = ((dd ** (-kappa))[:, None] * matpow(G, kappa) * (dd ** (-kappa))[None, :]) - Z
            target_diag = np.concatenate([[-sp / (m - 1.0)], np.full(r_cur - 1, sp)])
            return np.concatenate([R1[triu], np.diag(Ehat) - target_diag])
        except Exception:
            return np.full(len(x0), 1e3)

    sol = root(res, x0, method="hybr", tol=1e-14)
    rnorm = float(np.linalg.norm(res(sol.x)))
    if rnorm > 1e-10:
        sol_ls = least_squares(res, sol.x if rnorm < float(np.linalg.norm(res(x0))) else x0, xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=4000)
        if float(np.linalg.norm(sol_ls.fun)) < rnorm:
            sol = sol_ls
            rnorm = float(np.linalg.norm(sol_ls.fun))
    L, dd, X = unpack(sol.x)
    sD = np.sqrt(dd)
    H = (sD[:, None] * X) * sD[None, :]
    G = (sD[:, None] * H) * sD[None, :]
    Z = (dd ** (1.0 - kappa))[:, None] * matpow(G, kappa - 1.0) * (dd ** (1.0 - kappa))[None, :]
    Ehat = ((dd ** (-kappa))[:, None] * matpow(G, kappa) * (dd ** (-kappa))[None, :]) - Z
    off_err = float(np.linalg.norm(Ehat - np.diag(np.diag(Ehat))))
    return L, dd, X, rnorm, off_err


def continue_rg(p_target, m_target, r_cur, rg_p32_map):
    """Adaptive step-halving continuation of rank-r RG block from (p=3/2, m=2) to (p_target, m_target)."""
    L, d, X = rg_p32_map[r_cur]
    L1_prev = scalar_1x1(1.5, 2)
    err = oe = 0.0
    if abs(p_target - 1.5) > 1e-12:
        p_cur = 1.5
        step = (p_target - 1.5) / (45.0 if (p_target >= 1.82 or p_target <= 1.15) else (30.0 if r_cur >= 7 else 20.0))
        while abs(p_target - p_cur) > 1e-12:
            p_next = p_target if abs(p_target - p_cur) <= abs(step) * 1.01 else p_cur + step
            L1 = scalar_1x1(p_next / (2.0 * (p_next - 1.0)), 2)
            L_guess = L1 * max(1.000001, L / L1_prev)
            Ln, dn, Xn, en, oen = solve_rg_square(p_next, 2, r_cur, L_guess, d, X)
            if en < 1e-9 and oen < 1e-9:
                p_cur, L, d, X, err, oe, L1_prev = p_next, Ln, dn, Xn, en, oen, L1
            else:
                step *= 0.5
                assert abs(step) > 1e-5, f"Adaptive p-continuation stalled at p={p_cur:.6f} -> {p_target} (r={r_cur})"
    if m_target > 2:
        kap = p_target / (2.0 * (p_target - 1.0))
        log_m_cur = np.log(2.0)
        log_m_tgt = np.log(float(m_target))
        step = (log_m_tgt - log_m_cur) / (45.0 if m_target >= 100 else 28.0)
        while log_m_tgt - log_m_cur > 1e-12:
            log_m_next = log_m_tgt if (log_m_tgt - log_m_cur) <= step * 1.01 else log_m_cur + step
            mm = float(np.exp(log_m_next))
            L1 = scalar_1x1(kap, mm)
            L_guess = L1 * max(1.000001, L / L1_prev)
            Ln, dn, Xn, en, oen = solve_rg_square(p_target, mm, r_cur, L_guess, d, X)
            if en < 1e-9 and oen < 1e-9:
                log_m_cur, L, d, X, err, oe, L1_prev = log_m_next, Ln, dn, Xn, en, oen, L1
            else:
                step *= 0.5
                assert step > 1e-5, f"Adaptive m-continuation stalled at m={np.exp(log_m_cur):.3f} -> {m_target} (p={p_target}, r={r_cur})"
    return L, d, X, err, oe


def extract_rg_measures(dd, X):
    """Extract Primal measure nu = spec_{e_0}(X) and Dual measure mu = spec_{e_0}(Q)."""
    sD = np.sqrt(dd)
    H = (sD[:, None] * X) * sD[None, :]
    G = (sD[:, None] * H) * sD[None, :]
    Q = (dd ** (-0.5))[:, None] * matpow(G, 0.5) * (dd ** (-0.5))[None, :]
    x_nu, Vx = eigh(0.5 * (X + X.T))
    w_nu = Vx[0, :] ** 2
    s_mu, Vq = eigh(0.5 * (Q + Q.T))
    w_mu = Vq[0, :] ** 2
    return x_nu, w_nu, s_mu, w_mu


def solve_holden_real(dd, X_init, Lam, kappa):
    """Solve real symmetric n x n Holden equation D^{-k+1/2} M^{2k-1} D^{-k+1/2} = Lam Z."""
    n = len(dd)
    triu = np.triu_indices(n)
    sD = np.sqrt(dd)
    D = np.diag(dd)
    Ds = dd ** (-kappa + 0.5)
    w0, V0 = eigh(0.5 * (X_init + X_init.T))
    S0 = (V0 * np.log(np.maximum(w0, 1e-18))) @ V0.T

    def res(x):
        try:
            S = np.zeros((n, n))
            S[triu] = np.clip(x, -30.0, 12.0)
            S = S + S.T - np.diag(np.diag(S))
            w, V = eigh(S)
            X = (V * np.exp(w)) @ V.T
            H = (sD[:, None] * X) * sD[None, :]
            M = D + H
            G = (sD[:, None] * H) * sD[None, :]
            Z = (dd ** (1.0 - kappa))[:, None] * matpow(G, kappa - 1.0) * (dd ** (1.0 - kappa))[None, :]
            R = (Ds[:, None] * matpow(M, 2.0 * kappa - 1.0) * Ds[None, :]) - Lam * Z
            return R[triu]
        except Exception:
            return np.full(len(triu[0]), 1e3)

    sol = root(res, S0[triu], method="hybr", tol=1e-13)
    S = np.zeros((n, n))
    S[triu] = np.clip(sol.x, -30.0, 12.0)
    S = S + S.T - np.diag(np.diag(S))
    w, V = eigh(S)
    X = (V * np.exp(w)) @ V.T
    return X, float(np.linalg.norm(res(sol.x)))


def eval_primal_dual_general(D, H, Lam, kappa, m, x_nu, w_nu, s_mu, w_mu, delta_extra=0.0):
    """
    Evaluate BOTH Primal X-kernel (#107) and Dual Q-kernel (#119) operator integrals
    on arbitrary (possibly complex Hermitian, non-diagonal) (D, H) > 0.
    Returns dict with eigs_P, eigs_D, rho_primal_xp, rho_dual_sp, dreq, sp, holden_err, evals_E.
    """
    _, xp, _, sp = roots_kappa(Lam, kappa)
    n = D.shape[0]
    Dh = matpow(D, 0.5)
    M = D + H
    G = Dh @ H @ Dh
    Dm_kh = matpow(D, -kappa + 0.5)
    Dm_k = matpow(D, -kappa)
    D1mk = matpow(D, 1.0 - kappa)

    Z = D1mk @ matpow(G, kappa - 1.0) @ D1mk
    holden_err = float(np.linalg.norm(Dm_kh @ matpow(M, 2.0 * kappa - 1.0) @ Dm_kh - Lam * Z))
    Ehat = Dm_k @ matpow(G, kappa) @ Dm_k - Z
    evals_E = np.linalg.eigvalsh(0.5 * (Ehat + Ehat.conj().T))
    dreq = max(0.0, float(evals_E[-1]) - sp)
    delta = dreq + delta_extra
    c = (m / (m - 1.0)) * (sp + delta)

    # Primal operators (#107)
    Dk32 = matpow(D, kappa - 1.5)
    Dk2 = matpow(D, kappa - 2.0)
    T1 = Dk32 @ matpow(M, 3.0 - 2.0 * kappa) @ Dk32
    T2 = Dk2 @ matpow(G, 2.0 - kappa) @ Dk2
    T1mh = matpow(T1, -0.5)
    g_xp = (1.0 + xp) / Lam
    Sp_mat = T1mh @ T2 @ T1mh
    rho_p = g_xp * float(np.max(np.linalg.eigvalsh(0.5 * (Sp_mat + Sp_mat.conj().T))))

    # Dual operators (#119)
    D05mk = matpow(D, 0.5 - kappa)
    Dkm1 = matpow(D, kappa - 1.0)
    Y = D05mk @ matpow(G, kappa - 0.5) @ D05mk
    W1inv = Dkm1 @ matpow(M, 2.0 - 2.0 * kappa) @ Dkm1
    P = Dk32 @ matpow(G, 1.5 - kappa) @ Dk32
    W1h = matpow(Lam * W1inv, -0.5)
    Sd_mat = W1h @ P @ W1h
    rho_d = float(np.sqrt(xp)) * float(np.max(np.linalg.eigvalsh(0.5 * (Sd_mat + Sd_mat.conj().T))))

    dtype = np.complex128 if (np.iscomplexobj(D) or np.iscomplexobj(H)) else np.float64
    Ip = np.zeros((n, n), dtype=dtype)
    for xk, wk in zip(x_nu, w_nu):
        g = (1.0 + xk) / Lam
        mid = T1 - g * T2
        if float(np.min(np.linalg.eigvalsh(0.5 * (mid + mid.conj().T)))) <= 1e-14:
            return {"ok": False, "rho_p": rho_p, "rho_d": rho_d, "dreq": dreq, "sp": sp, "holden_err": holden_err}
        Kd = (sp + delta) * np.eye(n, dtype=dtype) - xk * Z + g * np.linalg.inv(mid)
        Ip += wk * np.linalg.inv(Kd)

    Id = np.zeros((n, n), dtype=dtype)
    for sk, wk in zip(s_mu, w_mu):
        mid = Lam * W1inv - sk * P
        if float(np.min(np.linalg.eigvalsh(0.5 * (mid + mid.conj().T)))) <= 1e-14:
            return {"ok": False, "rho_p": rho_p, "rho_d": rho_d, "dreq": dreq, "sp": sp, "holden_err": holden_err}
        Kd = (sp + delta) * np.eye(n, dtype=dtype) - sk * Y + np.linalg.inv(mid)
        Id += wk * np.linalg.inv(Kd)

    cIp = 0.5 * (c * Ip + (c * Ip).conj().T)
    cId = 0.5 * (c * Id + (c * Id).conj().T)
    eP = np.linalg.eigvalsh(cIp)
    eD = np.linalg.eigvalsh(cId)
    return {
        "ok": True, "eP": eP, "eD": eD, "cIp": cIp, "cId": cId, "rho_p": rho_p, "rho_d": rho_d,
        "dreq": dreq, "sp": sp, "xp": xp, "holden_err": holden_err, "evals_E": evals_E
    }


def eval_primal_dual_diag(dd, X, Lam, kappa, m, x_nu, w_nu, s_mu, w_mu, delta_extra=0.0):
    """Fast diagonal-D wrapper around eval_primal_dual_general."""
    sD = np.sqrt(dd)
    D = np.diag(dd)
    H = (sD[:, None] * X) * sD[None, :]
    return eval_primal_dual_general(D, H, Lam, kappa, m, x_nu, w_nu, s_mu, w_mu, delta_extra)


# ==============================================================================
# 50-Digit mpmath Helpers (2x2 Exact Symmetric Certification)
# ==============================================================================

def mp_roots(Lam, kappa):
    t_min = mp.log((kappa - 1) / kappa)
    logL = mp.log(Lam)
    fn = lambda t: (2 * kappa - 1) * mp.log(1 + mp.exp(t)) - (kappa - 1) * t - logL
    lo = t_min - 1
    while fn(lo) < 0:
        lo -= 10
    hi = t_min + 1
    while fn(hi) < 0:
        hi += 10
    tm = mp.findroot(fn, (lo, t_min), solver="anderson")
    tp = mp.findroot(fn, (t_min, hi), solver="anderson")
    xm = mp.exp(tm)
    xp = mp.exp(tp)
    return xm, xp, xm ** (kappa - 1) * (xm - 1), xp ** (kappa - 1) * (xp - 1)


def mp_matpow2(A, alpha):
    a, b, d = A[0, 0], A[0, 1], A[1, 1]
    tr = a + d
    diff = a - d
    disc = mp.sqrt(diff * diff + 4 * b * b)
    l1 = (tr - disc) / 2
    l2 = (tr + disc) / 2
    if abs(b) == 0:
        return mp.matrix([[a ** alpha, 0], [0, d ** alpha]])
    v1x, v1y = b, l1 - a
    n1 = mp.sqrt(v1x * v1x + v1y * v1y)
    v1x /= n1
    v1y /= n1
    v2x, v2y = -v1y, v1x
    p1, p2 = l1 ** alpha, l2 ** alpha
    return mp.matrix([
        [p1 * v1x * v1x + p2 * v2x * v2x, p1 * v1x * v1y + p2 * v2x * v2y],
        [p1 * v1x * v1y + p2 * v2x * v2y, p1 * v1y * v1y + p2 * v2y * v2y],
    ])


def mp_inv2(A):
    det = A[0, 0] * A[1, 1] - A[0, 1] * A[1, 0]
    return mp.matrix([[A[1, 1] / det, -A[0, 1] / det], [-A[1, 0] / det, A[0, 0] / det]])


def mp_eigs2(A):
    a, b, d = A[0, 0], A[0, 1], A[1, 1]
    tr = a + d
    diff = a - d
    disc = mp.sqrt(diff * diff + 4 * b * b)
    l1 = (tr - disc) / 2
    l2 = (tr + disc) / 2
    v1x, v1y = b, l1 - a
    n1 = mp.sqrt(v1x * v1x + v1y * v1y)
    if n1 == 0:
        return [a, d], [mp.mpf(1), mp.mpf(0)]
    v1x /= n1
    v1y /= n1
    v2x = -v1y
    return [l1, l2], [v1x * v1x, v2x * v2x]


def mp_matpow_n(A, alpha):
    """Exact n x n real symmetric matrix power in 50-dps mpmath via mp.eigh."""
    ev, Q = mp.eigh(A)
    n = A.rows
    Qp = mp.matrix(n, n)
    for j in range(n):
        assert ev[j] > 0, f"mp_matpow_n non-pos eig {ev[j]}"
        val = ev[j] ** alpha
        for i in range(n):
            Qp[i, j] = Q[i, j] * val
    return Qp * Q.T


# Build master RG p=3/2 anchors up to r = 8 once!
rg_p32 = solve_rg_p32_Q(8)
rng = np.random.default_rng(20261128)


# ==============================================================================
# SUITE 1: COMPLEX 1-SQUARE IDENTITIES, HIGH-RANK RG SPECTRA (r = 2..8, m = 2..200),
#          AND EXACT FINITE-RANK GAP SEPARATION
# ==============================================================================
print("=" * 100)
print("SUITE 1: EXACT 1-SQUARE IDENTITIES, HIGH-RANK RG SPECTRA (r = 2..8), & FINITE-RANK SEPARATION")
print("=" * 100)

print("\n[1A] Independent Complex-Rotated 3x3 Verification of Primal (#107) & Dual (#119) 1-Square Identities:")
for lbl, p_val in [("5/3", 5.0 / 3.0), ("7/5", 1.4), ("sqrt2", np.sqrt(2.0)), ("5/4", 1.25), ("6/5", 1.2)]:
    kap = p_val / (2.0 * (p_val - 1.0))
    L, d, X, err, oe = continue_rg(p_val, 2, 3, rg_p32)
    assert err < 1e-12 and oe < 1e-12
    _, _, _, sp = roots_kappa(L, kap)
    x_nu, w_nu, s_mu, w_mu = extract_rg_measures(d, X)

    # Rotate by random complex U in U(3)
    Zc = rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3))
    Uc, _ = np.linalg.qr(Zc)
    sD = np.sqrt(d)
    H_diag = (sD[:, None] * X) * sD[None, :]
    D = Uc @ np.diag(d) @ Uc.conj().T
    H = Uc @ H_diag @ Uc.conj().T
    Dh = matpow(D, 0.5)
    M = D + H
    G = Dh @ H @ Dh

    # Primal 1-square identity (#107)
    Z_p = matpow(D, 1.0 - kap) @ matpow(G, kap - 1.0) @ matpow(D, 1.0 - kap)
    Ehat = matpow(D, -kap) @ matpow(G, kap) @ matpow(D, -kap) - Z_p
    B_sig = sp * np.eye(3) - Ehat
    T1 = matpow(D, kap - 1.5) @ matpow(M, 3.0 - 2.0 * kap) @ matpow(D, kap - 1.5)
    T2 = matpow(D, kap - 2.0) @ matpow(G, 2.0 - kap) @ matpow(D, kap - 2.0)
    V_p = matpow(D, -kap) @ matpow(G, 0.5 * kap)
    A_p = matpow(D, 1.5 - kap) @ matpow(M, kap - 1.5)
    B_p = matpow(G, 1.0 - 0.5 * kap) @ matpow(D, -0.5) @ matpow(M, kap - 1.5)
    BBt = B_p @ B_p.conj().T
    max_p_sq = 0.0
    for xk in x_nu:
        g = (1.0 + xk) / L
        K_p = sp * np.eye(3) - xk * Z_p + g * np.linalg.inv(T1 - g * T2)
        I_gBB = np.eye(3) - g * BBt
        R_x = V_p - g * A_p @ B_p.conj().T @ np.linalg.inv(I_gBB)
        max_p_sq = max(max_p_sq, float(np.linalg.norm((K_p - B_sig) - R_x @ I_gBB @ R_x.conj().T)))

    # Dual 1-square identity (#119)
    Z_d = matpow(D, -kap) @ M @ matpow(D, kap - 1.0)
    W1 = matpow(D, 1.0 - kap) @ matpow(M, 2.0 * kap - 2.0) @ matpow(D, 1.0 - kap)
    W1inv = matpow(D, kap - 1.0) @ matpow(M, 2.0 - 2.0 * kap) @ matpow(D, kap - 1.0)
    Y_d = matpow(D, 0.5 - kap) @ matpow(G, kap - 0.5) @ matpow(D, 0.5 - kap)
    P_d = matpow(D, kap - 1.5) @ matpow(G, 1.5 - kap) @ matpow(D, kap - 1.5)
    W2 = W1 @ P_d @ W1
    max_d_sq = 0.0
    for sk in s_mu:
        mid = L * W1inv - sk * P_d
        K_d = sp * np.eye(3) - sk * Y_d + np.linalg.inv(mid)
        Rt = Z_d - L * np.linalg.inv(mid) @ W1inv
        Sq_d = (Rt @ (W1 - (sk / L) * W2) @ Rt.conj().T) / L
        max_d_sq = max(max_d_sq, float(np.linalg.norm((K_d - B_sig) - Sq_d)))

    res_u = eval_primal_dual_general(D, H, L, kap, 2, x_nu, w_nu, s_mu, w_mu)
    res_diag = eval_primal_dual_diag(d, X, L, kap, 2, x_nu, w_nu, s_mu, w_mu)
    u_inv_err = max(float(np.max(np.abs(res_u["eP"] - res_diag["eP"]))),
                    float(np.max(np.abs(res_u["eD"] - res_diag["eD"]))))
    assert max_p_sq < 1e-10 and max_d_sq < 1e-10 and u_inv_err < 1e-10
    print(f"  p={lbl:5s} (k={kap:5.3f}) U(3)-complex | Primal 1-sq={max_p_sq:.2e} | Dual 1-sq={max_d_sq:.2e} | U(3) inv={u_inv_err:.2e}")

print("\n[1B] High-Rank RG Spectra up to r = 8 (Regimes I, II, III; m = 2, 10, 50, 200):")
rg_cache = {}
rg_specs = [
    ("1.85", 1.85, 2, 3, "primal"),
    ("7/4", 1.75, 2, 5, "primal"),
    ("5/3", 5.0 / 3.0, 2, 8, "primal"),
    ("5/3", 5.0 / 3.0, 50, 3, "primal"),
    ("5/3", 5.0 / 3.0, 200, 3, "primal"),
    ("1.49", 1.49, 2, 5, "dual"),
    ("1.45", 1.45, 2, 5, "dual"),
    ("sqrt2", np.sqrt(2.0), 2, 8, "dual"),
    ("7/5", 1.4, 2, 8, "dual"),
    ("7/5", 1.4, 50, 3, "dual"),
    ("7/5", 1.4, 200, 3, "dual"),
    ("5/4", 1.25, 2, 8, "both"),
    ("5/4", 1.25, 50, 3, "both"),
    ("6/5", 1.2, 2, 8, "both"),
    ("6/5", 1.2, 50, 3, "both"),
    ("6/5", 1.2, 200, 3, "both"),
    ("1.1", 1.1, 2, 3, "both"),
]
for lbl, p_val, m_val, r_use, fam in rg_specs:
    kap = p_val / (2.0 * (p_val - 1.0))
    L, d, X, err, oe = continue_rg(p_val, m_val, r_use, rg_p32)
    assert err < 1e-8 and oe < 1e-8, f"RG continuation failed for ({lbl}, m={m_val}, r={r_use}): err={err}, oe={oe}"
    x_nu, w_nu, s_mu, w_mu = extract_rg_measures(d, X)
    res = eval_primal_dual_diag(d, X, L, kap, m_val, x_nu, w_nu, s_mu, w_mu)
    assert res["ok"]
    rg_cache[(lbl, m_val, r_use)] = (L, d, X, x_nu, w_nu, s_mu, w_mu, res)
    if fam in ("primal", "both"):
        assert float(res["eP"][0]) >= 1.0 - 1e-9 and float(res["eP"][1]) > 1.0
    if fam in ("dual", "both"):
        assert float(res["eD"][0]) >= 1.0 - 1e-9 and float(res["eD"][1]) > 1.0
    p_str = f"[{res['eP'][0]:.6f}, {res['eP'][1]:.5f}..{res['eP'][-1]:.5f}]"
    d_str = f"[{res['eD'][0]:.6f}, {res['eD'][1]:.5f}..{res['eD'][-1]:.5f}]"
    print(f"  p={lbl:5s} m={m_val:3d} r={r_use} (err={err:.1e}) Lam={L:13.8f} | P={p_str} | D={d_str}")

print("\n[1C] Exact Finite-Rank Gap Separation (Schur-Complement Theorem: nu_2/mu_2 evaluated on r=8 RG at Lam_8):")
# Proves that finite-rank measure nu_2 / mu_2 strictly drops < 1 on higher-rank X_8 at Lam_8 (expected finite-r gap!),
# whereas full nu_8 / mu_8 gives exact 1.0000000000 on e_0 and > 1 on e_0^perp!
for lbl, p_val, fam in [("7/5", 1.4, "dual"), ("5/4", 1.25, "both"), ("6/5", 1.2, "both")]:
    kap = p_val / (2.0 * (p_val - 1.0))
    L2, d2, X2, err2, oe2 = continue_rg(p_val, 2, 2, rg_p32)
    L8, d8, X8, _, _, _, _, _ = rg_cache[(lbl, 2, 8)]
    assert err2 < 1e-11 and oe2 < 1e-11 and L8 > L2
    x_nu2, w_nu2, s_mu2, w_mu2 = extract_rg_measures(d2, X2)
    res_mismatch = eval_primal_dual_diag(d8, X8, L8, kap, 2, x_nu2, w_nu2, s_mu2, w_mu2)
    assert res_mismatch["ok"]
    if fam in ("primal", "both"):
        assert float(res_mismatch["eP"][0]) < 1.0 - 1e-8
    if fam in ("dual", "both"):
        assert float(res_mismatch["eD"][0]) < 1.0 - 1e-8
    print(
        f"  p={lbl:4s}: Lam_8 - Lam_2 = {L8 - L2:+.3e} | nu_2 on X_8: min(P)={res_mismatch['eP'][0]:.10f} (< 1) "
        f"| mu_2 on X_8: min(D)={res_mismatch['eD'][0]:.10f} (< 1) [expected finite-r gap]"
    )


# ==============================================================================
# SUITE 2: 50-DIGIT MPMATH CERTIFIED COUNTEREXAMPLES & NO-GO THEOREM FOR
#          CONSTANT-WEIGHT U_{3/4} = (3/4) I_primal + (1/4) I_dual (#119),
#          PLUS DUAL theta-FAMILY AUDIT
# ==============================================================================
print("\n" + "=" * 100)
print("SUITE 2: 50-DPS COUNTEREXAMPLES & NO-GO FOR CONSTANT-WEIGHT U_{3/4} + DUAL theta-FAMILY AUDIT")
print("=" * 100)

print("\n[2A] Exact Slope-Ratio No-Go at p = 3/2: R(m) = |D'(3/2, m) / P'(3/2, m)| Strictly Increases in m:")
alpha_stars = {}
for m_val in [2, 3, 10, 50]:
    L_m, d_m, X_m, err_m, _ = continue_rg(1.5, m_val, 2, rg_p32)
    assert err_m < 1e-12
    vals = {}
    for dp in [-0.005, -0.001, +0.001, +0.005]:
        pp = 1.5 + dp
        kap = pp / (2.0 * (pp - 1.0))
        L1 = scalar_1x1(kap, m_val)
        L, d, X, err, oe = solve_rg_square(pp, m_val, 2, L1 * 1.0001, d_m, X_m)
        assert err < 1e-12 and oe < 1e-12
        x_nu, w_nu, s_mu, w_mu = extract_rg_measures(d, X)
        res = eval_primal_dual_diag(d, X, L, kap, m_val, x_nu, w_nu, s_mu, w_mu)
        p11 = float(res["eP"][0] if abs(res["eP"][1] - 1.0) < abs(res["eP"][0] - 1.0) else res["eP"][1]) - 1.0
        d11 = float(res["eD"][0] if abs(res["eD"][1] - 1.0) < abs(res["eD"][0] - 1.0) else res["eD"][1]) - 1.0
        vals[dp] = (p11, d11)
    Pp = (vals[+0.001][0] - vals[-0.001][0]) / 0.002
    Dp = (vals[+0.001][1] - vals[-0.001][1]) / 0.002
    assert Pp > 0.0 and Dp < 0.0
    R_m = abs(Dp / Pp)
    a_star = R_m / (1.0 + R_m)
    Ppp = (vals[+0.005][0] + vals[-0.005][0]) / (0.005 ** 2)
    Dpp = (vals[+0.005][1] + vals[-0.005][1]) / (0.005 ** 2)
    fpp = a_star * Ppp + (1.0 - a_star) * Dpp
    assert fpp > 0.0
    alpha_stars[m_val] = a_star
    print(f"  m={m_val:2d}: P'(3/2)={Pp:+.5f}, D'(3/2)={Dp:+.5f} => R(m)={R_m:.5f}, unique alpha*(m)={a_star:.6f}, f''_{{alpha*}}(3/2)={fpp:+.4f} > 0")

assert alpha_stars[2] < 0.75 < alpha_stars[10] < alpha_stars[50]
print(f"  NO-GO (across m): alpha*(2)={alpha_stars[2]:.6f} < 3/4 = 0.75 < alpha*(10)={alpha_stars[10]:.6f} < alpha*(50)={alpha_stars[50]:.6f}!")

# Strengthened No-Go at FIXED m = 2 on r = 4 RG (exact generalized eigenvalues on non-commuting 3x3 e_0^perp blocks!)
L4_m, d4_m, X4_m = rg_p32[4]
L4_lo, d4_lo, X4_lo, e4_lo, _ = solve_rg_square(1.499, 2, 4, scalar_1x1(1.499 / 0.998, 2) * 1.0001, d4_m, X4_m)
L4_hi, d4_hi, X4_hi, e4_hi, _ = solve_rg_square(1.501, 2, 4, scalar_1x1(1.501 / 1.002, 2) * 1.0001, d4_m, X4_m)
assert e4_lo < 1e-12 and e4_hi < 1e-12
xn_lo, wn_lo, sm_lo, wm_lo = extract_rg_measures(d4_lo, X4_lo)
xn_hi, wn_hi, sm_hi, wm_hi = extract_rg_measures(d4_hi, X4_hi)
r4_lo = eval_primal_dual_diag(d4_lo, X4_lo, L4_lo, 1.499 / 0.998, 2, xn_lo, wn_lo, sm_lo, wm_lo)
r4_hi = eval_primal_dual_diag(d4_hi, X4_hi, L4_hi, 1.501 / 1.002, 2, xn_hi, wn_hi, sm_hi, wm_hi)
# Exact 3x3 e_0^perp derivative blocks P_p = d/dp(c I_primal)|_{e_0^perp} and D_p = d/dp(c I_dual)|_{e_0^perp}
P_p = (r4_hi["cIp"][1:, 1:] - r4_lo["cIp"][1:, 1:]) / 0.002
D_p = (r4_hi["cId"][1:, 1:] - r4_lo["cId"][1:, 1:]) / 0.002
P_p = 0.5 * (P_p + P_p.T)
D_p = 0.5 * (D_p + D_p.T)
comm_PD = float(np.linalg.norm(P_p @ D_p - D_p @ P_p))
assert float(np.min(np.linalg.eigvalsh(P_p))) > 0.0 and float(np.max(np.linalg.eigvalsh(D_p))) < 0.0
assert comm_PD > 1e-6  # genuinely non-commuting 3x3 blocks!
# Solve exact generalized eigenvalue problem (-D_p) v = rho P_p v => (1-lam) P_p + lam D_p = 0 at lam = 1/(1+rho)
rho_gen = eigh(-D_p, P_p, eigvals_only=True)
lam_crit_4 = np.sort(1.0 / (1.0 + rho_gen))
spread_4 = float(lam_crit_4[-1] - lam_crit_4[0])
assert spread_4 > 0.01
print(f"  NO-GO (even at FIXED m=2, r=4, ||[P',D']||={comm_PD:.2e}): exact gen-eig lam_crit={np.round(lam_crit_4, 6)} (spread={spread_4:.6f} > 0.01)!")
print("  => NO single scalar weight (1-lam)*I_primal + lam*I_dual works near p=3/2; uniquely forces exact 2-piece split at p=3/2!")

print("\n[2B] 50-Digit mpmath Certified Counterexamples Breaking U_{3/4} = (3/4) I_primal + (1/4) I_dual on BOTH Sides of p = 3/2:")
ce_cases = [
    ("1495/1000", mp.mpf(1495) / 1000, 2, "Regime II (below 3/2)"),
    ("1505/1000", mp.mpf(1505) / 1000, 10, "Regime I (above 3/2)"),
    ("1550/1000", mp.mpf(1550) / 1000, 50, "Regime I (well above 3/2)"),
]
for plbl, p_mp, m_val, side_lbl in ce_cases:
    p_f = float(p_mp)
    kap_mp = p_mp / (2 * (p_mp - 1))
    L_f, d_f, X_f, err_f, _ = continue_rg(p_f, m_val, 2, rg_p32)
    assert err_f < 1e-12
    v_init = [mp.mpf(L_f), mp.mpf(d_f[1]), mp.mpf(X_f[0, 0]), mp.mpf(X_f[0, 1]), mp.mpf(X_f[1, 1])]

    def mp_rg2_res(L_, d1_, x00_, x01_, x11_):
        _, _, _, sp_ = mp_roots(L_, kap_mp)
        sD1 = mp.sqrt(d1_)
        H_ = mp.matrix([[x00_, sD1 * x01_], [sD1 * x01_, d1_ * x11_]])
        M_ = mp.matrix([[1 + H_[0, 0], H_[0, 1]], [H_[0, 1], d1_ + H_[1, 1]]])
        G_ = mp.matrix([[H_[0, 0], sD1 * H_[0, 1]], [sD1 * H_[0, 1], d1_ * H_[1, 1]]])
        Gp = mp_matpow2(G_, kap_mp - 1)
        Gpp = mp_matpow2(G_, kap_mp)
        Mp = mp_matpow2(M_, 2 * kap_mp - 1)
        Z_ = mp.matrix([[Gp[0, 0], d1_ ** (1 - kap_mp) * Gp[0, 1]],
                        [d1_ ** (1 - kap_mp) * Gp[0, 1], d1_ ** (2 - 2 * kap_mp) * Gp[1, 1]]])
        Ds1 = d1_ ** (-kap_mp + mp.mpf("0.5"))
        R1_ = mp.matrix([[Mp[0, 0] - L_ * Z_[0, 0], Ds1 * Mp[0, 1] - L_ * Z_[0, 1]],
                         [Ds1 * Mp[0, 1] - L_ * Z_[0, 1], Ds1 * Ds1 * Mp[1, 1] - L_ * Z_[1, 1]]])
        E_ = mp.matrix([[Gpp[0, 0] - Z_[0, 0], d1_ ** (-kap_mp) * Gpp[0, 1] - Z_[0, 1]],
                        [d1_ ** (-kap_mp) * Gpp[0, 1] - Z_[0, 1], d1_ ** (-2 * kap_mp) * Gpp[1, 1] - Z_[1, 1]]])
        return [R1_[0, 0], R1_[0, 1], R1_[1, 1], E_[0, 0] + sp_ / (m_val - 1), E_[1, 1] - sp_]

    sol = mp.findroot(mp_rg2_res, v_init, tol=mp.mpf("1e-44"))
    L_, d1_, x00_, x01_, x11_ = [sol[i] for i in range(5)]
    res_n = mp.sqrt(sum(r * r for r in mp_rg2_res(L_, d1_, x00_, x01_, x11_)))
    _, _, _, sp_ = mp_roots(L_, kap_mp)
    sD1 = mp.sqrt(d1_)
    X_ = mp.matrix([[x00_, x01_], [x01_, x11_]])
    H_ = mp.matrix([[x00_, sD1 * x01_], [sD1 * x01_, d1_ * x11_]])
    M_ = mp.matrix([[1 + H_[0, 0], H_[0, 1]], [H_[0, 1], d1_ + H_[1, 1]]])
    G_ = mp.matrix([[H_[0, 0], sD1 * H_[0, 1]], [sD1 * H_[0, 1], d1_ * H_[1, 1]]])
    Gh = mp_matpow2(G_, mp.mpf("0.5"))
    Q_ = mp.matrix([[Gh[0, 0], Gh[0, 1] / sD1], [Gh[0, 1] / sD1, Gh[1, 1] / d1_]])
    Gp = mp_matpow2(G_, kap_mp - 1)
    Z_ = mp.matrix([[Gp[0, 0], d1_ ** (1 - kap_mp) * Gp[0, 1]],
                    [d1_ ** (1 - kap_mp) * Gp[0, 1], d1_ ** (2 - 2 * kap_mp) * Gp[1, 1]]])
    Gpp = mp_matpow2(G_, kap_mp)
    E_off = abs(d1_ ** (-kap_mp) * Gpp[0, 1] - Z_[0, 1])
    M1 = mp_matpow2(M_, 3 - 2 * kap_mp)
    G1 = mp_matpow2(G_, 2 - kap_mp)
    T1 = mp.matrix([[M1[0, 0], d1_ ** (kap_mp - mp.mpf("1.5")) * M1[0, 1]],
                    [d1_ ** (kap_mp - mp.mpf("1.5")) * M1[0, 1], d1_ ** (2 * kap_mp - 3) * M1[1, 1]]])
    T2 = mp.matrix([[G1[0, 0], d1_ ** (kap_mp - 2) * G1[0, 1]],
                    [d1_ ** (kap_mp - 2) * G1[0, 1], d1_ ** (2 * kap_mp - 4) * G1[1, 1]]])
    Gy = mp_matpow2(G_, kap_mp - mp.mpf("0.5"))
    Y_ = mp.matrix([[Gy[0, 0], d1_ ** (mp.mpf("0.5") - kap_mp) * Gy[0, 1]],
                    [d1_ ** (mp.mpf("0.5") - kap_mp) * Gy[0, 1], d1_ ** (1 - 2 * kap_mp) * Gy[1, 1]]])
    Mw = mp_matpow2(M_, 2 - 2 * kap_mp)
    Gq = mp_matpow2(G_, mp.mpf("1.5") - kap_mp)
    W1inv = mp.matrix([[Mw[0, 0], d1_ ** (kap_mp - 1) * Mw[0, 1]],
                       [d1_ ** (kap_mp - 1) * Mw[0, 1], d1_ ** (2 * kap_mp - 2) * Mw[1, 1]]])
    P_ = mp.matrix([[Gq[0, 0], d1_ ** (kap_mp - mp.mpf("1.5")) * Gq[0, 1]],
                    [d1_ ** (kap_mp - mp.mpf("1.5")) * Gq[0, 1], d1_ ** (2 * kap_mp - 3) * Gq[1, 1]]])
    xs, wx = mp_eigs2(X_)
    ss, ws = mp_eigs2(Q_)
    Ip = mp.matrix([[0, 0], [0, 0]])
    Id = mp.matrix([[0, 0], [0, 0]])
    for xk, wk in zip(xs, wx):
        g = (1 + xk) / L_
        Ip += wk * mp_inv2(sp_ * mp.eye(2) - xk * Z_ + g * mp_inv2(T1 - g * T2))
    for sk, wk in zip(ss, ws):
        Id += wk * mp_inv2(sp_ * mp.eye(2) - sk * Y_ + mp_inv2(L_ * W1inv - sk * P_))
    c = (mp.mpf(m_val) / (m_val - 1)) * sp_
    cP, cD = c * Ip, c * Id
    cU = mp.mpf("0.75") * cP + mp.mpf("0.25") * cD
    assert res_n < mp.mpf("1e-45") and E_off < mp.mpf("1e-45")
    assert abs(cP[0, 0] - 1) < mp.mpf("1e-45") and abs(cD[0, 0] - 1) < mp.mpf("1e-45")
    assert cU[1, 1] - 1 < mp.mpf("-1e-5")
    print(f"  p={plbl} m={m_val:2d} [{side_lbl}]: 50-dps res={mp.nstr(res_n, 3)}, E_off={mp.nstr(E_off, 3)}")
    print(f"    Lam={mp.nstr(L_, 16)}, d1={mp.nstr(d1_, 12)}, X=({mp.nstr(x00_, 10)}, {mp.nstr(x01_, 10)}, {mp.nstr(x11_, 10)})")
    print(f"    (cP)_11-1={mp.nstr(cP[1, 1] - 1, 8)}, (cD)_11-1={mp.nstr(cD[1, 1] - 1, 8)} => (cU_3/4)_11-1 = {mp.nstr(cU[1, 1] - 1, 10)} < 0 [CERTIFIED!]")

print("\n[2C] Dual Continuous theta-Family Audit (#119 Item 3): Exact 1-Square Identity & Unique theta=0 Zero-Gap Tangency:")
# Test on r = 3 RG at p = 7/5 (k = 7/4)
L3_75, d3_75, X3_75, err3_75, _ = continue_rg(1.4, 2, 3, rg_p32)
assert err3_75 < 1e-12
kap75 = 1.4 / 0.8
_, _, _, sp75 = roots_kappa(L3_75, kap75)
sD3 = np.sqrt(d3_75)
D3 = np.diag(d3_75)
H3 = (sD3[:, None] * X3_75) * sD3[None, :]
M3 = D3 + H3
G3 = (sD3[:, None] * H3) * sD3[None, :]
Z_d3 = matpow(D3, -kap75) @ M3 @ matpow(D3, kap75 - 1.0)
W1_3 = matpow(D3, 1.0 - kap75) @ matpow(M3, 2.0 * kap75 - 2.0) @ matpow(D3, 1.0 - kap75)
W1inv_3 = matpow(D3, kap75 - 1.0) @ matpow(M3, 2.0 - 2.0 * kap75) @ matpow(D3, kap75 - 1.0)
Ehat3 = matpow(D3, -kap75) @ matpow(G3, kap75) @ matpow(D3, -kap75) - matpow(D3, 1.0 - kap75) @ matpow(G3, kap75 - 1.0) @ matpow(D3, 1.0 - kap75)
B_sig3 = sp75 * np.eye(3) - Ehat3
for theta in [-0.10, -0.05, 0.0, +0.05, +0.10]:
    P_th = matpow(D3, kap75 - 1.5 - theta) @ matpow(G3, 1.5 - kap75 + theta) @ matpow(D3, kap75 - 1.5 - theta)
    Y_th = (
        matpow(D3, 0.5 - kap75) @ matpow(G3, kap75 - 1.0) @ matpow(D3, -theta)
        @ matpow(G3, 1.5 - kap75 + theta) @ matpow(D3, -theta) @ matpow(G3, kap75 - 1.0) @ matpow(D3, 0.5 - kap75)
    )
    W2_th = W1_3 @ P_th @ W1_3
    # Natural scale-matched spectral measure of Q_th = D^{theta - 1/2} G^{1/2 - theta} D^{theta - 1/2}
    Q_th = matpow(D3, theta - 0.5) @ matpow(G3, 0.5 - theta) @ matpow(D3, theta - 0.5)
    s_th, V_th = eigh(0.5 * (Q_th + Q_th.T))
    w_th = V_th[0, :] ** 2
    max_sq_th = 0.0
    I_th = np.zeros((3, 3))
    for sk, wk in zip(s_th, w_th):
        mid = L3_75 * W1inv_3 - sk * P_th
        K_th = sp75 * np.eye(3) - sk * Y_th + np.linalg.inv(mid)
        Rt = Z_d3 - L3_75 * np.linalg.inv(mid) @ W1inv_3
        Sq = (Rt @ (W1_3 - (sk / L3_75) * W2_th) @ Rt.T) / L3_75
        max_sq_th = max(max_sq_th, float(np.linalg.norm((K_th - B_sig3) - Sq)))
        I_th += wk * np.linalg.inv(K_th)
    cI_00 = float(2.0 * sp75 * I_th[0, 0])
    eI_th = np.linalg.eigvalsh(0.5 * (2.0 * sp75 * I_th + (2.0 * sp75 * I_th).T))
    assert max_sq_th < 1e-12
    if abs(theta) < 1e-15:
        assert abs(cI_00 - 1.0) < 1e-12 and float(eI_th[0]) >= 1.0 - 1e-12
    else:
        assert cI_00 < 1.0 - 1e-6  # nonzero theta strictly loses zero-gap RG tangency!
    print(f"  p=7/5 r=3 theta={theta:+.2f} | 1-sq err={max_sq_th:.2e} | (c I_th)_00={cI_00:.8f} | eigs={np.round(eI_th, 6)}")


# ==============================================================================
# SUITE 3: DOMAIN POSITIVITY AUDIT — NON-HOLDEN FAILURE vs HOLDEN HANSEN SURVIVAL
# ==============================================================================
print("\n" + "=" * 100)
print("SUITE 3: DOMAIN POSITIVITY AUDIT (NON-HOLDEN CATASTROPHIC FAILURE vs HOLDEN HANSEN SURVIVAL)")
print("=" * 100)

print("\n[3A] Non-Holden Random Complex 3x3 Matrices (0 < H <= x_+ D) Break Domain Positivity Without Holden:")
for lbl, p_val in [("7/5", 1.4), ("5/4", 1.25), ("6/5", 1.2)]:
    kap = p_val / (2.0 * (p_val - 1.0))
    L1 = scalar_1x1(kap, 2)
    _, xp, _, _ = roots_kappa(L1, kap)
    g_xp = (1.0 + xp) / L1
    sp_root = np.sqrt(xp)
    max_rp = max_rd = 0.0
    neg_p = neg_d = 0
    for _ in range(1500):
        d = np.array([1.0, 10.0 ** rng.uniform(-3.5, 0.0), 10.0 ** rng.uniform(-3.5, 0.0)])
        sD = np.sqrt(d)
        D = np.diag(d)
        A = rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3))
        U, _ = np.linalg.qr(A)
        eigs = 10.0 ** rng.uniform(-4.5, np.log10(xp), 3)
        X = (U * eigs) @ U.conj().T
        H = (sD[:, None] * X) * sD[None, :]
        M = D + H
        G = (sD[:, None] * H) * sD[None, :]
        T1 = (d ** (kap - 1.5))[:, None] * matpow(M, 3.0 - 2.0 * kap) * (d ** (kap - 1.5))[None, :]
        T2 = (d ** (kap - 2.0))[:, None] * matpow(G, 2.0 - kap) * (d ** (kap - 2.0))[None, :]
        T1mh = matpow(T1, -0.5)
        Sp = T1mh @ T2 @ T1mh
        rp = g_xp * float(np.max(np.linalg.eigvalsh(0.5 * (Sp + Sp.conj().T))))
        if rp > max_rp:
            max_rp = rp
        if rp >= 1.0:
            neg_p += 1

        W1inv = (d ** (kap - 1.0))[:, None] * matpow(M, 2.0 - 2.0 * kap) * (d ** (kap - 1.0))[None, :]
        P = (d ** (kap - 1.5))[:, None] * matpow(G, 1.5 - kap) * (d ** (kap - 1.5))[None, :]
        W1h = matpow(L1 * W1inv, -0.5)
        Sd = W1h @ P @ W1h
        rd = sp_root * float(np.max(np.linalg.eigvalsh(0.5 * (Sd + Sd.conj().T))))
        if rd > max_rd:
            max_rd = rd
        if rd >= 1.0:
            neg_d += 1

    theo = xp / (1.0 + xp)
    if kap <= 2.0:
        assert neg_p == 0 and max_rp <= theo + 1e-10  # Thm 1.3 holds without Holden for p >= 4/3!
        assert neg_d > 100 and max_rd > 2.0          # Dual needs Hansen (Holden!) for p < 3/2!
    else:
        assert neg_p > 1000 and max_rp > 10.0        # Primal needs Hansen (Holden!) for p < 4/3!
        assert neg_d > 1000 and max_rd > 10.0        # Dual needs Hansen (Holden!) for p < 3/2!
    print(f"  NON-HOLDEN p={lbl:4s} (k={kap:4.2f}, x_+/(1+x_+)={theo:.5f}): Primal neg={neg_p:4d}/1500 (max_rho={max_rp:.3e}) | Dual neg={neg_d:4d}/1500 (max_rho={max_rd:.3e})")


# ==============================================================================
# SUITE 4: HIGH-DIM (n = 3..8) ADVERSARIAL NELDER-MEAD, MULTI-BRANCH (2,1),
#          FORCED STRONGLY-INDEFINITE B_{sig_+} AT m = 50, 200, DELTA SWEEP,
#          n > r AT LAMBDA_UB, & 50-DPS MPMATH VERIFICATION
# ==============================================================================
print("\n" + "=" * 100)
print("SUITE 4: ADVERSARIAL NELDER-MEAD, MULTI-BRANCH, LARGE-m INDEFINITE B, n > r, & 50-DPS CHECK")
print("=" * 100)

print("\n[4A] Direct Adversarial Nelder-Mead Minimization of min_eig(c(dreq + de) I_op) & Maximization of rho:")
nm_configs = [
    ("1.85", 1.85, 2, 3, "primal"),
    ("7/4", 1.75, 2, 5, "primal"),
    ("5/3", 5.0 / 3.0, 2, 5, "primal"),
    ("5/3", 5.0 / 3.0, 50, 3, "primal"),
    ("1.49", 1.49, 2, 5, "dual"),
    ("1.45", 1.45, 2, 5, "dual"),
    ("sqrt2", np.sqrt(2.0), 2, 5, "dual"),
    ("7/5", 1.4, 2, 6, "dual"),
    ("7/5", 1.4, 50, 3, "dual"),
    ("5/4", 1.25, 2, 5, "both"),
    ("5/4", 1.25, 50, 3, "both"),
    ("6/5", 1.2, 2, 5, "both"),
    ("6/5", 1.2, 50, 3, "both"),
    ("1.1", 1.1, 2, 3, "both"),
]
total_nm_evals = 0
total_nm_indef = 0
tight_nonrg_for_mp = []

for lbl, p_val, m_val, r_use, fam in nm_configs:
    kap = p_val / (2.0 * (p_val - 1.0))
    if (lbl, m_val, r_use) in rg_cache:
        L, d, X, x_nu, w_nu, s_mu, w_mu, res0 = rg_cache[(lbl, m_val, r_use)]
    else:
        L, d, X, err, oe = continue_rg(p_val, m_val, r_use, rg_p32)
        assert err < 1e-9 and oe < 1e-9
        x_nu, w_nu, s_mu, w_mu = extract_rg_measures(d, X)
        res0 = eval_primal_dual_diag(d, X, L, kap, m_val, x_nu, w_nu, s_mu, w_mu)
    theo_rho = res0["xp"] / (1.0 + res0["xp"])
    state = {
        "X": X.copy(),
        "minP": float(res0["eP"][0]) if fam in ("primal", "both") else 1e9,
        "minD": float(res0["eD"][0]) if fam in ("dual", "both") else 1e9,
        "max_rp": res0["rho_p"], "max_rd": res0["rho_d"],
        "evals": 0, "indef": 0, "max_dreq": 0.0,
        "best_nonrg": None,
    }

    def obj_min(u):
        dd = np.concatenate([[1.0], np.exp(np.clip(u, -22.0, -1e-4))])
        if np.any(dd[1:] >= 0.9999) or np.any(dd[1:] <= 1e-9):
            return 10.0
        Xn, e = solve_holden_real(dd, state["X"], L, kap)
        if e > 1e-10:
            Xn, e = solve_holden_real(dd, X, L, kap)
        if e > 1e-10:
            return 10.0
        state["X"] = Xn
        state["evals"] += 1
        r0 = eval_primal_dual_diag(dd, Xn, L, kap, m_val, x_nu, w_nu, s_mu, w_mu, 0.0)
        if not r0["ok"]:
            return -10.0
        state["max_rp"] = max(state["max_rp"], r0["rho_p"])
        state["max_rd"] = max(state["max_rd"], r0["rho_d"])
        if r0["dreq"] > 1e-6:
            state["indef"] += 1
            state["max_dreq"] = max(state["max_dreq"], r0["dreq"])
        vals_cur = []
        for de in [0.0, 0.01, 0.5, 5.0]:
            rd_ = r0 if de == 0.0 else eval_primal_dual_diag(dd, Xn, L, kap, m_val, x_nu, w_nu, s_mu, w_mu, de)
            if not rd_["ok"]:
                return -10.0
            if fam in ("primal", "both"):
                vp = float(rd_["eP"][0])
                if vp < state["minP"]:
                    state["minP"] = vp
                vals_cur.append(vp)
            if fam in ("dual", "both"):
                vd = float(rd_["eD"][0])
                if vd < state["minD"]:
                    state["minD"] = vd
                vals_cur.append(vd)
        # Track tightest genuine non-RG point with indef B for 50-dps verification
        if np.linalg.norm(dd - d) > 1e-3 and r0["dreq"] > 1e-5:
            v0 = float(r0["eP"][0]) if fam == "primal" else (float(r0["eD"][0]) if fam == "dual" else min(float(r0["eP"][0]), float(r0["eD"][0])))
            if state["best_nonrg"] is None or v0 < state["best_nonrg"][0]:
                state["best_nonrg"] = (v0, dd.copy(), Xn.copy(), r0["dreq"])
        return min(vals_cur)

    u0 = np.log(d[1:])
    for si in range(3):
        state["X"] = X.copy()
        u_start = u0 + (0.0 if si == 0 else rng.normal(0.0, 0.12, len(u0)))
        minimize(obj_min, u_start, method="Nelder-Mead", options={"maxiter": 75, "xatol": 1e-4, "fatol": 1e-8})

    total_nm_evals += state["evals"]
    total_nm_indef += state["indef"]
    assert state["max_rp"] <= theo_rho + 1e-9 and state["max_rd"] <= theo_rho + 1e-9
    if fam in ("primal", "both"):
        assert state["minP"] >= 1.0 - 1e-9, f"Primal violation at ({lbl}, m={m_val}): {state['minP']}"
    if fam in ("dual", "both"):
        assert state["minD"] >= 1.0 - 1e-9, f"Dual violation at ({lbl}, m={m_val}): {state['minD']}"
    if lbl in ("5/3", "7/5", "6/5") and m_val == 2 and r_use in (5, 6) and state["best_nonrg"] is not None:
        tight_nonrg_for_mp.append((lbl, p_val, m_val, L, d, X, x_nu, w_nu, s_mu, w_mu, fam, state["best_nonrg"]))
    p_s = f"{state['minP']:.8f}" if fam in ("primal", "both") else "   (n/a)  "
    d_s = f"{state['minD']:.8f}" if fam in ("dual", "both") else "   (n/a)  "
    print(
        f"  p={lbl:5s} m={m_val:2d} r={r_use} [{fam:6s}]: evals={state['evals']:3d} (indef={state['indef']:3d}) "
        f"| rho<= {max(state['max_rp'], state['max_rd']):.6f} <= {theo_rho:.6f} | min(P)={p_s} | min(D)={d_s}"
    )

print(f"  TOTAL Nelder-Mead adversarial evaluations: {total_nm_evals} ({total_nm_indef} indef B) — ZERO violations!")

print("\n[4B] Forced Strongly-Indefinite B_{sig_+} Sweeps at Large m = 50, 200 (with delta_extra in {0, 0.01, 0.5, 5.0}):")
for lbl, p_val, m_val, fam, st0 in [
    ("5/3", 5.0 / 3.0, 50, "primal", 0.015),
    ("5/3", 5.0 / 3.0, 200, "primal", 0.015),
    ("7/5", 1.4, 50, "dual", 0.05),
    ("7/5", 1.4, 200, "dual", 0.05),
    ("5/4", 1.25, 50, "both", 0.05),
    ("6/5", 1.2, 50, "both", 0.05),
    ("6/5", 1.2, 200, "both", 0.05),
]:
    kap = p_val / (2.0 * (p_val - 1.0))
    L, d, X, x_nu, w_nu, s_mu, w_mu, _ = rg_cache[(lbl, m_val, 3)]
    min_p = min_d = 1e9
    max_dr_rat = 0.0
    n_ind = n_ok = 0
    for sdir in [np.array([1.0, 1.0]), np.array([1.0, 0.0]), np.array([0.0, 1.0]), np.array([1.0, -0.5])]:
        dc = d.copy()
        Xc = X.copy()
        st = st0
        for _ in range(90):
            dn = dc.copy()
            dn[1:] = dc[1:] * np.exp(st * sdir)
            if np.any(dn[1:] >= 0.999) or np.any(dn[1:] <= 1e-11):
                st *= 0.5
                if st < 1e-4:
                    break
                continue
            Xn, e = solve_holden_real(dn, Xc, L, kap)
            if e > 1e-10 or np.linalg.norm(Xn - np.diag(np.diag(Xn))) < 1e-6:
                st *= 0.5
                if st < 1e-4:
                    break
                continue
            dc, Xc = dn, Xn
            n_ok += 1
            for de in [0.0, 0.01, 0.5, 5.0]:
                rd_ = eval_primal_dual_diag(dc, Xc, L, kap, m_val, x_nu, w_nu, s_mu, w_mu, de)
                assert rd_["ok"]
                if de == 0.0 and rd_["dreq"] > 1e-7:
                    n_ind += 1
                max_dr_rat = max(max_dr_rat, rd_["dreq"] / rd_["sp"])
                min_p = min(min_p, float(rd_["eP"][0]))
                min_d = min(min_d, float(rd_["eD"][0]))
    assert n_ind >= 10 and max_dr_rat > 0.5
    if fam in ("primal", "both"):
        assert min_p >= 1.0 - 1e-9
    if fam in ("dual", "both"):
        assert min_d >= 1.0 - 1e-9
    p_s = f"{min_p:.8f}" if fam in ("primal", "both") else "   (n/a)  "
    d_s = f"{min_d:.8f}" if fam in ("dual", "both") else "   (n/a)  "
    print(f"  p={lbl:4s} m={m_val:3d} r=3 [{fam:6s}]: ok={n_ok:3d}, indef={n_ind:3d}, max(dreq/sp)={max_dr_rat:.3f} | min(P)={p_s} | min(D)={d_s}")

print("\n[4C] High-Dim n = 6, 8 Non-RG Deformations, Multi-Branch (2,1) Irreducible 3x3, & n > r at Lambda_UB:")
# (i) n = 6, 8 non-RG smooth ray continuations across Regimes I, II, III!
for lbl, p_val, n_dim, fam, step_sz in [
    ("5/3", 5.0 / 3.0, 6, "primal", 0.015),
    ("7/5", 1.4, 8, "dual", 0.06),
    ("sqrt2", np.sqrt(2.0), 8, "dual", 0.06),
    ("5/4", 1.25, 8, "both", 0.08),
    ("6/5", 1.2, 8, "both", 0.08),
]:
    kap = p_val / (2.0 * (p_val - 1.0))
    if (lbl, 2, n_dim) in rg_cache:
        L, d, X, x_nu, w_nu, s_mu, w_mu, _ = rg_cache[(lbl, 2, n_dim)]
    else:
        L, d, X, err, _ = continue_rg(p_val, 2, n_dim, rg_p32)
        assert err < 1e-10
        x_nu, w_nu, s_mu, w_mu = extract_rg_measures(d, X)
    n_ok = n_ind = 0
    min_p = min_d = 1e9
    max_dr = 0.0
    for _ in range(10):
        dc = d.copy()
        Xc = X.copy()
        vdir = rng.standard_normal(n_dim - 1)
        vdir /= np.linalg.norm(vdir)
        st = step_sz
        for _ in range(6):
            dn = dc.copy()
            dn[1:] = dc[1:] * np.exp(st * vdir)
            dn = np.sort(dn / np.max(dn))[::-1]
            Xn, e = solve_holden_real(dn, Xc, L, kap)
            if e > 1e-10:
                st *= 0.5
                if st < 1e-4:
                    break
                continue
            dc, Xc = dn, Xn
            n_ok += 1
            rd_ = eval_primal_dual_diag(dc, Xc, L, kap, 2, x_nu, w_nu, s_mu, w_mu)
            assert rd_["ok"]
            if rd_["dreq"] > 1e-6:
                n_ind += 1
                if lbl == "5/3" and (not any(rec[0] == "5/3" for rec in tight_nonrg_for_mp)):
                    tight_nonrg_for_mp.insert(0, ("5/3", p_val, 2, L, d, X, x_nu, w_nu, s_mu, w_mu, "primal", (float(rd_["eP"][0]), dc.copy(), Xc.copy(), rd_["dreq"])))
            max_dr = max(max_dr, rd_["dreq"])
            min_p = min(min_p, float(rd_["eP"][0]))
            min_d = min(min_d, float(rd_["eD"][0]))
    assert n_ok >= 10
    if fam in ("primal", "both"):
        assert min_p >= 1.0 - 1e-9
    if fam in ("dual", "both"):
        assert min_d >= 1.0 - 1e-9
    p_s = f"{min_p:.8f}" if fam in ("primal", "both") else "   (n/a)  "
    d_s = f"{min_d:.8f}" if fam in ("dual", "both") else "   (n/a)  "
    print(f"  n={n_dim} non-RG p={lbl:5s} [{fam:6s}]: ok={n_ok:2d} (indef={n_ind:2d}, max_dreq={max_dr:.3e}) | min(P)={p_s} | min(D)={d_s}")

# (ii) n > r test at Lambda_UB = Lambda_8 * (1 + 1e-4) (evaluating 4-atom measure nu_4/mu_4 on n = 8 Holden!)
for lbl, p_val, fam in [("7/5", 1.4, "dual"), ("5/4", 1.25, "both"), ("6/5", 1.2, "both")]:
    kap = p_val / (2.0 * (p_val - 1.0))
    L4, d4, X4, err4, _ = continue_rg(p_val, 2, 4, rg_p32)
    L8, d8, X8, _, _, _, _, _ = rg_cache[(lbl, 2, 8)]
    assert err4 < 1e-11
    x_nu4, w_nu4, s_mu4, w_mu4 = extract_rg_measures(d4, X4)
    L_ub = L8 * (1.0 + 1e-4)
    X8_ub, e8 = solve_holden_real(d8, X8, L_ub, kap)
    assert e8 < 1e-10
    rd_ub = eval_primal_dual_diag(d8, X8_ub, L_ub, kap, 2, x_nu4, w_nu4, s_mu4, w_mu4)
    assert rd_ub["ok"]
    if fam in ("primal", "both"):
        assert float(rd_ub["eP"][0]) > 1.0 + 1e-5
    if fam in ("dual", "both"):
        assert float(rd_ub["eD"][0]) > 1.0 + 1e-5
    print(f"  n=8 > r=4 at Lam_UB=Lam_8*(1+1e-4) p={lbl:4s}: min(P)={rd_ub['eP'][0]:.8f} | min(D)={rd_ub['eD'][0]:.8f} (STRICTLY > 1!)")

# (iii) Multi-Branch Irreducible (2,1) 3x3 (TWO negative Ehat eigenvalues!) at p = 5/3 and p = 6/5
for lbl, p_val, fam, dd3_seed in [
    ("5/3", 5.0 / 3.0, "primal", np.array([1.0, 0.0148, 0.0094])),
    ("6/5", 1.2, "both", np.array([1.0, 0.4202, 0.2288])),
]:
    kap = p_val / (2.0 * (p_val - 1.0))
    L5, d5, X5, err5, _ = continue_rg(p_val, 2, 5, rg_p32)
    assert err5 < 1e-11
    x_nu5, w_nu5, s_mu5, w_mu5 = extract_rg_measures(d5, X5)
    found_21 = None
    for trial in range(60):
        dd3 = dd3_seed if trial == 0 else np.sort(dd3_seed * np.array([1.0, rng.uniform(0.92, 1.08), rng.uniform(0.85, 1.15)]))[::-1]
        X0 = X5[:3, :3].copy() + rng.normal(0.0, 0.12, (3, 3))
        X0 = 0.5 * (X0 + X0.T)
        w0, V0 = eigh(X0)
        X0 = (V0 * np.maximum(w0, 1e-4)) @ V0.T
        Xn, e = solve_holden_real(dd3, X0, L5, kap)
        if e > 1e-10:
            continue
        if min(abs(Xn[0, 1]), abs(Xn[0, 2]), abs(Xn[1, 2])) < 1e-4:
            continue
        rd_ = eval_primal_dual_diag(dd3, Xn, L5, kap, 2, x_nu5, w_nu5, s_mu5, w_mu5)
        if rd_["ok"] and int(np.sum(rd_["evals_E"] < 0)) == 2:
            found_21 = (dd3, Xn, rd_)
            break
    assert found_21 is not None, f"Failed to find irreducible (2,1) 3x3 at p={lbl}"
    dd3, Xn, rd_ = found_21
    if fam in ("primal", "both"):
        assert float(rd_["eP"][0]) >= 1.0 - 1e-9
    if fam in ("dual", "both"):
        assert float(rd_["eD"][0]) >= 1.0 - 1e-9
    print(
        f"  Irred (2,1) 3x3 p={lbl:4s}: d={np.round(dd3, 4)}, E_eigs={np.round(rd_['evals_E'], 5)} (2 neg!), "
        f"dreq={rd_['dreq']:.3e} | min(P)={rd_['eP'][0]:.6f} | min(D)={rd_['eD'][0]:.6f}"
    )

print("\n[4D] 50-Digit mpmath Independent Verification of Tightest Non-RG Indefinite-B High-Dim Points:")
assert len(tight_nonrg_for_mp) >= 3
for lbl, p_val, m_val, L, d_rg, X_rg, x_nu, w_nu, s_mu, w_mu, fam, best_rec in tight_nonrg_for_mp:
    _, dd_w, X_w, dr_w = best_rec
    p_mp = mp.mpf(5) / 3 if lbl == "5/3" else (mp.mpf(7) / 5 if lbl == "7/5" else mp.mpf(6) / 5)
    kap_mp = p_mp / (2 * (p_mp - 1))
    L_mp = mp.mpf(repr(float(L)))
    _, _, _, sp_mp = mp_roots(L_mp, kap_mp)
    n_w = len(dd_w)
    dd_mp = [mp.mpf(repr(float(v))) for v in dd_w]
    sD_mp = [mp.sqrt(v) for v in dd_mp]
    X_mp = mp.matrix([[mp.mpf(repr(float(X_w[i, j]))) for j in range(n_w)] for i in range(n_w)])
    H_mp = mp.matrix([[sD_mp[i] * X_mp[i, j] * sD_mp[j] for j in range(n_w)] for i in range(n_w)])
    M_mp = mp.matrix([[(dd_mp[i] if i == j else mp.mpf(0)) + H_mp[i, j] for j in range(n_w)] for i in range(n_w)])
    G_mp = mp.matrix([[sD_mp[i] * H_mp[i, j] * sD_mp[j] for j in range(n_w)] for i in range(n_w)])
    Gp = mp_matpow_n(G_mp, kap_mp - 1)
    Gpp = mp_matpow_n(G_mp, kap_mp)
    Mp = mp_matpow_n(M_mp, 2 * kap_mp - 1)
    Z_mp = mp.matrix([[dd_mp[i] ** (1 - kap_mp) * Gp[i, j] * dd_mp[j] ** (1 - kap_mp) for j in range(n_w)] for i in range(n_w)])
    R_mp = mp.matrix([[dd_mp[i] ** (-kap_mp + mp.mpf("0.5")) * Mp[i, j] * dd_mp[j] ** (-kap_mp + mp.mpf("0.5")) - L_mp * Z_mp[i, j] for j in range(n_w)] for i in range(n_w)])
    hold_res = mp.norm(R_mp)
    E_mp = mp.matrix([[dd_mp[i] ** (-kap_mp) * Gpp[i, j] * dd_mp[j] ** (-kap_mp) - Z_mp[i, j] for j in range(n_w)] for i in range(n_w)])
    evE_mp, _ = mp.eigh(E_mp)
    lmax_E_mp = max(evE_mp[i] for i in range(n_w))
    dreq_mp = max(mp.mpf(0), lmax_E_mp - sp_mp)
    assert dreq_mp > mp.mpf("1e-6") and abs(float(dreq_mp) - dr_w) < 1e-10
    c_mp = (mp.mpf(m_val) / (m_val - 1)) * (sp_mp + dreq_mp)
    # Recompute Primal/Dual at 50-dps using exact mp.mpf measure atoms
    M1 = mp_matpow_n(M_mp, 3 - 2 * kap_mp)
    G1 = mp_matpow_n(G_mp, 2 - kap_mp)
    T1_mp = mp.matrix([[dd_mp[i] ** (kap_mp - mp.mpf("1.5")) * M1[i, j] * dd_mp[j] ** (kap_mp - mp.mpf("1.5")) for j in range(n_w)] for i in range(n_w)])
    T2_mp = mp.matrix([[dd_mp[i] ** (kap_mp - 2) * G1[i, j] * dd_mp[j] ** (kap_mp - 2) for j in range(n_w)] for i in range(n_w)])
    Gy = mp_matpow_n(G_mp, kap_mp - mp.mpf("0.5"))
    Y_mp = mp.matrix([[dd_mp[i] ** (mp.mpf("0.5") - kap_mp) * Gy[i, j] * dd_mp[j] ** (mp.mpf("0.5") - kap_mp) for j in range(n_w)] for i in range(n_w)])
    Mw = mp_matpow_n(M_mp, 2 - 2 * kap_mp)
    Gq = mp_matpow_n(G_mp, mp.mpf("1.5") - kap_mp)
    W1inv_mp = mp.matrix([[dd_mp[i] ** (kap_mp - 1) * Mw[i, j] * dd_mp[j] ** (kap_mp - 1) for j in range(n_w)] for i in range(n_w)])
    P_mp = mp.matrix([[dd_mp[i] ** (kap_mp - mp.mpf("1.5")) * Gq[i, j] * dd_mp[j] ** (kap_mp - mp.mpf("1.5")) for j in range(n_w)] for i in range(n_w)])
    Ip_mp = mp.zeros(n_w, n_w)
    for xk, wk in zip(x_nu, w_nu):
        xk_m, wk_m = mp.mpf(repr(float(xk))), mp.mpf(repr(float(wk)))
        g_m = (1 + xk_m) / L_mp
        K_m = (sp_mp + dreq_mp) * mp.eye(n_w) - xk_m * Z_mp + g_m * ((T1_mp - g_m * T2_mp) ** (-1))
        Ip_mp += wk_m * (K_m ** (-1))
    Id_mp = mp.zeros(n_w, n_w)
    for sk, wk in zip(s_mu, w_mu):
        sk_m, wk_m = mp.mpf(repr(float(sk))), mp.mpf(repr(float(wk)))
        K_m = (sp_mp + dreq_mp) * mp.eye(n_w) - sk_m * Y_mp + ((L_mp * W1inv_mp - sk_m * P_mp) ** (-1))
        Id_mp += wk_m * (K_m ** (-1))
    evP_mp, _ = mp.eigh(mp.mpf("0.5") * (c_mp * Ip_mp + (c_mp * Ip_mp).T))
    evD_mp, _ = mp.eigh(mp.mpf("0.5") * (c_mp * Id_mp + (c_mp * Id_mp).T))
    minP_mp = min(evP_mp[i] for i in range(n_w))
    minD_mp = min(evD_mp[i] for i in range(n_w))
    assert hold_res < mp.mpf("1e-10")
    if fam in ("primal", "both"):
        assert minP_mp > 1
    if fam in ("dual", "both"):
        assert minD_mp > 1
    print(f"  50-dps {n_w}x{n_w} non-RG indef p={lbl:4s}: hold_res={mp.nstr(hold_res, 3)}, dreq={mp.nstr(dreq_mp, 5)} | min(P)={mp.nstr(minP_mp, 10)} | min(D)={mp.nstr(minD_mp, 10)}")


# ==============================================================================
# SUITE 5: COUPLED MULTI-BLOCK HOLDEN SOLUTIONS (D, H_1, ..., H_m) WITH sum Ehat_j = 0
#          (COMPLEX HERMITIAN KUBO-ANDO MULTI-BLOCK TUPLES, N = 4, 6, m = 2, 3)
# ==============================================================================
print("\n" + "=" * 100)
print("SUITE 5: COUPLED MULTI-BLOCK HOLDEN SOLUTIONS (sum Ehat_j = 0, COMPLEX NON-COMMUTING MULTI-COLOR KA)")
print("=" * 100)

print("\n[5A] Complex Hermitian Coupled Multi-Block Tuples (D, H_1, ..., H_m) with Exact Color Balance sum Ehat_j = 0:")

def optimize_complex_ka(N, m, p, rng_loc, maxiter=2500):
    """Complex Hermitian Kubo-Ando optimizer yielding exact stationary multi-block tuples (D, H_1, ..., H_m)."""
    s = p / (2.0 - p)
    blk = 2 * N * N

    def unpack(x):
        Zs, Ss = [], []
        for j in range(m):
            seg = x[j * blk:(j + 1) * blk]
            Z = seg[:N * N].reshape(N, N) + 1j * seg[N * N:].reshape(N, N)
            Zs.append(Z)
            S = Z @ Z.conj().T
            Ss.append(0.5 * (S + S.conj().T))
        return Zs, Ss

    def obj_grad(x):
        Zs, Ss = unpack(x)
        M = np.zeros((N, N), dtype=complex)
        N_mat = np.zeros((N, N), dtype=complex)
        eigs, vecs = [], []
        for S in Ss:
            ev, Q = eigh(S)
            if ev[0] <= 1e-22 * max(ev[-1], 1e-30):
                return 1e6, np.zeros_like(x)
            eigs.append(ev)
            vecs.append(Q)
            M += (Q * (ev ** s)) @ Q.conj().T
            N_mat += S
        ln, qn = eigh(0.5 * (N_mat + N_mat.conj().T))
        if ln[0] <= 1e-22 * max(ln[-1], 1e-30):
            return 1e6, np.zeros_like(x)
        Nmh = (qn * (ln ** -0.5)) @ qn.conj().T
        Nh = (qn * np.sqrt(ln)) @ qn.conj().T
        C = 0.5 * (Nh @ M @ Nh + (Nh @ M @ Nh).conj().T)
        de, U = eigh(C)
        if de[0] <= 1e-24 * max(de[-1], 1e-30):
            return 1e6, np.zeros_like(x)
        sqD = np.sqrt(de)
        P = Nmh @ U
        Pinv = U.conj().T @ Nh
        K = 0.5 * ((P * sqD) @ P.conj().T + ((P * sqD) @ P.conj().T).conj().T)
        num = den = 0.0
        gK = np.zeros((N, N), dtype=complex)
        gS_dir = []
        for j in range(m):
            ev, Q = eigs[j], vecs[j]
            num += float(np.sum(ev ** s))
            sq = np.sqrt(ev)
            Sh = (Q * sq) @ Q.conj().T
            Y = 0.5 * (Sh @ K @ Sh + (Sh @ K @ Sh).conj().T)
            ly, qy = eigh(Y)
            den += float(np.sum(ly ** p))
            G = (qy * (ly ** (p - 1.0))) @ qy.conj().T
            gK += Sh @ G @ Sh
            Hh = Q.conj().T @ (K @ Sh @ G + G @ Sh @ K) @ Q
            gS_dir.append(0.5 * (Q @ (Hh / (sq[:, None] + sq[None, :])) @ Q.conj().T + (Q @ (Hh / (sq[:, None] + sq[None, :])) @ Q.conj().T).conj().T))
        val = -(np.log(num) - np.log(den)) / p
        PgP = P.conj().T @ gK @ P
        WM = Pinv.conj().T @ (PgP / (sqD[:, None] + sqD[None, :])) @ Pinv
        WM = 0.5 * (WM + WM.conj().T)
        WN = -0.5 * (K @ WM @ K + (K @ WM @ K).conj().T)
        grads = []
        for j in range(m):
            ev, Q = eigs[j], vecs[j]
            WMh = Q.conj().T @ WM @ Q
            fs = ev ** s
            de_m = ev[:, None] - ev[None, :]
            df_m = fs[:, None] - fs[None, :]
            Ds = np.where(
                np.abs(de_m) > 1e-12 * (ev[:, None] + ev[None, :]),
                df_m / np.where(np.abs(de_m) > 1e-30, de_m, 1.0),
                s * (0.5 * (ev[:, None] + ev[None, :])) ** (s - 1.0)
            )
            gS_K = 0.5 * (Q @ (Ds * WMh) @ Q.conj().T + (Q @ (Ds * WMh) @ Q.conj().T).conj().T) + WN
            gS = -(s / (p * num)) * ((Q * (ev ** (s - 1.0))) @ Q.conj().T) + (1.0 / den) * (gS_dir[j] + gS_K)
            gZ = 2.0 * (0.5 * (gS + gS.conj().T) @ Zs[j])
            grads.append(np.real(gZ).ravel())
            grads.append(np.imag(gZ).ravel())
        return float(val), np.concatenate(grads)

    decay = 0.65 if p > 1.55 else 0.50
    scales = decay ** np.arange(N)
    parts = []
    for _ in range(m):
        parts.append((rng_loc.standard_normal((N, N)) * scales[:, None]).ravel())
        parts.append((rng_loc.standard_normal((N, N)) * scales[:, None]).ravel())
    x0 = np.concatenate(parts)
    res = minimize(obj_grad, x0, jac=True, method="L-BFGS-B", options={"maxiter": maxiter, "ftol": 1e-16, "gtol": 1e-13})
    _, Ss = unpack(res.x)
    # Recompute K and R
    M = sum(matpow(S, s) for S in Ss)
    N_mat = sum(Ss)
    Nmh = matpow(N_mat, -0.5)
    Nh = matpow(N_mat, 0.5)
    K = Nmh @ matpow(Nh @ M @ Nh, 0.5) @ Nmh
    K = 0.5 * (K + K.conj().T)
    R = float(np.exp(-res.fun))
    return R, K, Ss


rng_s5 = np.random.default_rng(50505)
for lbl, p_val, m_val, N_dim, fam in [
    ("5/3", 5.0 / 3.0, 2, 4, "primal"),
    ("7/5", 1.4, 2, 4, "dual"),
    ("7/5", 1.4, 3, 4, "dual"),
    ("7/5", 1.4, 2, 6, "dual"),
    ("5/4", 1.25, 2, 4, "both"),
    ("5/4", 1.25, 3, 4, "both"),
    ("6/5", 1.2, 2, 4, "both"),
    ("6/5", 1.2, 3, 4, "both"),
    ("6/5", 1.2, 2, 6, "both"),
]:
    kap = p_val / (2.0 * (p_val - 1.0))
    L_rg, d_rg, X_rg, err_rg, _ = continue_rg(p_val, m_val, 4 if m_val == 2 else 3, rg_p32)
    assert err_rg < 1e-10
    x_nu, w_nu, s_mu, w_mu = extract_rg_measures(d_rg, X_rg)

    R_ka, K_ka, Ss_ka = optimize_complex_ka(N_dim, m_val, p_val, rng_s5, maxiter=3500)
    Lam_ka = (2.0 ** (2.0 * kap - 1.0)) * (R_ka ** (2.0 * kap))
    assert Lam_ka <= L_rg + 1e-9, f"KA exceeded RG! {Lam_ka} > {L_rg}"

    # Transform to K-eigenbasis (d_0 = 1)
    ld, Qk = eigh(K_ka)
    idx = np.argsort(ld)[::-1]
    ld = ld[idx]
    Qk = Qk[:, idx]
    dd = ld / ld[0]
    sD = np.sqrt(dd)

    sum_E_raw = np.zeros((N_dim, N_dim), dtype=complex)
    H_list = []
    X_list = []
    for j in range(m_val):
        Sj = Qk.conj().T @ Ss_ka[j] @ Qk / (ld[0] ** (2.0 * kap - 2.0))
        Sj = 0.5 * (Sj + Sj.conj().T)
        Gj = matpow(Sj, 1.0 / (kap - 1.0))
        Hj = (1.0 / sD)[:, None] * Gj * (1.0 / sD)[None, :]
        Xj = (1.0 / sD)[:, None] * Hj * (1.0 / sD)[None, :]
        H_list.append(Hj)
        X_list.append(Xj)
        # Exact un-rescaled color-balance term E_j = G_j^k - D G_j^{k-1} D (identically sums to 0 by K N K = M!)
        Ej_raw = matpow(Gj, kap) - (dd[:, None] * Sj) * dd[None, :]
        sum_E_raw += Ej_raw
    bal_err = float(np.linalg.norm(sum_E_raw))
    comm_H = max(float(np.linalg.norm(H_list[a] @ H_list[b] - H_list[b] @ H_list[a])) for a in range(m_val) for b in range(a + 1, m_val))
    assert bal_err < 1e-11 and comm_H > 1e-3, f"Kubo-Ando check failed: bal_err={bal_err}, comm_H={comm_H}"

    # Polish each color onto the EXACT Holden manifold at Lam_UB = Lam_rg * (1 + 1e-4) via continuation from Lam_KA,
    # tracking and asserting genuinely non-diagonal (coupled) polished colors (||Xj_pol - diag|| > 1e-3)!
    L_ub = L_rg * (1.0 + 1e-4)
    keep = np.where(dd >= 1e-4)[0]
    dd_k = dd[keep]
    min_P_all = min_D_all = 1e9
    n_nondiag = 0
    for j in range(m_val):
        Xj_sub = X_list[j][np.ix_(keep, keep)]
        # Diagonal phase gauge alignment (maximally real spanning-tree alignment preserving spectrum of (D, H_j))
        phases = np.ones(len(keep), dtype=complex)
        for a in range(1, len(keep)):
            b_best = int(np.argmax(np.abs(Xj_sub[:a, a])))
            if abs(Xj_sub[b_best, a]) > 1e-12:
                # phases[b] * X_{b,a} * conj(phases[a]) = |X_{b,a}| > 0 => phases[a] = phases[b] * exp(+i * arg(X_{b,a}))
                phases[a] = phases[b_best] * np.exp(1j * np.angle(Xj_sub[b_best, a]))
        Xj_al = (phases[:, None] * Xj_sub) * phases.conj()[None, :]
        Xj_re = np.real(0.5 * (Xj_al + Xj_al.conj().T))
        ev_r, Vr = eigh(Xj_re)
        Xj_re = (Vr * np.maximum(ev_r, 1e-5)) @ Vr.T

        # First polish via smooth 3-step continuation Lam_KA -> L_ub (using least_squares fallback to preserve off-diags!)
        X_cur = Xj_re.copy()
        h_err = 1e9
        for L_step in [Lam_ka, 0.5 * (Lam_ka + L_ub), L_ub]:
            Xt, et = solve_holden_real(dd_k, X_cur, L_step, kap)
            if et > 1e-10:
                # Trust-region least_squares from X_cur preserves the non-diagonal coupled branch!
                nk = len(dd_k)
                triu_k = np.triu_indices(nk)
                sDk_loc = np.sqrt(dd_k)
                Dk_loc = np.diag(dd_k)
                Dsk_loc = dd_k ** (-kap + 0.5)
                wk0, Vk0 = eigh(0.5 * (X_cur + X_cur.T))
                Sk0 = (Vk0 * np.log(np.maximum(wk0, 1e-18))) @ Vk0.T

                def res_ls(xv):
                    try:
                        Sm = np.zeros((nk, nk))
                        Sm[triu_k] = np.clip(xv, -30.0, 12.0)
                        Sm = Sm + Sm.T - np.diag(np.diag(Sm))
                        wl, Vl = eigh(Sm)
                        Xl = (Vl * np.exp(wl)) @ Vl.T
                        Hl = (sDk_loc[:, None] * Xl) * sDk_loc[None, :]
                        Ml = Dk_loc + Hl
                        Gl = (sDk_loc[:, None] * Hl) * sDk_loc[None, :]
                        Zl = (dd_k ** (1.0 - kap))[:, None] * matpow(Gl, kap - 1.0) * (dd_k ** (1.0 - kap))[None, :]
                        Rl = (Dsk_loc[:, None] * matpow(Ml, 2.0 * kap - 1.0) * Dsk_loc[None, :]) - L_step * Zl
                        return Rl[triu_k]
                    except Exception:
                        return np.full(len(triu_k[0]), 1e3)

                sol_ls = least_squares(res_ls, Sk0[triu_k], xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=3000)
                et = float(np.linalg.norm(sol_ls.fun))
                Sm = np.zeros((nk, nk))
                Sm[triu_k] = sol_ls.x
                Sm = Sm + Sm.T - np.diag(np.diag(Sm))
                wl, Vl = eigh(Sm)
                Xt = (Vl * np.exp(wl)) @ Vl.T
            if et < 1e-10:
                X_cur = Xt
                h_err = et
        Xj_pol = X_cur
        if h_err > 1e-10:
            xm_u, xp_u, _, _ = roots_kappa(L_ub, kap)
            mid_x = 0.5 * (xm_u + xp_u)
            X_fb = np.diag(np.where(np.diag(Xj_re) < mid_x, xm_u, xp_u))
            for blend in [0.7, 0.4, 0.0]:
                Xj_pol, h_err = solve_holden_real(dd_k, blend * Xj_re + (1.0 - blend) * X_fb, L_ub, kap)
                if h_err < 1e-10:
                    break
        assert h_err < 1e-10, f"Suite 5 Holden polish failed: h_err={h_err}"
        if float(np.linalg.norm(Xj_pol - np.diag(np.diag(Xj_pol)))) > 1e-3:
            n_nondiag += 1
        # Re-apply complex unitary conjugation U in U(|keep|) to verify complex Hermitian evaluation!
        Zc_k = rng.standard_normal((len(keep), len(keep))) + 1j * rng.standard_normal((len(keep), len(keep)))
        Uc_k, _ = np.linalg.qr(Zc_k)
        sDk = np.sqrt(dd_k)
        Dk_c = Uc_k @ np.diag(dd_k) @ Uc_k.conj().T
        Hk_c = Uc_k @ ((sDk[:, None] * Xj_pol) * sDk[None, :]) @ Uc_k.conj().T
        rd_j = eval_primal_dual_general(Dk_c, Hk_c, L_ub, kap, m_val, x_nu, w_nu, s_mu, w_mu)
        assert rd_j["ok"] and rd_j["holden_err"] < 1e-7
        min_P_all = min(min_P_all, float(rd_j["eP"][0]))
        min_D_all = min(min_D_all, float(rd_j["eD"][0]))
    assert n_nondiag >= 1, f"All colors collapsed to diagonal at p={lbl} m={m_val} N={N_dim}!"
    if fam in ("primal", "both"):
        assert min_P_all >= 1.0 - 1e-9
    if fam in ("dual", "both"):
        assert min_D_all >= 1.0 - 1e-9
    p_s = f"{min_P_all:.6f}" if fam in ("primal", "both") else "  (n/a) "
    d_s = f"{min_D_all:.6f}" if fam in ("dual", "both") else "  (n/a) "
    print(
        f"  Complex KA multi-block p={lbl:4s} m={m_val} N={N_dim} (active={len(keep)}, nondiag={n_nondiag}/{m_val}): "
        f"Lam_KA={Lam_ka:.8f} <= Lam_RG={L_rg:.8f} | ||sum E_j||={bal_err:.1e} | ||[Ha,Hb]||={comm_H:.2e} | @Lam_UB: min(P)={p_s}, min(D)={d_s}"
    )


# ==============================================================================
# SUITE 6: COMPLEX NON-REAL SINGLE-BLOCK HOLDEN RIGIDITY INVESTIGATION (n = 3, 4)
# ==============================================================================
print("\n" + "=" * 100)
print("SUITE 6: COMPLEX NON-REAL SINGLE-BLOCK HOLDEN RIGIDITY (EXACT p=4/3 PROOF + n=3,4 SEARCH)")
print("=" * 100)

print("\n[6A] Exact 4-Line Algebraic Proof Verification at p = 4/3 (n = 3): (M^3 - Lam D H D)_{12} == C_12 w e^{i phi} + Tr(M) u v:")
# Verify the exact algebraic identity on 20 random complex 3x3 Hermitian (D, H) > 0 with gauge-fixed real u=H01, v=H02 and complex w e^{i phi}=H12!
max_alg_err = 0.0
for _ in range(20):
    d1, d2 = rng.uniform(0.1, 0.9, 2)
    D3 = np.diag([1.0, d1, d2])
    a, b, c = rng.uniform(0.5, 2.0, 3)
    u, v, w = rng.uniform(0.05, 0.3, 3)
    phi = rng.uniform(0.2, 2.9)
    H3 = np.array([
        [a, u, v],
        [u, b, w * np.exp(1j * phi)],
        [v, w * np.exp(-1j * phi), c],
    ], dtype=complex)
    M3 = D3 + H3
    Lam_t = rng.uniform(5.0, 15.0)
    lhs = (M3 @ M3 @ M3 - Lam_t * (D3 @ H3 @ D3))[1, 2]
    C12 = (d1 + b) ** 2 + (d1 + b) * (d2 + c) + (d2 + c) ** 2 + u ** 2 + v ** 2 + w ** 2 - Lam_t * d1 * d2
    trM = (1.0 + a) + (d1 + b) + (d2 + c)
    rhs = C12 * w * np.exp(1j * phi) + trM * u * v
    max_alg_err = max(max_alg_err, abs(lhs - rhs))
assert max_alg_err < 1e-13
print(f"  Algebraic identity |(M^3 - Lam D H D)_12 - (C_12 w e^{{i phi}} + Tr(M) u v)| <= {max_alg_err:.2e}!")
print("  => Case 1 (u v w = 0): off-diagonal graph is a forest (zero 3-cycle Bargmann invariant) => diagonal unitary fixes D and makes H real.")
print("  => Case 2 (u v w != 0): gauge-fix u, v > 0; Im=0 forces C_12 w sin(phi) = 0, so sin(phi) != 0 => C_12 = 0 => Tr(M) u v = 0, contradicting Tr(M) > 0!")
print("  => PROVED ANALYTICALLY: EVERY 3x3 complex Hermitian Holden solution at p = 4/3 (reducible or irreducible) is diagonal-unitarily equivalent to a REAL pair!")

print("\n[6B] Gauge-Fixed Complex Multi-Start Searches (n = 3, 4) & Imaginary Jacobian SVDs:")
for lbl, p_val in [("4/3", 4.0 / 3.0), ("5/3", 5.0 / 3.0), ("5/4", 1.25), ("6/5", 1.2)]:
    kap = p_val / (2.0 * (p_val - 1.0))
    L3, d3, X3, err3, _ = continue_rg(p_val, 2, 3, rg_p32)
    assert err3 < 1e-11
    # (i) Imaginary Jacobian SVD on irreducible r=3 RG block (must have 2 exact gauge zeros + 1 nonzero physical mode!)
    sD3 = np.sqrt(d3)
    D3 = np.diag(d3)
    Ds3 = d3 ** (-kap + 0.5)
    w0, V0 = eigh(X3)
    S0 = (V0 * np.log(np.maximum(w0, 1e-16))) @ V0.T
    J_im = np.zeros((3, 3))
    pairs = [(0, 1), (0, 2), (1, 2)]
    eps = 1e-7
    for col, (a_i, b_i) in enumerate(pairs):
        Sq = S0.astype(complex)
        Sq[a_i, b_i] += 1j * eps
        Sq[b_i, a_i] -= 1j * eps
        wq, Vq = eigh(Sq)
        Xq = (Vq * np.exp(wq)) @ Vq.conj().T
        Hq = (sD3[:, None] * Xq) * sD3[None, :]
        Mq = D3 + Hq
        Gq = (sD3[:, None] * Hq) * sD3[None, :]
        Zq = (d3 ** (1.0 - kap))[:, None] * matpow(Gq, kap - 1.0) * (d3 ** (1.0 - kap))[None, :]
        Rq = (Ds3[:, None] * matpow(Mq, 2.0 * kap - 1.0) * Ds3[None, :]) - L3 * Zq
        for row, (r1, r2) in enumerate(pairs):
            J_im[row, col] = Rq[r1, r2].imag / eps
    sv3 = np.linalg.svd(J_im, compute_uv=False)
    assert sv3[0] > 0.5 and sv3[1] < 1e-11 and sv3[2] < 1e-11

    # (ii) 40 gauge-fixed complex 3x3 random starts around coupled scale
    xm3, xp3, _, _ = roots_kappa(L3, kap)
    n_c3 = n_r3 = 0
    for _ in range(40):
        dd = np.sort(np.array([1.0, d3[1] * rng.uniform(0.7, 1.5), d3[2] * rng.uniform(0.5, 2.0)]))[::-1]
        sD = np.sqrt(dd)
        Dc = np.diag(dd)
        Ds = dd ** (-kap + 0.5)
        v0 = np.array([np.log(xm3), -0.3, -0.1, np.log(xp3 * 0.5), -0.2, np.log(xp3 * 0.8), rng.uniform(0.3, 1.5)]) + rng.normal(0.0, 0.3, 7)

        def unpack_c3(v):
            S = np.array([[v[0], v[1], v[2]], [v[1], v[3], v[4] + 1j * v[6]], [v[2], v[4] - 1j * v[6], v[5]]], dtype=complex)
            w, V = eigh(S)
            return (V * np.exp(np.clip(w, -20.0, 10.0))) @ V.conj().T

        def res_c3(v):
            try:
                Xc = unpack_c3(v)
                H = (sD[:, None] * Xc) * sD[None, :]
                M = Dc + H
                G = (sD[:, None] * H) * sD[None, :]
                Z = (dd ** (1.0 - kap))[:, None] * matpow(G, kap - 1.0) * (dd ** (1.0 - kap))[None, :]
                R = (Ds[:, None] * matpow(M, 2.0 * kap - 1.0) * Ds[None, :]) - L3 * Z
                return np.array([R[0, 0].real, R[0, 1].real, R[0, 2].real, R[1, 1].real, R[1, 2].real, R[2, 2].real, R[1, 2].imag])
            except Exception:
                return np.full(7, 1e3)

        sol = root(res_c3, v0, method="hybr", tol=1e-12)
        if float(np.linalg.norm(res_c3(sol.x))) < 1e-9:
            Xc = unpack_c3(sol.x)
            H = (sD[:, None] * Xc) * sD[None, :]
            M = Dc + H
            G = (sD[:, None] * H) * sD[None, :]
            Z = (dd ** (1.0 - kap))[:, None] * matpow(G, kap - 1.0) * (dd ** (1.0 - kap))[None, :]
            if float(np.linalg.norm((Ds[:, None] * matpow(M, 2.0 * kap - 1.0) * Ds[None, :]) - L3 * Z)) < 1e-9:
                if abs(np.imag(Xc[0, 1] * Xc[1, 2] * Xc[2, 0])) > 1e-6:
                    n_c3 += 1
                else:
                    n_r3 += 1
    # (iii) Imaginary Jacobian SVD on irreducible r=4 RG block (3 exact gauge zeros + 3 nonzero physical modes)
    #       + 25 gauge-fixed complex 4x4 starts (13 real vars: 4 diag + 6 real off + 3 gauge-invariant imag phases)!
    L4, d4, X4, err4, _ = continue_rg(p_val, 2, 4, rg_p32)
    assert err4 < 1e-10
    sD4 = np.sqrt(d4)
    D4 = np.diag(d4)
    Ds4 = d4 ** (-kap + 0.5)
    w4, V4 = eigh(X4)
    S4_0 = (V4 * np.log(np.maximum(w4, 1e-16))) @ V4.T
    pairs4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
    J_im4 = np.zeros((6, 6))
    for col, (a_i, b_i) in enumerate(pairs4):
        Sq = S4_0.astype(complex)
        Sq[a_i, b_i] += 1j * eps
        Sq[b_i, a_i] -= 1j * eps
        wq, Vq = eigh(Sq)
        Xq = (Vq * np.exp(wq)) @ Vq.conj().T
        Hq = (sD4[:, None] * Xq) * sD4[None, :]
        Mq = D4 + Hq
        Gq = (sD4[:, None] * Hq) * sD4[None, :]
        Zq = (d4 ** (1.0 - kap))[:, None] * matpow(Gq, kap - 1.0) * (d4 ** (1.0 - kap))[None, :]
        Rq = (Ds4[:, None] * matpow(Mq, 2.0 * kap - 1.0) * Ds4[None, :]) - L4 * Zq
        for row, (r1, r2) in enumerate(pairs4):
            J_im4[row, col] = Rq[r1, r2].imag / eps
    sv4 = np.linalg.svd(J_im4, compute_uv=False)
    assert sv4[2] > 0.1 and sv4[3] < 1e-8 and sv4[5] < 1e-10

    n_c4 = n_r4 = 0
    sig_4 = 0.08 if p_val <= 1.26 else 0.20
    im_amp = 0.25 if p_val <= 1.26 else 0.7
    for _ in range(25):
        dd = np.sort(d4 * np.array([1.0, rng.uniform(0.90, 1.12), rng.uniform(0.85, 1.18), rng.uniform(0.80, 1.25)]))[::-1]
        dd = np.clip(dd, 1e-6, 1.0)
        dd[0] = 1.0
        sD = np.sqrt(dd)
        Dc = np.diag(dd)
        Ds = dd ** (-kap + 0.5)
        v0 = np.array([
            S4_0[0, 0], S4_0[1, 1], S4_0[2, 2], S4_0[3, 3],
            S4_0[0, 1], S4_0[0, 2], S4_0[0, 3], S4_0[1, 2], S4_0[1, 3], S4_0[2, 3],
            rng.uniform(0.05, im_amp), rng.uniform(0.05, im_amp), rng.uniform(0.05, im_amp)
        ]) + rng.normal(0.0, sig_4, 13)

        def unpack_c4(v):
            S = np.zeros((4, 4), dtype=complex)
            S[0, 0], S[1, 1], S[2, 2], S[3, 3] = v[0], v[1], v[2], v[3]
            S[0, 1] = S[1, 0] = v[4]
            S[0, 2] = S[2, 0] = v[5]
            S[0, 3] = S[3, 0] = v[6]
            S[1, 2] = v[7] + 1j * v[10]
            S[2, 1] = np.conj(S[1, 2])
            S[1, 3] = v[8] + 1j * v[11]
            S[3, 1] = np.conj(S[1, 3])
            S[2, 3] = v[9] + 1j * v[12]
            S[3, 2] = np.conj(S[2, 3])
            w, V = eigh(S)
            return (V * np.exp(np.clip(w, -20.0, 10.0))) @ V.conj().T

        def res_c4(v):
            try:
                Xc = unpack_c4(v)
                H = (sD[:, None] * Xc) * sD[None, :]
                M = Dc + H
                G = (sD[:, None] * H) * sD[None, :]
                Z = (dd ** (1.0 - kap))[:, None] * matpow(G, kap - 1.0) * (dd ** (1.0 - kap))[None, :]
                R = (Ds[:, None] * matpow(M, 2.0 * kap - 1.0) * Ds[None, :]) - L4 * Z
                return np.array([
                    R[0, 0].real, R[1, 1].real, R[2, 2].real, R[3, 3].real,
                    R[0, 1].real, R[0, 2].real, R[0, 3].real, R[1, 2].real, R[1, 3].real, R[2, 3].real,
                    R[1, 2].imag, R[1, 3].imag, R[2, 3].imag,
                ])
            except Exception:
                return np.full(13, 1e3)

        sol = root(res_c4, v0, method="hybr", tol=1e-12)
        if float(np.linalg.norm(res_c4(sol.x))) < 1e-9:
            Xc = unpack_c4(sol.x)
            H = (sD[:, None] * Xc) * sD[None, :]
            M = Dc + H
            G = (sD[:, None] * H) * sD[None, :]
            Z = (dd ** (1.0 - kap))[:, None] * matpow(G, kap - 1.0) * (dd ** (1.0 - kap))[None, :]
            if float(np.linalg.norm((Ds[:, None] * matpow(M, 2.0 * kap - 1.0) * Ds[None, :]) - L4 * Z)) < 1e-9:
                bargs = [abs(np.imag(Xc[i, j] * Xc[j, k] * Xc[k, i])) for i in range(4) for j in range(i + 1, 4) for k in range(j + 1, 4)]
                if max(bargs) > 1e-6:
                    n_c4 += 1
                else:
                    n_r4 += 1

    assert n_r3 >= 1 and n_r4 >= 1
    print(
        f"  p={lbl:4s}: 3x3 imag-J=[{sv3[0]:.3f}, {sv3[1]:.1e}] (real={n_r3:2d}, cplx={n_c3}) "
        f"| 4x4 imag-J=[{sv4[0]:.2f}..{sv4[2]:.2f}, {sv4[3]:.1e}] (real={n_r4:2d}, cplx={n_c4})"
    )

print("\n" + "=" * 100)
print(f"ALL 6 ADVERSARIAL STRESS SUITES PASSED WITH ZERO DEFECTS in {time.time() - t_start:.2f}s!")
print("=" * 100)
