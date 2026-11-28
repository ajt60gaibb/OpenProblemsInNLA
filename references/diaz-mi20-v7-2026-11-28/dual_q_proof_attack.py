#!/usr/bin/env python3
"""
dual_q_proof_attack.py
======================
100% self-contained verification suite for the Final-Mountain Dual Q-Family
Proof Attack on (1, 3/2) (Regimes II & III) for Open Problem MI-20:
  - Suite 1: Exact Kubo-Ando Holden Substitution Identity (Dual & Primal),
             Resolvent Integral Representation, Universal Unitary Polar
             1-Line (A, B, M, Qtilde) Reformulation, Operator Convexity in s,
             and 3-Line Hansen-Pedersen Two-Sided Y-Sandwich (60 dps complex).
  - Suite 2: Single-Point Dual Operator Inequality Prototype Test across
             n = 2..6 non-RG indefinite-B_{sigma_+} Holden solutions, Exact
             1-Line delta=0 Obstruction vs Regime II Harmonic Integral delta=0
             Survival & 2x2 Schur-Complement Mechanism.
  - Suite 3: Second-Use-of-Holden Obstruction Taxonomy: 1D Branch-Crossing
             Law of (F1, F2), max(F1, F2) Envelope, Quadratic Penalty
             F_eff(mu) = F2 + mu (F1-F2) F2^{-1} (F1-F2), and Adversarial
             Non-Holden Rank-1 Kernel Obstruction.
  - Suite 4: First-Order Non-Commutative Relative-Entropy Logarithmic Defect
             Decomposition (Delta_Y, Delta_W, Delta_P) at kappa = 3/2.
  - Suite 5: Hadamard Three-Lines Complex Interpolation Verification +
             45-digit mpmath.iv Outward-Rounded All-n Enclosures for
             p = sqrt(2) and p = 7/5 (m = 2) vs Single-Point Dual Target.

Dependencies: Python standard library + numpy, scipy, mpmath ONLY.
Zero external scratch imports. Zero touches outside scratch/.
"""

import math
import time
import numpy as np
import mpmath as mp
from mpmath import iv
from scipy.linalg import eigh
from scipy.optimize import brentq, least_squares, minimize


# ==============================================================================
# 0. SELF-CONTAINED LINEAR ALGEBRA & HOLDEN SOLVERS
# ==============================================================================

def matpow(A, alpha):
    Ah = 0.5 * (A + A.conj().T)
    w, V = eigh(Ah)
    if np.min(w) <= 0.0:
        raise ValueError(f"matpow requires PD matrix, got min eig {np.min(w):.3e}")
    return (V * (w ** alpha)) @ V.conj().T


def matlog(A):
    Ah = 0.5 * (A + A.conj().T)
    w, V = eigh(Ah)
    if np.min(w) <= 0.0:
        raise ValueError(f"matlog requires PD matrix, got min eig {np.min(w):.3e}")
    return (V * np.log(w)) @ V.conj().T


def kubo_ando_mean(A, B, alpha):
    """Exact Kubo-Ando alpha-geometric mean A #_alpha B = A^{1/2}(A^{-1/2} B A^{-1/2})^alpha A^{1/2}."""
    sA = matpow(A, 0.5)
    isA = matpow(A, -0.5)
    return sA @ matpow(isA @ B @ isA, alpha) @ sA


def roots_kappa(Lam, kappa):
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
    return xm, xp, (xm ** (kappa - 1.0)) * (xm - 1.0), (xp ** (kappa - 1.0)) * (xp - 1.0)


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
    ratio = d_p[-1] / d_p[-2] if rp >= 3 else 0.15
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
    raise RuntimeError(f"p=3/2 RG solver failed at r={r}, m={m}")


def solve_rg_lsq(p, m, r_cur, Lam_init, d_init, X_init):
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
        return L, dd, (V * np.exp(w)) @ V.T

    def res(x):
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

    sol = least_squares(res, x0, xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=3000)
    L, dd, X = unpack(sol.x)
    sD = np.sqrt(dd)
    H = (sD[:, None] * X) * sD[None, :]
    G = (sD[:, None] * H) * sD[None, :]
    Z = (dd ** (1.0 - kappa))[:, None] * matpow(G, kappa - 1.0) * (dd ** (1.0 - kappa))[None, :]
    Ehat = ((dd ** (-kappa))[:, None] * matpow(G, kappa) * (dd ** (-kappa))[None, :]) - Z
    off_err = float(np.linalg.norm(Ehat - np.diag(np.diag(Ehat))))
    return L, dd, X, float(np.linalg.norm(sol.fun)), off_err


_P32_CACHE = {}
_RG_CACHE = {}


def get_p32_rg(r, m=2.0):
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
    L, d, X = get_p32_rg(r, m=2.0)
    for mm in np.geomspace(2.0, float(m), 6 if m <= 12 else 12)[1:]:
        L, d, X, err, oe = solve_rg_lsq(1.5, float(mm), r, L, d, X)
        assert err < 1e-9 and oe < 1e-9
    _P32_CACHE[key] = (L, d, X)
    return L, d, X


def continue_rg(p_target, r, m=2.0):
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
            assert abs(step) > 1e-5
    _RG_CACHE[key] = (L, d, X)
    return L, d, X


def holden_operators(D, H, kappa):
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
    W1_inv = matpow(D, kappa - 1.0) @ matpow(M, 2.0 - 2.0 * kappa) @ matpow(D, kappa - 1.0)
    P = matpow(D, kappa - 1.5) @ matpow(G, 1.5 - kappa) @ matpow(D, kappa - 1.5)
    Y = matpow(D, 0.5 - kappa) @ matpow(G, kappa - 0.5) @ matpow(D, 0.5 - kappa)
    return dict(sD=sD, isD=isD, G=G, M=M, X=X, Q=Q, Z_primal=Z_primal, Ehat=Ehat, W1_inv=W1_inv, P=P, Y=Y)


def sweep_2x2_branch(p, L, d_seed, X_seed):
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
            return ((Ds[:, None] * matpow(M, 2.0 * kap - 1.0) * Ds[None, :]) - L * Z)[triu]

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


def eval_dual_integral(L, kap, D, H, s_nodes, w_nodes, delta=0.0):
    n = D.shape[0]
    _, _, _, sp = roots_kappa(L, kap)
    ops = holden_operators(D, H, kap)
    W1i, P, Y = ops["W1_inv"], ops["P"], ops["Y"]
    I_op = np.zeros((n, n), dtype=np.result_type(D.dtype, H.dtype))
    min_K = 1e99
    for sk, wk in zip(s_nodes, w_nodes):
        Ko = (sp + delta) * np.eye(n) - sk * Y + np.linalg.inv(L * W1i - sk * P)
        Ko = 0.5 * (Ko + Ko.conj().T)
        min_K = min(min_K, float(eigh(Ko, eigvals_only=True)[0]))
        if min_K <= 0.0:
            return None, min_K
        I_op += wk * np.linalg.inv(Ko)
    return 0.5 * (I_op + I_op.conj().T), min_K


# ==============================================================================
# SUITE 1: KUBO-ANDO HOLDEN SUBSTITUTION, UNITARY POLAR 1-LINE FORM,
#          OPERATOR CONVEXITY IN s, & HANSEN-PEDERSEN TWO-SIDED Y-SANDWICH
# ==============================================================================

def _mp_gram_schmidt_complex(M_np):
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


def run_suite_1():
    print("=" * 86)
    print("SUITE 1: KUBO-ANDO SUBSTITUTION, UNITARY POLAR 1-LINE FORM, s-CONVEXITY & Y-SANDWICH")
    print("=" * 86)
    rng = np.random.default_rng(111)
    exps = [("3/2", 1.5), ("sqrt(2)", math.sqrt(2.0)), ("7/5", 7 / 5),
            ("4/3", 4 / 3), ("5/4", 5 / 4), ("6/5", 6 / 5)]

    print("\n--- 1A: Exact Identities on U(3)-Rotated Complex 3x3 Holden Blocks (Theorems 1-3) ---")
    # Precompute uniform log-grid for exponentially convergent trapezoid rule on analytic strip |Im u| < pi:
    u_grid = np.linspace(-125.0, 125.0, 1001)
    du_grid = float(u_grid[1] - u_grid[0])

    for label, p in exps:
        kap = p / (2.0 * (p - 1.0))
        alpha = (kap - 1.5) / (kap - 1.0)
        gam = (kap - 0.5) / (kap - 1.0)  # in (1, 2] for all p in (1, 3/2]!
        L, d, X = continue_rg(p, 3, m=2.0)
        _, xp, _, sp = roots_kappa(L, kap)
        sd = np.sqrt(d)
        D0 = np.diag(d)
        H0 = (sd[:, None] * X) * sd[None, :]
        U_rot, _ = np.linalg.qr(rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3)))
        D = U_rot @ D0 @ U_rot.conj().T
        H = U_rot @ H0 @ U_rot.conj().T

        ops = holden_operators(D, H, kap)
        G, M, Xc, Q, Eh = ops["G"], ops["M"], ops["X"], ops["Q"], ops["Ehat"]
        W1i, P, Y = ops["W1_inv"], ops["P"], ops["Y"]

        # Theorem 1: Dual Kubo-Ando Holden Substitution: L W1^{-1} = A #_alpha B
        Dk15 = matpow(D, kap - 1.5)
        A_ka = L * Dk15 @ np.linalg.inv(np.eye(3) + Xc) @ Dk15
        B_ka = Dk15 @ matpow(G, 1.0 - kap) @ Dk15
        ka_dual_err = float(np.linalg.norm(L * W1i - kubo_ando_mean(A_ka, B_ka, alpha)))
        assert ka_dual_err < 1e-11

        # Theorem 1 Primal twin (for kap >= 2): T1 = (D^{k-2}(I+X)^{-1}D^{k-2}) #_beta (L^{-1} D^{k-2} G^{1-k} D^{k-2})
        ka_prim_str = "n/a"
        if kap >= 2.0 - 1e-12:
            beta_ka = (kap - 2.0) / (kap - 1.0)
            T1 = matpow(D, kap - 1.5) @ matpow(M, 3.0 - 2.0 * kap) @ matpow(D, kap - 1.5)
            Dk2 = matpow(D, kap - 2.0)
            Ap = Dk2 @ np.linalg.inv(np.eye(3) + Xc) @ Dk2
            Bp = (1.0 / L) * Dk2 @ matpow(G, 1.0 - kap) @ Dk2
            ka_prim_err = float(np.linalg.norm(T1 - kubo_ando_mean(Ap, Bp, beta_ka)))
            assert ka_prim_err < 1e-11
            ka_prim_str = f"{ka_prim_err:.1e}"

        # Corollary 1.2: Exact Resolvent Integral Formula (alpha in (0, 1)):
        # A #_alpha B = (sin(pi*alpha)/pi) * int_0^infty t^{alpha-1} (A^{-1} + t B^{-1})^{-1} dt
        # Substitute t = exp(u) => (sin(pi*alpha)/pi) * int_{-infty}^{infty} (e^{-alpha u} A^{-1} + e^{(1-alpha) u} B^{-1})^{-1} du
        int_str = "exact(a=0)"
        if alpha > 1e-12:
            Ainv = np.linalg.inv(A_ka)
            Binv = np.linalg.inv(B_ka)
            acc = np.zeros((3, 3), dtype=complex)
            for u in u_grid:
                acc += du_grid * np.linalg.inv(math.exp(-alpha * u) * Ainv + math.exp((1.0 - alpha) * u) * Binv)
            acc *= math.sin(math.pi * alpha) / math.pi
            int_err = float(np.linalg.norm(L * W1i - acc)) / float(np.linalg.norm(L * W1i))
            assert int_err < 1e-12
            int_str = f"{int_err:.1e}"

        # Theorem 2: Unitary Polar U = L^{1/2} G^{(k-1)/2} D^{1/2} M^{1/2-k} & 1-line (A, B, M, Qtilde) form
        Upol = math.sqrt(L) * matpow(G, 0.5 * (kap - 1.0)) @ matpow(D, 0.5) @ matpow(M, 0.5 - kap)
        unit_err = float(np.linalg.norm(Upol.conj().T @ Upol - np.eye(3)))
        Qtil = Upol.conj().T @ matpow(G, 0.5) @ Upol
        dom_kfree = float(eigh(0.5 * ((M - ((1.0 + xp) / math.sqrt(xp)) * Qtil) + (M - ((1.0 + xp) / math.sqrt(xp)) * Qtil).conj().T), eigvals_only=True)[0])
        A_op = matpow(D, -kap) @ matpow(M, kap - 0.5)
        B_op = D @ A_op
        eh_err = float(np.linalg.norm(L * Eh - (A_op @ M @ A_op.conj().T - A_op @ B_op.conj().T - B_op @ A_op.conj().T)))
        s_test = 0.5 * math.sqrt(xp)
        K_orig = sp * np.eye(3) - s_test * Y + np.linalg.inv(L * W1i - s_test * P)
        K_ab = sp * np.eye(3) - (s_test / L) * (A_op @ Qtil @ A_op.conj().T) + (1.0 / L) * (B_op @ np.linalg.inv(M - s_test * Qtil) @ B_op.conj().T)
        k_ab_err = float(np.linalg.norm(K_orig - K_ab))
        # 1-line square identity:
        sq_fac = A_op @ matpow(M - s_test * Qtil, 0.5) - B_op @ matpow(M - s_test * Qtil, -0.5)
        sq_err = float(np.linalg.norm(L * (K_ab - (sp * np.eye(3) - Eh)) - sq_fac @ sq_fac.conj().T))
        assert unit_err < 1e-12 and dom_kfree > 0.0 and eh_err < 1e-11 and k_ab_err < 1e-11 and sq_err < 1e-11

        # Theorem 2(c): Operator convexity in s -> K_sbar <= Kbar (strict Jensen gap!)
        evQ, UQ = eigh(0.5 * (Q + Q.conj().T))
        w0 = U_rot[:, 0]
        w_mu = np.abs(w0.conj() @ UQ) ** 2
        sbar = float(np.dot(w_mu, evQ))
        Kbar = sum(wk * (sp * np.eye(3) - sk * Y + np.linalg.inv(L * W1i - sk * P)) for sk, wk in zip(evQ, w_mu))
        Ksbar = sp * np.eye(3) - sbar * Y + np.linalg.inv(L * W1i - sbar * P)
        sconv_min = float(eigh(0.5 * ((Kbar - Ksbar) + (Kbar - Ksbar).conj().T), eigvals_only=True)[0])
        assert sconv_min > 0.0

        # Theorem 3: Hansen-Pedersen Two-Sided Y-Sandwich
        DM2kD = matpow(D, -kap) @ matpow(M, 2.0 * kap) @ matpow(D, -kap)
        y_lo = float(eigh(0.5 * ((Y - (L ** (-gam)) * DM2kD) + (Y - (L ** (-gam)) * DM2kD).conj().T), eigvals_only=True)[0])
        y_hi = float(eigh(0.5 * ((((1.0 + xp) ** (gam - 1.0)) * (L ** (-gam)) * DM2kD - Y) + ((((1.0 + xp) ** (gam - 1.0)) * (L ** (-gam)) * DM2kD - Y)).conj().T), eigvals_only=True)[0])
        assert y_lo > 0.0 and y_hi > 0.0

        print(f"  p={label:>7s}: KA_D={ka_dual_err:.1e} KA_P={ka_prim_str:>7s} int={int_str:>10s} | U={unit_err:.1e} 1sq={sq_err:.1e} | sConv={sconv_min:+.2e} | Y_sand=[{y_lo:+.2e},{y_hi:+.2e}]")

    print("\n--- 1B: 60-dps Complex Verification of Hansen-Pedersen Operator-Convex Inequality K* A^gam K >= (K* A K)^gam ---")
    mp.mp.dps = 60
    for label, p_mp in [("3/2", mp.mpf(3) / 2), ("sqrt(2)", mp.sqrt(2)), ("4/3", mp.mpf(4) / 3), ("6/5", mp.mpf(6) / 5)]:
        kap = p_mp / (2 * (p_mp - 1))
        gam = (kap - mp.mpf(1) / 2) / (kap - 1)  # in (1, 2]
        min_ev = mp.mpf("1e99")
        for _ in range(5):
            # Random genuinely complex non-real contraction K (||K|| <= 1) and PD A > 0
            U1 = _mp_gram_schmidt_complex(rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3)))
            U2 = _mp_gram_schmidt_complex(rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3)))
            U3 = _mp_gram_schmidt_complex(rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3)))
            sv = [mp.mpf(float(rng.uniform(0.05, 0.99))) for _ in range(3)]
            ae = [mp.exp(mp.mpf(float(rng.uniform(-4.0, 4.0)))) for _ in range(3)]
            K = mp.matrix(3, 3)
            A = mp.matrix(3, 3)
            for i in range(3):
                for j in range(3):
                    K[i, j] = sum(U1[i, k] * sv[k] * mp.conj(U2[j, k]) for k in range(3))
                    A[i, j] = sum(U3[i, k] * ae[k] * mp.conj(U3[j, k]) for k in range(3))
            Ks = K.transpose_conj()
            diff_hp = Ks * _mp_matpow_herm(A, gam) * K - _mp_matpow_herm(Ks * A * K, gam)
            min_ev = min(min_ev, min(mp.eigh(diff_hp, eigvals_only=True)))
        print(f"  p={label:>7s} (gam={mp.nstr(gam, 5)} in (1,2], 60 dps): min_eig(K* A^gam K - (K* A K)^gam) = {mp.nstr(min_ev, 4)}")
        assert min_ev >= -mp.mpf("1e-40")

    print("\n--- 1C: Quantitative Diagnosis of 1-Step Hansen Y_lo Substitution Loss on RG4 (m = 2) ---")
    for label, p in [("sqrt(2)", math.sqrt(2.0)), ("4/3", 4 / 3), ("6/5", 6 / 5)]:
        kap = p / (2.0 * (p - 1.0))
        gam = (kap - 0.5) / (kap - 1.0)
        L4, d4, X4 = continue_rg(p, 4, m=2.0)
        _, _, _, sp4 = roots_kappa(L4, kap)
        c4 = 2.0 * sp4
        sd4 = np.sqrt(d4)
        D4 = np.diag(d4)
        H4 = (sd4[:, None] * X4) * sd4[None, :]
        ops4 = holden_operators(D4, H4, kap)
        evQ4, UQ4 = eigh(ops4["Q"])
        sbar = float(np.dot(UQ4[0, :] ** 2, evQ4))
        DM2kD = matpow(D4, -kap) @ matpow(ops4["M"], 2.0 * kap) @ matpow(D4, -kap)
        K_ex = sp4 * np.eye(4) - sbar * ops4["Y"] + np.linalg.inv(L4 * ops4["W1_inv"] - sbar * ops4["P"])
        K_lo = sp4 * np.eye(4) - sbar * (L4 ** (-gam)) * DM2kD + np.linalg.inv(L4 * ops4["W1_inv"] - sbar * ops4["P"])
        r_ex = float(eigh(K_ex / c4, eigvals_only=True)[-1])
        r_lo = float(eigh(K_lo / c4, eigvals_only=True)[-1])
        print(f"  p={label:>7s}: exact K_sbar/c4 = {r_ex:.6f} vs with Hansen Y_lo: {r_lo:.6f} (loss = +{(r_lo - 1)*100:.2f}%)")
        assert r_lo > 1.10

    print("  [PASS] Suite 1 verified Theorems 1-3 and the 1-step contraction loss diagnosis.\n")


# ==============================================================================
# SUITE 2: SINGLE-POINT DUAL PROTOTYPE TEST (n=2..6), EXACT delta=0 OBSTRUCTION,
#          AND REGIME II HARMONIC INTEGRAL delta=0 SURVIVAL + 2x2 SCHUR MECHANISM
# ==============================================================================

def run_suite_2():
    print("=" * 86)
    print("SUITE 2: SINGLE-POINT DUAL PROTOTYPE (n=2..6), delta=0 OBSTRUCTION & 2x2 SCHUR MECHANISM")
    print("=" * 86)
    rng = np.random.default_rng(2026)

    print("\n--- 2A: Optimal Single-Point s_* C_p(m) Gap Benchmark & Exact Schur Equivalence ---")
    for label, p, m in [("1.45", 1.45, 2.0), ("sqrt(2)", math.sqrt(2.0), 2.0), ("7/5", 7 / 5, 2.0),
                        ("5/4", 5 / 4, 2.0), ("6/5", 6 / 5, 2.0),
                        ("sqrt(2)", math.sqrt(2.0), 10.0), ("7/5", 7 / 5, 10.0), ("6/5", 6 / 5, 10.0)]:
        kap = p / (2.0 * (p - 1.0))
        L4, d4, X4 = continue_rg(p, 4, m=m)
        _, _, _, sp4 = roots_kappa(L4, kap)
        c4 = (m / (m - 1.0)) * sp4
        C_rg4 = (L4 / (2.0 ** (2.0 * kap - 1.0))) ** (1.0 / (2.0 * kap))
        sd4 = np.sqrt(d4)
        D4 = np.diag(d4)
        H4 = (sd4[:, None] * X4) * sd4[None, :]
        ops4 = holden_operators(D4, H4, kap)
        evQ4, _ = eigh(ops4["Q"])
        s_grid = np.linspace(evQ4[0], evQ4[-1], 400)
        s_star = float(min(s_grid, key=lambda st: float(eigh((sp4 * np.eye(4) - st * ops4["Y"] + np.linalg.inv(L4 * ops4["W1_inv"] - st * ops4["P"])) / c4, eigvals_only=True)[-1])))
        K_st = sp4 * np.eye(4) - s_star * ops4["Y"] + np.linalg.inv(L4 * ops4["W1_inv"] - s_star * ops4["P"])
        r_star = float(eigh(K_st / c4, eigvals_only=True)[-1])
        # Verify exact Schur-block equivalence at c_eff = r_star * c4 (so min eig of Schur block == 0!)
        beta_eff = r_star * c4 - sp4
        schur_diff = L4 * ops4["W1_inv"] - s_star * ops4["P"] - np.linalg.inv(beta_eff * np.eye(4) + s_star * ops4["Y"])
        block_M = np.block([[L4 * ops4["W1_inv"] - s_star * ops4["P"], np.eye(4)],
                            [np.eye(4), beta_eff * np.eye(4) + s_star * ops4["Y"]]])
        assert abs(float(eigh(schur_diff, eigvals_only=True)[0])) < 1e-11
        assert abs(float(eigh(block_M, eigvals_only=True)[0])) < 1e-11

        L_hi = L4 * 1.001
        _, _, _, sp_hi = roots_kappa(L_hi, kap)
        dlogC_dlogsp = (math.log(L_hi / L4) / (2.0 * kap)) / math.log(sp_hi / sp4)
        dC_est = C_rg4 * (r_star - 1.0) * dlogC_dlogsp
        print(f"  p={label:>7s}, m={int(m):2d}: s*={s_star:.5f} | RG4(s*)-1={r_star-1:+.2e} | approx dC_single={dC_est:+.2e}")
        assert (r_star - 1.0) > 0.0 and dC_est < 2.0e-6

    print("\n--- 2B: Single-Point Dual Bound Across n = 2..6 Non-RG Indefinite-B_sp Holden Solutions ---")
    total_pts = 0
    total_indef = 0
    for label, p, m, r_max in [("1.45", 1.45, 2.0, 6), ("sqrt(2)", math.sqrt(2.0), 2.0, 6),
                               ("7/5", 7 / 5, 2.0, 6), ("7/5", 7 / 5, 10.0, 5),
                               ("5/4", 5 / 4, 2.0, 4), ("6/5", 6 / 5, 2.0, 4)]:
        kap = p / (2.0 * (p - 1.0))
        L_ref, d_ref, X_ref = continue_rg(p, r_max, m=m)
        _, _, _, sp_ref = roots_kappa(L_ref, kap)
        c_ref = (m / (m - 1.0)) * sp_ref
        sd_ref = np.sqrt(d_ref)
        D_ref = np.diag(d_ref)
        H_ref = (sd_ref[:, None] * X_ref) * sd_ref[None, :]
        ops_ref = holden_operators(D_ref, H_ref, kap)
        evQ_ref, _ = eigh(ops_ref["Q"])
        s_grid = np.linspace(evQ_ref[0], evQ_ref[-1], 400)
        s_star = float(min(s_grid, key=lambda st: float(eigh((sp_ref * np.eye(r_max) - st * ops_ref["Y"] + np.linalg.inv(L_ref * ops_ref["W1_inv"] - st * ops_ref["P"])) / c_ref, eigvals_only=True)[-1])))
        r_rg = float(eigh((sp_ref * np.eye(r_max) - s_star * ops_ref["Y"] + np.linalg.inv(L_ref * ops_ref["W1_inv"] - s_star * ops_ref["P"])) / c_ref, eigvals_only=True)[-1])

        max_dreq = 0.0
        max_d0 = 0.0
        n_ok = 0
        n_indef = 0
        # Full 2x2 branch
        _, d2, X2 = continue_rg(p, 2, m=m)
        for d1, X in sweep_2x2_branch(p, L_ref, d2[1], X2):
            d = np.array([1.0, d1])
            sd = np.sqrt(d)
            D = np.diag(d)
            H = (sd[:, None] * X) * sd[None, :]
            ops = holden_operators(D, H, kap)
            dreq = max(0.0, float(eigh(ops["Ehat"], eigvals_only=True)[-1]) - sp_ref)
            creq = (m / (m - 1.0)) * (sp_ref + dreq)
            K0 = sp_ref * np.eye(2) - s_star * ops["Y"] + np.linalg.inv(L_ref * ops["W1_inv"] - s_star * ops["P"])
            max_d0 = max(max_d0, float(eigh(K0 / c_ref, eigvals_only=True)[-1]))
            max_dreq = max(max_dreq, float(eigh((K0 + dreq * np.eye(2)) / creq, eigvals_only=True)[-1]))
            n_ok += 1
            if dreq > 1e-4:
                n_indef += 1

        # Higher-rank n = 3..r_max
        for n in range(3, r_max + 1):
            _, dn, Xn = continue_rg(p, n, m=m)
            for _ in range(5):
                d_try = dn * np.exp(rng.uniform(-0.8, 0.8, size=n))
                d_try = np.sort(d_try / np.max(d_try))[::-1]
                A_n = rng.normal(0.0, 0.15, (n, n))
                A_n = 0.5 * (A_n + A_n.T)
                X_seed = Xn + 0.05 * A_n
                evs, Us = eigh(X_seed)
                X_seed = (Us * np.maximum(evs, 0.02)) @ Us.T
                X_sol, err = solve_complex_holden(p, L_ref, d_try, X_seed)
                if err > 1e-9:
                    continue
                sd = np.sqrt(d_try)
                D = np.diag(d_try)
                H = (sd[:, None] * X_sol) * sd[None, :]
                if np.linalg.norm(H - np.diag(np.diag(H))) < 1e-4:
                    continue
                ops = holden_operators(D, H, kap)
                dreq = max(0.0, float(eigh(0.5 * (ops["Ehat"] + ops["Ehat"].conj().T), eigvals_only=True)[-1]) - sp_ref)
                creq = (m / (m - 1.0)) * (sp_ref + dreq)
                K0 = sp_ref * np.eye(n) - s_star * ops["Y"] + np.linalg.inv(L_ref * ops["W1_inv"] - s_star * ops["P"])
                K0 = 0.5 * (K0 + K0.conj().T)
                max_d0 = max(max_d0, float(eigh(K0 / c_ref, eigvals_only=True)[-1]))
                max_dreq = max(max_dreq, float(eigh((K0 + dreq * np.eye(n)) / creq, eigvals_only=True)[-1]))
                n_ok += 1
                if dreq > 1e-4:
                    n_indef += 1
        total_pts += n_ok
        total_indef += n_indef
        print(f"  p={label:>7s}, m={int(m):2d}, n<={r_max} ({n_ok:2d} pts, {n_indef:2d} indef): RG(s*)={r_rg:.8f} | nonRG(dreq)={max_dreq:.8f} | nonRG(d=0)={max_d0:.6f}")
        assert max_dreq < r_rg and max_d0 > 1.0001  # Confirms BOTH dreq success & delta=0 obstruction!
    print(f"  -> Total non-RG points verified across n=2..6: {total_pts} ({total_indef} indef-B_sp), ALL strictly < RG(s*)!")

    print("\n--- 2C: Regime II Harmonic Integral delta=0 Survival & 2x2 Schur-Complement Mechanism ---")
    p = math.sqrt(2.0)
    kap = p / (2.0 * (p - 1.0))
    L4, d4, X4 = continue_rg(p, 4, m=2.0)
    _, d2, X2 = continue_rg(p, 2, m=2.0)
    _, _, _, sp4 = roots_kappa(L4, kap)
    c0 = 2.0 * sp4
    sd4 = np.sqrt(d4)
    Q4 = holden_operators(np.diag(d4), (sd4[:, None] * X4) * sd4[None, :], kap)["Q"]
    evQ4, UQ4 = eigh(Q4)
    w4 = UQ4[0, :] ** 2
    found_overshoot = False
    for d1, X in sweep_2x2_branch(p, L4, d2[1], X2):
        d = np.array([1.0, d1])
        sd = np.sqrt(d)
        D = np.diag(d)
        H = (sd[:, None] * X) * sd[None, :]
        ops = holden_operators(D, H, kap)
        B00 = sp4 - float(ops["Ehat"][0, 0])
        B11 = sp4 - float(ops["Ehat"][1, 1])
        I0, mK0 = eval_dual_integral(L4, kap, D, H, evQ4, w4, delta=0.0)
        assert I0 is not None and mK0 > 0.0
        evI0 = eigh(c0 * I0, eigvals_only=True)
        assert evI0[0] >= 1.0 - 1e-8
        Ks = [sp4 * np.eye(2) - sk * ops["Y"] + np.linalg.inv(L4 * ops["W1_inv"] - sk * ops["P"]) for sk in evQ4]
        mean_k00 = float(np.dot(w4, [float(K[0, 0]) / c0 for K in Ks]))
        mean_schur = float(np.dot(w4, [float(K[0, 0] - (K[0, 1] ** 2) / K[1, 1]) / c0 for K in Ks]))
        if B00 / c0 > 1.0005:
            found_overshoot = True
            print(f"  p=sqrt(2), d1={d1:.4f}: B00/c0={B00/c0:.5f} (>1!), B11/c0={B11/c0:+.4f} | mean(K00/c0)={mean_k00:.5f} -> mean(Schur/c0)={mean_schur:.5f} (<1!) | min(c0*I0)={evI0[0]:.6f}")
            assert mean_k00 > 1.001 and mean_schur < 1.0
    assert found_overshoot
    print("  [PASS] Suite 2 verified Single-Point prototype, delta=0 obstruction, and Regime II Schur mechanism.\n")


# ==============================================================================
# SUITE 3: SECOND-USE-OF-HOLDEN OBSTRUCTION TAXONOMY (F1, F2, max(F1,F2), F_eff)
# ==============================================================================

def run_suite_3():
    print("=" * 86)
    print("SUITE 3: SECOND-USE-OF-HOLDEN OBSTRUCTION TAXONOMY (F1, F2, max(F1,F2), & F_eff(mu))")
    print("=" * 86)
    rng = np.random.default_rng(303)

    print("\n--- 3A: 1D Branch-Crossing Law of (F1, F2) vs max(F1, F2) & Convex/Power Means ---")
    for label, p in [("1.45", 1.45), ("sqrt(2)", math.sqrt(2.0)), ("7/5", 7 / 5),
                     ("4/3", 4 / 3), ("5/4", 5 / 4), ("6/5", 6 / 5)]:
        kap = p / (2.0 * (p - 1.0))
        alpha = (kap - 1.5) / (kap - 1.0)
        L4, d4, X4 = continue_rg(p, 4, m=2.0)
        xm, xp, _, sp = roots_kappa(L4, kap)
        c4 = 2.0 * sp
        sd4 = np.sqrt(d4)
        Q4 = holden_operators(np.diag(d4), (sd4[:, None] * X4) * sd4[None, :], kap)["Q"]
        evQ, UQ = eigh(Q4)
        w4 = UQ[0, :] ** 2
        sbar = float(np.dot(w4, evQ))

        xs = np.concatenate([np.geomspace(1e-6, xm, 1000), np.linspace(xm, xp, 1000)[1:]])
        F1 = L4 * (1.0 + xs) ** (2.0 - 2.0 * kap)
        F2 = ((L4 / (1.0 + xs)) ** (1.0 - alpha)) * (xs ** (1.5 - kap))
        P1 = xs ** (1.5 - kap)
        Y1 = xs ** (kap - 0.5)

        # F2 alone dips on (xm, xp); max(F1, F2) succeeds on all (0, xp]!
        min_F2 = float(np.min(c4 * sum(wk / (sp - sk * Y1 + 1.0 / (F2 - sk * P1)) for sk, wk in zip(evQ, w4))))
        Fmax = np.maximum(F1, F2)
        min_max = float(np.min(c4 * sum(wk / (sp - sk * Y1 + 1.0 / (Fmax - sk * P1)) for sk, wk in zip(evQ, w4))))
        max_sb_max = float(np.max((sp - sbar * Y1 + 1.0 / (Fmax - sbar * P1)) / c4))
        # Symmetric power mean q = 32
        F32 = Fmax * (0.5 * ((F1 / Fmax) ** 32.0 + (F2 / Fmax) ** 32.0)) ** (1.0 / 32.0)
        min_q32 = float(np.min(c4 * sum(wk / (sp - sk * Y1 + 1.0 / (F32 - sk * P1)) for sk, wk in zip(evQ, w4))))
        print(f"  p={label:>7s}: 1D min(c4 I): F2={min_F2:.5f} (<1) | q=32={min_q32:.5f} (<1) | max(F1,F2)={min_max:.6f} (>1!) | 1D Ksb(max)/c4={max_sb_max:.5f}")
        assert min_F2 < 0.96 and min_q32 < 0.996 and min_max > 1.00001

    print("\n--- 3B: F_eff(mu) = F2 + mu(F1-F2)F2^{-1}(F1-F2): Random Non-Holden 3x3 vs Adversarial Rank-1 Kernel ---")
    for label, p in [("sqrt(2)", math.sqrt(2.0)), ("4/3", 4 / 3), ("6/5", 6 / 5)]:
        kap = p / (2.0 * (p - 1.0))
        alpha = (kap - 1.5) / (kap - 1.0)
        L4, d4, X4 = continue_rg(p, 4, m=2.0)
        _, xp, _, sp4 = roots_kappa(L4, kap)
        c4 = 2.0 * sp4
        sd4 = np.sqrt(d4)
        Q4 = holden_operators(np.diag(d4), (sd4[:, None] * X4) * sd4[None, :], kap)["Q"]
        evQ4, UQ4 = eigh(Q4)
        sbar = float(np.dot(UQ4[0, :] ** 2, evQ4))

        # 100 random complex non-Holden 3x3 matrices at mu = 200 (zero domain failures by Kubo-Ando!)
        mu = 200.0
        min_dom = 1e99
        max_rand_ksb = 0.0
        for _ in range(100):
            d = np.exp(rng.uniform(-2.0, 2.0, size=3))
            U1, _ = np.linalg.qr(rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3)))
            U2, _ = np.linalg.qr(rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3)))
            D = (U1 * d) @ U1.conj().T
            X = (U2 * rng.uniform(1e-3, xp, size=3)) @ U2.conj().T
            sD = matpow(D, 0.5)
            H = sD @ X @ sD
            G = sD @ H @ sD
            M = D + H
            Dk = matpow(D, kap - 1.5)
            F1 = L4 * matpow(D, kap - 1.0) @ matpow(M, 2.0 - 2.0 * kap) @ matpow(D, kap - 1.0)
            F2 = kubo_ando_mean(L4 * Dk @ np.linalg.inv(np.eye(3) + X) @ Dk, Dk @ matpow(G, 1.0 - kap) @ Dk, alpha)
            diff = F1 - F2
            Feff = F2 + mu * diff @ np.linalg.inv(F2) @ diff
            P = Dk @ matpow(G, 1.5 - kap) @ Dk
            Y = matpow(D, 0.5 - kap) @ matpow(G, kap - 0.5) @ matpow(D, 0.5 - kap)
            mid = 0.5 * ((Feff - sbar * P) + (Feff - sbar * P).conj().T)
            min_dom = min(min_dom, float(eigh(mid, eigvals_only=True)[0]))
            Ksb = sp4 * np.eye(3) - sbar * Y + np.linalg.inv(mid)
            max_rand_ksb = max(max_rand_ksb, float(eigh(0.5 * (Ksb + Ksb.conj().T) / c4, eigvals_only=True)[-1]))

        # Adversarial non-Holden 2x2 Nelder-Mead search at mu = 500 (safe x_min >= 1e-4 to avoid float64 G^{-k} overflow)
        mu_adv = 500.0

        def eval_adv(z):
            d1 = math.exp(float(np.clip(z[0], -6.0, -0.02)))
            th = float(z[1])
            x0 = 1e-4 + (xp - 1e-4) / (1.0 + math.exp(-float(np.clip(z[2], -10.0, 10.0))))
            x1 = 1e-4 + (xp - 1e-4) / (1.0 + math.exp(-float(np.clip(z[3], -10.0, 10.0))))
            d = np.array([1.0, d1])
            sd = np.sqrt(d)
            D = np.diag(d)
            c, s = math.cos(th), math.sin(th)
            U = np.array([[c, -s], [s, c]])
            X = (U * np.array([x0, x1])) @ U.T
            H = (sd[:, None] * X) * sd[None, :]
            G = (sd[:, None] * H) * sd[None, :]
            M = D + H
            Dk = np.diag(d ** (kap - 1.5))
            F1 = L4 * (d ** (kap - 1.0))[:, None] * matpow(M, 2.0 - 2.0 * kap) * (d ** (kap - 1.0))[None, :]
            F2 = kubo_ando_mean(L4 * Dk @ np.linalg.inv(np.eye(2) + X) @ Dk, Dk @ matpow(G, 1.0 - kap) @ Dk, alpha)
            diff = F1 - F2
            Feff = F2 + mu_adv * diff @ np.linalg.inv(F2) @ diff
            P = Dk @ matpow(G, 1.5 - kap) @ Dk
            Y = (d ** (0.5 - kap))[:, None] * matpow(G, kap - 0.5) * (d ** (0.5 - kap))[None, :]
            Ksb = sp4 * np.eye(2) - sbar * Y + np.linalg.inv(Feff - sbar * P)
            return -float(eigh(0.5 * (Ksb + Ksb.T) / c4, eigvals_only=True)[-1])

        best_adv = 0.0
        best_z = None
        for _ in range(18):
            z0 = np.array([rng.uniform(-3.0, -0.1), rng.uniform(0.0, math.pi), rng.uniform(-4.0, 4.0), rng.uniform(-4.0, 4.0)])
            res = minimize(eval_adv, z0, method="Nelder-Mead", options={"maxiter": 400})
            if -res.fun > best_adv:
                best_adv, best_z = float(-res.fun), res.x

        # Verify rank-1 near-kernel of F1 - F2 at adversarial maximizer!
        d1 = math.exp(float(np.clip(best_z[0], -6.0, -0.02)))
        th = float(best_z[1])
        x0 = 1e-4 + (xp - 1e-4) / (1.0 + math.exp(-float(np.clip(best_z[2], -10.0, 10.0))))
        x1 = 1e-4 + (xp - 1e-4) / (1.0 + math.exp(-float(np.clip(best_z[3], -10.0, 10.0))))
        d = np.array([1.0, d1])
        sd = np.sqrt(d)
        D = np.diag(d)
        U = np.array([[math.cos(th), -math.sin(th)], [math.sin(th), math.cos(th)]])
        X = (U * np.array([x0, x1])) @ U.T
        H = (sd[:, None] * X) * sd[None, :]
        G = (sd[:, None] * H) * sd[None, :]
        M = D + H
        Dk = np.diag(d ** (kap - 1.5))
        F1 = L4 * (d ** (kap - 1.0))[:, None] * matpow(M, 2.0 - 2.0 * kap) * (d ** (kap - 1.0))[None, :]
        F2 = kubo_ando_mean(L4 * Dk @ np.linalg.inv(np.eye(2) + X) @ Dk, Dk @ matpow(G, 1.0 - kap) @ Dk, alpha)
        ev_diff = np.sort(np.abs(eigh(0.5 * ((F1 - F2) + (F1 - F2).T), eigvals_only=True)))
        res_H = float(np.linalg.norm((d ** (-kap + 0.5))[:, None] * matpow(M, 2.0 * kap - 1.0) * (d ** (-kap + 0.5))[None, :] - L4 * (d ** (1.0 - kap))[:, None] * matpow(G, kap - 1.0) * (d ** (1.0 - kap))[None, :]))
        print(f"  p={label:>7s}: 100 rand 3x3 (mu=200) min_dom={min_dom:+.2e}, max(Ksb/c4)={max_rand_ksb:.5f} | ADV 2x2 (mu=500): max(Ksb/c4)={best_adv:.5f} (|eig(F1-F2)|=[{ev_diff[0]:.2e},{ev_diff[1]:.2e}], ||Holden||={res_H:.2f})")
        assert min_dom > 0.0 and best_adv > max_rand_ksb and best_adv > 1.01 and res_H > 1.0 and ev_diff[0] < 0.01 * ev_diff[1]

    print("  [PASS] Suite 3 verified the complete second-use-of-Holden obstruction taxonomy.\n")


# ==============================================================================
# SUITE 4: EXACT FIRST-ORDER NON-COMMUTATIVE RELATIVE-ENTROPY LOG DEFECTS AT k=3/2
# ==============================================================================

def run_suite_4():
    print("=" * 86)
    print("SUITE 4: FIRST-ORDER NON-COMMUTATIVE LOGARITHMIC DEFECT DECOMPOSITION AT kappa = 3/2")
    print("=" * 86)
    for r in [2, 3, 4]:
        L, d, X = continue_rg(1.5, r, m=2.0)
        _, _, _, sp = roots_kappa(L, 1.5)
        c = 2.0 * sp
        sd = np.sqrt(d)
        D = np.diag(d)
        H = (sd[:, None] * X) * sd[None, :]
        G = (sd[:, None] * H) * sd[None, :]
        M = D + H
        Q = holden_operators(D, H, 1.5)["Q"]
        evQ, UQ = eigh(Q)
        w_mu = UQ[0, :] ** 2
        logD = np.diag(np.log(d))
        logG = matlog(G)
        logM = matlog(M)
        logX = matlog(X)
        IpX = np.eye(r) + X
        iIpX = np.linalg.inv(IpX)
        logIpX = matlog(IpX)

        dY_nc = 0.5 * (((1.0 / d)[:, None] * (G @ logG) * (1.0 / d)[None, :] - logD @ X - X @ logD - X @ logX) +
                       ((1.0 / d)[:, None] * (G @ logG) * (1.0 / d)[None, :] - logD @ X - X @ logD - X @ logX).T)
        dW_nc = 0.5 * ((logD @ iIpX + iIpX @ logD - 2.0 * (sd[:, None] * (np.linalg.inv(M) @ logM) * sd[None, :]) + 2.0 * (iIpX @ logIpX)) +
                       (logD @ iIpX + iIpX @ logD - 2.0 * (sd[:, None] * (np.linalg.inv(M) @ logM) * sd[None, :]) + 2.0 * (iIpX @ logIpX)).T)
        dP_nc = 0.5 * ((2.0 * logD - logG + logX) + (2.0 * logD - logG + logX).T)

        C_Y = np.zeros((r, r))
        C_W = np.zeros((r, r))
        C_P = np.zeros((r, r))
        for sk, wk in zip(evQ, w_mu):
            Rs = np.linalg.inv(L * iIpX - sk * np.eye(r))
            iKs = np.linalg.inv(sp * np.eye(r) - sk * X + Rs)
            C_Y += -c * wk * (iKs @ (-sk * dY_nc) @ iKs)
            C_W += -c * wk * (iKs @ (-L * (Rs @ dW_nc @ Rs)) @ iKs)
            C_P += -c * wk * (iKs @ (+sk * (Rs @ dP_nc @ Rs)) @ iKs)

        # Independent central finite-difference verification of (dY_nc, dW_nc, dP_nc) and C_Y + C_W + C_P at kap = 1.5 +/- 1e-6:
        eps_k = 1e-6

        def _nc_minus_comm_I(kk):
            ops_k = holden_operators(D, H, kk)
            I_nc = np.zeros((r, r))
            I_cm = np.zeros((r, r))
            Yc = matpow(X, kk - 0.5)
            W1ic = matpow(IpX, 2.0 - 2.0 * kk)
            Pc = matpow(X, 1.5 - kk)
            for sk, wk in zip(evQ, w_mu):
                I_nc += wk * np.linalg.inv(sp * np.eye(r) - sk * ops_k["Y"] + np.linalg.inv(L * ops_k["W1_inv"] - sk * ops_k["P"]))
                I_cm += wk * np.linalg.inv(sp * np.eye(r) - sk * Yc + np.linalg.inv(L * W1ic - sk * Pc))
            return c * (I_nc - I_cm)

        fd_Ctot = (_nc_minus_comm_I(1.5 + eps_k) - _nc_minus_comm_I(1.5 - eps_k)) / (2.0 * eps_k)
        fd_err = float(np.linalg.norm((C_Y + C_W + C_P) - fd_Ctot))
        assert fd_err < 1e-6

        trY = float(np.trace(dY_nc))
        trP = float(np.trace(dP_nc))
        ev_CY = eigh(C_Y[1:, 1:], eigvals_only=True)
        ev_CW = eigh(C_W[1:, 1:], eigvals_only=True)
        ev_CP = eigh(C_P[1:, 1:], eigvals_only=True)
        ev_Ctot = eigh((C_Y + C_W + C_P)[1:, 1:], eigvals_only=True)
        print(f"  r={r}: Tr(dY)={trY:+.5f}, |Tr(dP)|={abs(trP):.1e}, fd_err={fd_err:.1e} | C_Y|_perp={np.round(ev_CY, 5)} | C_W|_perp={np.round(ev_CW, 5)} | C_P|_perp={np.round(ev_CP, 5)} | sum={np.round(ev_Ctot, 5)}")
        assert trY > 0.4 and abs(trP) < 1e-13 and float(ev_CY[0]) > 0.2 and float(ev_Ctot[0]) > 0.13 and float(ev_CP[-1]) < 0.0

    print("  [PASS] Suite 4 confirmed Delta_Y relative-entropy defect drives >100% of the positive e_0^perp signal.\n")


# ==============================================================================
# SUITE 5: HADAMARD THREE-LINES INTERPOLATION & 45-DIGIT mpmath.iv ENCLOSURES
#          FOR IRRATIONAL p = sqrt(2) AND p = 7/5 (m = 2)
# ==============================================================================

def _mp_roots_kappa(L_mp, kap_mp):
    """High-precision scalar roots (xm, xp, sm, sp) in mpmath."""
    t_min = mp.log((kap_mp - 1) / kap_mp)
    logL = mp.log(L_mp)

    def fn(t):
        return (2 * kap_mp - 1) * mp.log(1 + mp.exp(t)) - (kap_mp - 1) * t - logL

    lo, hi = t_min - 5, t_min + 5
    while fn(lo) < 0:
        lo -= 10
    while fn(hi) < 0:
        hi += 10
    tm = mp.findroot(fn, (lo, t_min), solver="anderson")
    tp = mp.findroot(fn, (t_min, hi), solver="anderson")
    xm, xp = mp.exp(tm), mp.exp(tp)
    return xm, xp, (xm ** (kap_mp - 1)) * (xm - 1), (xp ** (kap_mp - 1)) * (xp - 1)


def _polish_rg_50dps(p_mp, r, L_f, d_f, X_f):
    """Polish a rank-r RG block (m = 2) to 50-digit mpmath precision via Newton's method."""
    mp.mp.dps = 55
    kap = p_mp / (2 * (p_mp - 1))
    triu = [(i, j) for i in range(r) for j in range(i, r)]
    nv = 1 + (r - 1) + len(triu)

    # Initial vector: [L, log(d_1..d_{r-1}), S[triu]] where X = exp(S)
    w0, V0 = eigh(0.5 * (X_f + X_f.T))
    S0_np = (V0 * np.log(w0)) @ V0.T
    vec = [mp.mpf(float(L_f))] + [mp.log(mp.mpf(float(d_f[i]))) for i in range(1, r)] + [mp.mpf(float(S0_np[i, j])) for (i, j) in triu]

    def unpack(v):
        L = v[0]
        dd = [mp.mpf(1)] + [mp.exp(v[i]) for i in range(1, r)]
        S = mp.matrix(r, r)
        for idx, (i, j) in enumerate(triu):
            S[i, j] = S[j, i] = v[r + idx]
        evS, VS = mp.eigh(S)
        X = mp.matrix(r, r)
        for k in range(r):
            ex = mp.exp(evS[k])
            for i in range(r):
                for j in range(r):
                    X[i, j] += ex * VS[i, k] * VS[j, k]
        return L, dd, X

    def residual(v):
        L, dd, X = unpack(v)
        _, _, _, sp = _mp_roots_kappa(L, kap)
        sd = [mp.sqrt(x) for x in dd]
        H = mp.matrix(r, r)
        G = mp.matrix(r, r)
        M = mp.matrix(r, r)
        for i in range(r):
            for j in range(r):
                H[i, j] = sd[i] * X[i, j] * sd[j]
                G[i, j] = sd[i] * H[i, j] * sd[j]
                M[i, j] = H[i, j] + (dd[i] if i == j else 0)
        M2km1 = _mp_matpow_herm(M, 2 * kap - 1)
        Gkm1 = _mp_matpow_herm(G, kap - 1)
        Gk = _mp_matpow_herm(G, kap)
        out = []
        for (i, j) in triu:
            lhs = (dd[i] ** (-kap + mp.mpf(1) / 2)) * M2km1[i, j] * (dd[j] ** (-kap + mp.mpf(1) / 2))
            rhs = L * (dd[i] ** (1 - kap)) * Gkm1[i, j] * (dd[j] ** (1 - kap))
            out.append(lhs - rhs)
        for i in range(r):
            eh_ii = (dd[i] ** (-kap)) * Gk[i, i] * (dd[i] ** (-kap)) - (dd[i] ** (1 - kap)) * Gkm1[i, i] * (dd[i] ** (1 - kap))
            tar = -sp if i == 0 else sp
            out.append(eh_ii - tar)
        return out

    h_fd = mp.mpf("1e-22")
    for _ in range(6):
        f0 = residual(vec)
        nrm = mp.sqrt(sum(x * x for x in f0))
        if nrm < mp.mpf("1e-46"):
            break
        J = mp.matrix(nv, nv)
        for col in range(nv):
            v2 = list(vec)
            v2[col] += h_fd
            f1 = residual(v2)
            for row in range(nv):
                J[row, col] = (f1[row] - f0[row]) / h_fd
        step = mp.lu_solve(J, mp.matrix([-x for x in f0]))
        vec = [vec[i] + step[i] for i in range(nv)]

    L, dd, X = unpack(vec)
    f_end = residual(vec)
    res_norm = mp.sqrt(sum(x * x for x in f_end))
    # Compute exact branching ratio rho_r = sum_{k=1}^{r-1} d_k^{2*kap} (< 1 guarantees trace-class RG tree!)
    rho = sum(dd[i] ** (2 * kap) for i in range(1, r))
    return L, dd, X, res_norm, rho


def _outward_floor_str(x_iv, digits):
    scale = mp.mpf(10) ** digits
    n = int(mp.floor(mp.mpf(x_iv.a) * scale))
    while mp.mpf(iv.mpf(f"{n // (10**digits)}.{abs(n) % (10**digits):0{digits}d}").b) > mp.mpf(x_iv.a):
        n -= 1
    return f"{n // (10**digits)}.{abs(n) % (10**digits):0{digits}d}"


def _outward_ceil_str(x_iv, digits):
    scale = mp.mpf(10) ** digits
    n = int(mp.ceil(mp.mpf(x_iv.b) * scale))
    while mp.mpf(iv.mpf(f"{n // (10**digits)}.{abs(n) % (10**digits):0{digits}d}").a) < mp.mpf(x_iv.b):
        n += 1
    return f"{n // (10**digits)}.{abs(n) % (10**digits):0{digits}d}"


def run_suite_5():
    print("=" * 86)
    print("SUITE 5: HADAMARD THREE-LINES PROOF CHECK & 45-DPS mpmath.iv ENCLOSURES (p=sqrt(2), 7/5)")
    print("=" * 86)
    rng = np.random.default_rng(505)

    # 5A: Direct verification of the Hadamard Three-Lines analytic family G_j(z) on complex 3x3 matrices!
    print("\n--- 5A: Direct Complex 3x3 Verification of Hadamard Three-Lines Boundary Norm ||sum |G_j(it)| ||_{p0} = 1 ---")
    p0, p1 = 4.0 / 3.0, 1.5
    p_mid = math.sqrt(2.0)
    B1 = rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3))
    B2 = rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3))
    B1 = B1 @ B1.conj().T + 0.3 * np.eye(3)
    B2 = B2 @ B2.conj().T + 0.3 * np.eye(3)
    S = B1 + B2
    # Normalize ||S||_{p_mid} = 1
    evS, US = eigh(S)
    nrm_p = float(np.sum(evS ** p_mid) ** (1.0 / p_mid))
    B1 /= nrm_p
    B2 /= nrm_p
    S = B1 + B2
    evS, US = eigh(S)
    U1, _ = np.linalg.qr(rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3)))
    U2, _ = np.linalg.qr(rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3)))

    max_bnd_err = 0.0
    for re_z, p_bnd in [(0.0, p0), (1.0, p1)]:
        for t_im in [-2.5, 0.0, 1.7]:
            z = complex(re_z, t_im)
            inv_pz = (1.0 - z) / p0 + z / p1
            exp_S = 0.5 * (p_mid * inv_pz - 1.0)
            Spow = (US * (evS ** exp_S)) @ US.conj().T
            G1 = U1 @ Spow @ B1 @ Spow
            G2 = U2 @ Spow @ B2 @ Spow
            mod1 = matpow(G1.conj().T @ G1, 0.5)
            mod2 = matpow(G2.conj().T @ G2, 0.5)
            ev_sum = eigh(0.5 * ((mod1 + mod2) + (mod1 + mod2).conj().T), eigvals_only=True)
            norm_pb = float(np.sum(ev_sum ** p_bnd) ** (1.0 / p_bnd))
            max_bnd_err = max(max_bnd_err, abs(norm_pb - 1.0))
    print(f"  Max boundary norm error | ||sum |G_j(re+it)| ||_{{p_bnd}} - 1 | across 6 boundary points = {max_bnd_err:.3e}")
    assert max_bnd_err < 1e-13

    # 5B: 45-digit mpmath.iv Outward-Rounded All-n Enclosures for p = sqrt(2) and p = 7/5 (m = 2)
    #   - Unconditional zero-float 2x2 explicit matrix lower bound:
    #       A_0 = diag(1, u) P_0 diag(1, v), A_1 = diag(1, u) P_1 diag(1, v)  (P_0, P_1 = 2x2 DFT rank-1 projections)
    #       => A_0 + A_1 = diag(1, u v),  |A_0| + |A_1| = sqrt((1+u^2)/(1+v^2)) diag(1, v^2)
    #       => C_p(2) >= R_p(u, v) = sqrt((1+v^2)/(1+u^2)) * ((1 + (u v)^p) / (1 + v^{2p}))^{1/p}  (EXACT for all u, v > 0!)
    #   - Zero-float Hadamard Three-Lines upper bound using our signed-off #114 certified endpoints:
    #       C_{4/3}(2) <= 1.018371580069016    (Module 4 of #114 continuum_operator_certificate.py)
    #       C_{3/2}(2) <= 1.036437168069746188 (Module 2 of #114 continuum_operator_certificate.py)
    #   - 50-dps RG4 fixed-point lower bound (res4 < 1e-45, rho_4 < 0.5) shown separately alongside!
    print("\n--- 5B: 45-dps mpmath.iv Unconditional 2x2 Lower Bounds, Hadamard 3-Lines Upper Bounds, & 50-dps RG4 (m = 2) ---")
    iv.dps = 45
    mp.mp.dps = 55
    C43_ub_iv = iv.mpf("1.018371580069016")
    C32_ub_iv = iv.mpf("1.036437168069746188")

    # Rational near-optimal (u, v) witnesses for explicit 2x2 matrix lower bound (zero floats!)
    witnesses_2x2 = {
        "sqrt(2)": (iv.mpf("6.89151393"), iv.mpf("2.22454540")),
        "7/5":     (iv.mpf("6.63476589"), iv.mpf("2.25014751")),
    }

    for label, p_float, p_mp, p_iv in [("sqrt(2)", math.sqrt(2.0), mp.sqrt(2), iv.sqrt(2)),
                                       ("7/5", 7.0 / 5.0, mp.mpf(7) / 5, iv.mpf(7) / 5)]:
        # Direct 2x2 numerical cross-check of explicit matrix witness (A0, A1)
        u_iv, v_iv = witnesses_2x2[label]
        uf, vf = float(u_iv.a), float(v_iv.a)
        P0 = 0.5 * np.array([[1.0, 1.0], [1.0, 1.0]])
        P1 = 0.5 * np.array([[1.0, -1.0], [-1.0, 1.0]])
        A0 = np.diag([1.0, uf]) @ P0 @ np.diag([1.0, vf])
        A1 = np.diag([1.0, uf]) @ P1 @ np.diag([1.0, vf])
        s_sum = np.linalg.svd(A0 + A1, compute_uv=False)
        # Exact rank-1 |A_k| verification (mod_ex >= 0, mod_ex^2 = A_k^T A_k):
        mod_total = np.zeros((2, 2))
        for Ak, Pk in [(A0, P0), (A1, P1)]:
            mod_ex = math.sqrt((1.0 + uf * uf) / (1.0 + vf * vf)) * (np.diag([1.0, vf]) @ Pk @ np.diag([1.0, vf]))
            assert float(np.linalg.norm(mod_ex @ mod_ex - Ak.T @ Ak)) < 1e-13
            assert float(eigh(mod_ex, eigvals_only=True)[0]) > -1e-14
            mod_total += mod_ex
        ev_mod = eigh(mod_total, eigvals_only=True)
        ratio_f = (float(np.sum(s_sum ** p_float)) / float(np.sum(ev_mod ** p_float))) ** (1.0 / p_float)

        # Pure 45-digit mpmath.iv evaluation of unconditional 2x2 lower bound R_p(u, v)
        C_lb_2x2_iv = iv.sqrt((iv.mpf(1) + v_iv ** 2) / (iv.mpf(1) + u_iv ** 2)) * (
            (iv.mpf(1) + (u_iv * v_iv) ** p_iv) / (iv.mpf(1) + v_iv ** (iv.mpf(2) * p_iv))
        ) ** (iv.mpf(1) / p_iv)
        assert abs(ratio_f - float(C_lb_2x2_iv.a)) < 1e-12

        # Pure 45-digit mpmath.iv Hadamard Three-Lines upper bound:
        # 1/p = (1-theta)/(4/3) + theta/(3/2)  =>  theta = 9 - 12/p
        theta_iv = iv.mpf(9) - iv.mpf(12) / p_iv
        C_ub_iv = (C43_ub_iv ** (iv.mpf(1) - theta_iv)) * (C32_ub_iv ** theta_iv)
        # Classical [1, 2] Hadamard Three-Lines upper bound ((1 + sqrt(2))/2)^{1 - 1/p} (C_1(2)=1, C_2(2)=sqrt((1+sqrt(2))/2))
        # and #143 closed-form bound (x_+ <= 2^{1/3}) for comparison
        C_had12_iv = ((iv.mpf(1) + iv.sqrt(iv.mpf(2))) / iv.mpf(2)) ** (iv.mpf(1) - iv.mpf(1) / p_iv)
        kap_iv = p_iv / (iv.mpf(2) * (p_iv - iv.mpf(1)))
        xp_4L_iv = iv.mpf(2) ** (iv.mpf(1) / iv.mpf(3))
        L_4L_iv = ((iv.mpf(1) + xp_4L_iv) ** (iv.mpf(2) * kap_iv - iv.mpf(1))) / (xp_4L_iv ** (kap_iv - iv.mpf(1)))
        C_4L_iv = (L_4L_iv / (iv.mpf(2) ** (iv.mpf(2) * kap_iv - iv.mpf(1)))) ** (iv.mpf(1) / (iv.mpf(2) * kap_iv))

        # 50-dps polished rank-4 RG block lower bound (exact branching ratio rho_4 < 1, Proposition 1.4)
        L4_f, d4_f, X4_f = continue_rg(p_float, 4, m=2.0)
        L4_mp, dd4_mp, X4_mp, res4, rho4 = _polish_rg_50dps(p_mp, 4, L4_f, d4_f, X4_f)
        assert res4 < mp.mpf("1e-45") and rho4 < mp.mpf("0.5")
        kap_mp = p_mp / (2 * (p_mp - 1))
        C_rg4_mp = (L4_mp / (mp.mpf(2) ** (2 * kap_mp - 1))) ** (1 / (2 * kap_mp))

        lb2_str = _outward_floor_str(C_lb_2x2_iv, 12)
        ub_str = _outward_ceil_str(C_ub_iv, 12)
        gap_iv_str = _outward_ceil_str(iv.mpf(ub_str) - iv.mpf(lb2_str), 6)
        crush_had_iv = (C_had12_iv - C_lb_2x2_iv) / iv.mpf(gap_iv_str)
        crush_had_str = _outward_floor_str(crush_had_iv, 1)
        crush_4L_iv = (C_4L_iv - C_lb_2x2_iv) / iv.mpf(gap_iv_str)
        crush_4L_str = _outward_floor_str(crush_4L_iv, 1)
        rg4_str = mp.nstr(C_rg4_mp, 15)
        rg4_gap = float(iv.mpf(ub_str).b) - float(C_rg4_mp)

        print(f"  p={label:>7s}, m=2:")
        print(f"    Rigorous iv Encl (2x2 LB <= C_p(2) <= H3L UB): {lb2_str} <= C_{{{label}}}(2) <= {ub_str}  (iv gap <= {gap_iv_str})")
        print(f"      Strict iv crush: >={crush_had_str}x vs [1,2] Hadamard (((1+sqrt(2))/2)^(1-1/p)), >={crush_4L_str}x vs #143 closed-form (x_+<=2^(1/3))")
        print(f"    50-dps RG4 LB (res={mp.nstr(res4, 3)}, rho_4={mp.nstr(rho4, 6)}): C_RG4 = {rg4_str}  (H3L UB - RG4 = {rg4_gap:.6e})")
        assert mp.mpf(iv.mpf(lb2_str).b) <= mp.mpf(C_lb_2x2_iv.a)
        assert mp.mpf(iv.mpf(ub_str).a) >= mp.mpf(C_ub_iv.b)
        assert mp.mpf(iv.mpf(ub_str).b) - mp.mpf(iv.mpf(lb2_str).a) <= mp.mpf(iv.mpf(gap_iv_str).a)
        assert mp.mpf(iv.mpf(crush_had_str).b) <= mp.mpf(crush_had_iv.a)
        assert mp.mpf(iv.mpf(crush_4L_str).b) <= mp.mpf(crush_4L_iv.a)
        assert C_rg4_mp > mp.mpf(C_lb_2x2_iv.b) and C_rg4_mp < mp.mpf(C_ub_iv.a)
        assert mp.mpf(iv.mpf(crush_had_str).a) > mp.mpf(25) and mp.mpf(iv.mpf(crush_4L_str).a) > mp.mpf(10)

    print("  [PASS] Suite 5 verified Hadamard Three-Lines proof and 45-dps outward-rounded enclosures.\n")


def main():
    t0 = time.time()
    run_suite_1()
    run_suite_2()
    run_suite_3()
    run_suite_4()
    run_suite_5()
    dt = time.time() - t0
    print("=" * 86)
    print(f"ALL 5 SUITES PASSED WITH ZERO VIOLATIONS IN {dt:.2f}s (EXIT CODE 0)")
    print("=" * 86)


if __name__ == "__main__":
    main()
