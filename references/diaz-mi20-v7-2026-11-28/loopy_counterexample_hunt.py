"""
OPTION-B COUNTEREXAMPLE HUNT & EXACT LOOP-CLOSURE PERTURBATION DIAGNOSTIC
FOR OPEN PROBLEM MI-20 (SUBQUADRATIC LEE CONSTANTS C_p(m), 1 < p < 2, m >= 2).

Self-contained, zero local imports (uses only numpy, scipy, mpmath).
Reproduces every benchmark, graph/Cayley/ring/dense/PSD-POVM/Holden search,
D-eigenbasis anatomy check, full non-gauge real+complex Hessian spectrum,
and 50-digit mpmath loop-closure derivative & candidate verification reported
in loopy_hunt_report.md.
"""

import time
import numpy as np
import mpmath as mp
from scipy.optimize import minimize, least_squares, brentq

P_LIST = [
    ("6/5", (6, 5), 6.0 / 5.0, 3.0),
    ("5/4", (5, 4), 5.0 / 4.0, 2.5),
    ("4/3", (4, 3), 4.0 / 3.0, 2.0),   # Exact proved control (Thm 14)
    ("3/2", (3, 2), 3.0 / 2.0, 1.5),
    ("5/3", (5, 3), 5.0 / 3.0, 1.25),
]


# =============================================================================
# PART 0: EXACT BENCHMARKS C_{1x1}(p,m) & HIGH-RANK C_{RG}(p,m; r)
# =============================================================================

def roots_kappa(Lam, kappa):
    t_min = np.log((kappa - 1.0) / kappa)
    logL = np.log(Lam)

    def g(t):
        return (2.0 * kappa - 1.0) * np.logaddexp(0.0, t) - (kappa - 1.0) * t - logL

    if g(t_min) >= 0:
        return None
    lo = t_min - 1.0
    while g(lo) < 0:
        lo -= 10.0
    hi = t_min + 1.0
    while g(hi) < 0:
        hi += 10.0
    xm = np.exp(brentq(g, lo, t_min, xtol=1e-15, rtol=1e-15))
    xp = np.exp(brentq(g, t_min, hi, xtol=1e-15, rtol=1e-15))
    sigp = (xp ** (kappa - 1.0)) * (xp - 1.0)
    sigm = (xm ** (kappa - 1.0)) * (xm - 1.0)
    return xm, xp, sigp, sigm


def scalar_1x1(kappa, m):
    Lam0 = 2.0 ** (2.0 * kappa - 1.0)

    def eq(Lam):
        _, _, sigp, sigm = roots_kappa(Lam, kappa)
        return sigp + (m - 1.0) * sigm

    lo = Lam0 * (1.0 + 1e-13)
    hi = max(Lam0 * 2.0, 2.0 * np.sqrt(m))
    while eq(hi) < 0:
        hi *= 2.0
    Lam = brentq(eq, lo, hi, xtol=1e-15, rtol=1e-15)
    C = (Lam / Lam0) ** (1.0 / (2.0 * kappa))
    return Lam, C


def herm_pow(M, power, tol=1e-22):
    M = 0.5 * (M + M.conj().T)
    ev, V = np.linalg.eigh(M)
    if ev[0] <= tol * max(ev[-1], 1.0):
        return None
    return (V * (ev ** power)) @ V.conj().T


def solve_rg_cascade(kappa, m, r_max=7):
    Lam1, C1 = scalar_1x1(kappa, m)
    xm1, xp1, _, _ = roots_kappa(Lam1, kappa)
    sols = {1: (Lam1, C1, np.array([1.0]), np.array([[xm1]]), 0.0)}

    def solve_r(r, Lam0, d0, X0):
        triu = np.triu_indices(r)

        def unpack(x):
            Lam = x[0]
            d = np.concatenate([[1.0], np.exp(np.clip(x[1:r], -45.0, 2.0))])
            X = np.zeros((r, r))
            X[triu] = x[r:]
            X = X + X.T - np.diag(np.diag(X))
            return Lam, d, X

        def residuals(x):
            Lam, d, X = unpack(x)
            rt = roots_kappa(Lam, kappa)
            if rt is None:
                return np.full(r * (r + 1), 1e3)
            _, _, sigp, _ = rt
            sd = np.sqrt(d)
            D = np.diag(d)
            H = (sd[:, None] * X) * sd[None, :]
            G = (sd[:, None] * H) * sd[None, :]
            Mp = herm_pow(D + H, 2.0 * kappa - 1.0, tol=1e-22)
            Gkm1 = herm_pow(G, kappa - 1.0, tol=1e-22)
            Gk = herm_pow(G, kappa, tol=1e-22)
            if Mp is None or Gkm1 is None or Gk is None:
                return np.full(r * (r + 1), 1e3)
            R1 = Mp - Lam * ((sd[:, None] * Gkm1) * sd[None, :])
            tgt = sigp * (d ** (2.0 * kappa))
            tgt[0] = -sigp / (m - 1.0)
            R2 = Gk - (d[:, None] * Gkm1) * d[None, :] - np.diag(tgt)
            w1 = 1.0 / np.outer(d ** (kappa - 0.5), d ** (kappa - 0.5))
            w2 = 1.0 / np.outer(d ** kappa, d ** kappa)
            return np.concatenate([(R1 * w1)[triu], (R2 * w2)[triu]])

        sol = least_squares(
            residuals,
            np.concatenate([[Lam0], np.log(d0[1:]), X0[triu]]),
            xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=4000
        )
        Lam, d, X = unpack(sol.x)
        C = (Lam / (2.0 ** (2.0 * kappa - 1.0))) ** (1.0 / (2.0 * kappa))
        return Lam, C, d, X, float(np.linalg.norm(sol.fun))

    best_r2 = None
    for d_try in [1e-5, 1e-4, 1e-3, 1e-2, 0.06, 0.2, 0.4]:
        for bf in [-0.2, -0.45]:
            b = bf * np.sqrt(xm1 * xp1)
            Lam2, C2, d2, X2, err2 = solve_r(
                2, Lam1 * (1.0 + 1e-6), np.array([1.0, d_try]),
                np.array([[xm1, b], [b, 0.45 * xp1]])
            )
            if err2 < 1e-10 and abs(X2[0, 1]) > 1e-7 and C2 > C1 + 1e-15:
                if best_r2 is None or C2 > best_r2[1]:
                    best_r2 = (Lam2, C2, d2, X2, err2)
    assert best_r2 is not None, f"r=2 RG solve failed for kappa={kappa}, m={m}"
    Lam_p, C_p, d_p, X_p, err_p = best_r2
    sols[2] = best_r2

    for r in range(3, r_max + 1):
        ratio = d_p[-1] / d_p[-2] if r > 3 else min(0.8, max(0.05, d_p[-1] * 1.4))
        best_c = None
        for r_try in [ratio, 0.55, 0.3, 0.15, 0.05]:
            for diag_f in [1.0, 1.5, 2.2]:
                d0 = np.concatenate([d_p, [d_p[-1] * min(0.85, max(0.005, r_try))]])
                X0 = np.zeros((r, r))
                X0[:r - 1, :r - 1] = X_p
                X0[r - 1, r - 1] = X_p[r - 2, r - 2] * diag_f
                for j in range(1, r - 1):
                    X0[j, r - 1] = X0[r - 1, j] = X_p[j - 1, r - 2] * (0.5 if diag_f > 1.0 else 1.0)
                X0[0, r - 1] = X0[r - 1, 0] = X_p[0, r - 2] * 0.2
                # Ensure X0 is strictly SPD before calling least_squares
                ev0 = np.linalg.eigvalsh(X0)
                if ev0[0] <= 1e-5:
                    X0[r - 1, r - 1] += abs(ev0[0]) + 0.05 * X_p[r - 2, r - 2]
                    if np.linalg.eigvalsh(X0)[0] <= 1e-6:
                        X0[:r - 1, r - 1] *= 0.3; X0[r - 1, :r - 1] *= 0.3
                Lam_c, C_c, d_c, X_c, err_c = solve_r(r, Lam_p, d0, X0)
                rt_c = roots_kappa(Lam_c, kappa)
                if rt_c is None:
                    continue
                _, xp_c, _, _ = rt_c
                if err_c < 1e-8 and np.max(np.linalg.eigvalsh(X_c)) < xp_c - 1e-6 and C_c >= C_p - 1e-15:
                    ds_sorted = np.sort(d_c)
                    if np.min(np.diff(ds_sorted) / np.maximum(ds_sorted[1:], 1e-30)) > 1e-4:
                        best_c = (Lam_c, C_c, d_c, X_c, err_c)
                        break
            if best_c is not None:
                break
        if best_c is None:
            break
        Lam_c, C_c, d_c, X_c, err_c = best_c
        sols[r] = best_c
        Lam_p, C_p, d_p, X_p = Lam_c, C_c, d_c, X_c
    return sols


# =============================================================================
# PART 1: EXACT-GRADIENT REAL & COMPLEX KUBO-ANDO + PSD/POVM ENGINES
# =============================================================================

def ka_eval_and_grad_S_list(S_list, p):
    m = len(S_list)
    N = S_list[0].shape[0]
    is_cplx = any(np.iscomplexobj(S) for S in S_list)
    s = p / (2.0 - p)
    dtype = np.complex128 if is_cplx else np.float64

    eigs, vecs = [], []
    M = np.zeros((N, N), dtype=dtype)
    N_mat = np.zeros_like(M)
    for S in S_list:
        Sh = 0.5 * (S + S.conj().T)
        ev, Q = np.linalg.eigh(Sh)
        if ev[0] <= 1e-26 * max(ev[-1], 1e-30):
            return 1e6, 0.0, [np.zeros_like(M) for _ in range(m)], None
        ev = np.maximum(ev, 1e-30)
        eigs.append(ev); vecs.append(Q)
        M += (Q * (ev ** s)) @ Q.conj().T
        N_mat += Sh
    M = 0.5 * (M + M.conj().T)
    N_mat = 0.5 * (N_mat + N_mat.conj().T)

    ln, qn = np.linalg.eigh(N_mat)
    if ln[0] <= 1e-26 * max(ln[-1], 1e-30):
        return 1e6, 0.0, [np.zeros_like(M) for _ in range(m)], None
    ln = np.maximum(ln, 1e-30)
    N_mhalf = (qn * (ln ** -0.5)) @ qn.conj().T
    N_half = (qn * np.sqrt(ln)) @ qn.conj().T
    C_mat = 0.5 * (N_half @ M @ N_half + (N_half @ M @ N_half).conj().T)
    D_ev, U = np.linalg.eigh(C_mat)
    if D_ev[0] <= 1e-28 * max(D_ev[-1], 1e-30):
        return 1e6, 0.0, [np.zeros_like(M) for _ in range(m)], None
    D_ev = np.maximum(D_ev, 1e-30)
    sqD = np.sqrt(D_ev)

    P = N_mhalf @ U
    P_inv = U.conj().T @ N_half
    K = 0.5 * ((P * sqD) @ P.conj().T + ((P * sqD) @ P.conj().T).conj().T)

    num = 0.0; den = 0.0
    gK = np.zeros_like(M)
    gS_dir_list = []
    for j in range(m):
        ev, Q = eigs[j], vecs[j]
        num += float(np.sum(ev ** s))
        sq_ev = np.sqrt(ev)
        S_half = (Q * sq_ev) @ Q.conj().T
        Y = 0.5 * (S_half @ K @ S_half + (S_half @ K @ S_half).conj().T)
        ly, qy = np.linalg.eigh(Y)
        ly = np.maximum(ly, 1e-30)
        den += float(np.sum(ly ** p))
        G = (qy * (ly ** (p - 1.0))) @ qy.conj().T
        gK += S_half @ G @ S_half

        H_sh = K @ S_half @ G + G @ S_half @ K
        H_hat = Q.conj().T @ H_sh @ Q
        div_sq = 1.0 / (sq_ev[:, None] + sq_ev[None, :])
        gS_dir = Q @ (div_sq * H_hat) @ Q.conj().T
        gS_dir_list.append(0.5 * (gS_dir + gS_dir.conj().T))

    gK = 0.5 * (gK + gK.conj().T)
    val = -(np.log(num) - np.log(den)) / p
    R = float(np.exp(-val))

    PgP = P.conj().T @ gK @ P
    S_adj = PgP / (sqD[:, None] + sqD[None, :])
    W_M = P_inv.conj().T @ S_adj @ P_inv
    W_M = 0.5 * (W_M + W_M.conj().T)
    W_N = -K @ W_M @ K
    W_N = 0.5 * (W_N + W_N.conj().T)

    grad_list = []
    for j in range(m):
        ev, Q = eigs[j], vecs[j]
        WM_hat = Q.conj().T @ W_M @ Q
        fs = ev ** s
        diff_ev = ev[:, None] - ev[None, :]
        diff_fs = fs[:, None] - fs[None, :]
        D_s = np.where(
            np.abs(diff_ev) > 1e-12 * (ev[:, None] + ev[None, :]),
            diff_fs / np.where(np.abs(diff_ev) > 1e-30, diff_ev, 1.0),
            s * (0.5 * (ev[:, None] + ev[None, :])) ** (s - 1.0)
        )
        gS_from_K = 0.5 * (Q @ (D_s * WM_hat) @ Q.conj().T + (Q @ (D_s * WM_hat) @ Q.conj().T).conj().T) + W_N
        S_sm1 = (Q * (ev ** (s - 1.0))) @ Q.conj().T
        gS = -(s / (p * num)) * S_sm1 + (1.0 / den) * (gS_dir_list[j] + gS_from_K)
        grad_list.append(0.5 * (gS + gS.conj().T))

    return float(val), R, grad_list, K


def ka_eval_only(S_list, p):
    val, R, _, K = ka_eval_and_grad_S_list(S_list, p)
    return R, K


def optimize_ka_dense(N, m, p, complex_mode=False, init_S_list=None, rng=None, maxiter=2500):
    if rng is None:
        rng = np.random.default_rng(0)
    blk = N * N * (2 if complex_mode else 1)

    def unpack(x):
        Zs, Ss = [], []
        for j in range(m):
            seg = x[j * blk:(j + 1) * blk]
            Z = (seg[:N * N].reshape(N, N) + 1j * seg[N * N:].reshape(N, N)) if complex_mode else seg.reshape(N, N)
            Zs.append(Z)
            S = Z @ Z.conj().T
            Ss.append(0.5 * (S + S.conj().T))
        return Zs, Ss

    def obj_grad(x):
        Zs, Ss = unpack(x)
        val, _, gSs, _ = ka_eval_and_grad_S_list(Ss, p)
        if val >= 1e5:
            return val, np.zeros_like(x)
        grads = []
        for j in range(m):
            gZ = 2.0 * (gSs[j] @ Zs[j])
            if complex_mode:
                grads.append(np.real(gZ).ravel()); grads.append(np.imag(gZ).ravel())
            else:
                grads.append(gZ.ravel())
        return val, np.concatenate(grads)

    if init_S_list is not None:
        parts = []
        for S in init_S_list:
            ev, Q = np.linalg.eigh(0.5 * (S + S.conj().T))
            ev = np.maximum(ev, 1e-14)
            Z = (Q * np.sqrt(ev)) @ Q.conj().T
            if complex_mode:
                parts.append(np.real(Z).ravel()); parts.append(np.imag(Z).ravel())
            else:
                parts.append(np.real(Z).ravel())
        x0 = np.concatenate(parts)
    else:
        # Multi-scale hierarchical random initialization (adaptive decay so ev^s stays well-conditioned at p=5/3!)
        decay = 0.55 if p > 1.6 else (0.35 if p > 1.4 else 0.25)
        scales = (decay ** np.arange(N))
        parts = []
        for j in range(m):
            Z_re = rng.standard_normal((N, N)) * scales[:, None]
            if complex_mode:
                Z_im = rng.standard_normal((N, N)) * scales[:, None]
                parts.append(Z_re.ravel()); parts.append(Z_im.ravel())
            else:
                parts.append(Z_re.ravel())
        x0 = np.concatenate(parts)

    res = minimize(obj_grad, x0, jac=True, method="L-BFGS-B",
                   options={"maxiter": maxiter, "ftol": 1e-16, "gtol": 1e-14})
    _, Ss = unpack(res.x)
    R, K = ka_eval_only(Ss, p)
    return R, Ss, K, res


def optimize_ka_blocks(N, block_partitions, p, complex_mode=False, init_blocks=None,
                       rng=None, maxiter=3000):
    if rng is None:
        rng = np.random.default_rng(0)
    m = len(block_partitions)
    layout = []
    offset = 0
    for j in range(m):
        for B in block_partitions[j]:
            b = len(B)
            sz = b * b * (2 if complex_mode else 1)
            layout.append((j, np.array(B, dtype=int), b, offset, offset + sz))
            offset += sz
    n_vars = offset

    def unpack(x):
        dtype = np.complex128 if complex_mode else np.float64
        Ss = [np.zeros((N, N), dtype=dtype) for _ in range(m)]
        Zs = []
        for (j, B, b, i0, i1) in layout:
            seg = x[i0:i1]
            Z = (seg[:b * b].reshape(b, b) + 1j * seg[b * b:].reshape(b, b)) if complex_mode else seg.reshape(b, b)
            Zs.append(Z)
            Sb = Z @ Z.conj().T
            Ss[j][np.ix_(B, B)] = 0.5 * (Sb + Sb.conj().T)
        return Zs, Ss

    def obj_grad(x):
        Zs, Ss = unpack(x)
        val, _, gSs, _ = ka_eval_and_grad_S_list(Ss, p)
        if val >= 1e5:
            return val, np.zeros_like(x)
        g = np.zeros(n_vars)
        for idx, (j, B, b, i0, i1) in enumerate(layout):
            gB = gSs[j][np.ix_(B, B)]
            gZ = 2.0 * (gB @ Zs[idx])
            if complex_mode:
                g[i0:i0 + b * b] = np.real(gZ).ravel()
                g[i0 + b * b:i1] = np.imag(gZ).ravel()
            else:
                g[i0:i1] = gZ.ravel()
        return val, g

    if init_blocks is not None:
        x0 = np.zeros(n_vars)
        for idx, (j, B, b, i0, i1) in enumerate(layout):
            Sb = init_blocks[j][np.ix_(B, B)]
            ev, Q = np.linalg.eigh(0.5 * (Sb + Sb.conj().T))
            ev = np.maximum(ev, 1e-14)
            Z = (Q * np.sqrt(ev)) @ Q.conj().T
            if complex_mode:
                x0[i0:i0 + b * b] = np.real(Z).ravel()
                x0[i0 + b * b:i1] = np.imag(Z).ravel()
            else:
                x0[i0:i1] = np.real(Z).ravel()
    else:
        # Multi-scale vertex-weighted random initialization so hierarchical optima are easily found
        vscales = np.exp(-rng.uniform(0.0, 3.5, size=N))
        x0 = np.zeros(n_vars)
        for (j, B, b, i0, i1) in layout:
            sc = vscales[B][:, None]
            Z_re = rng.standard_normal((b, b)) * sc
            if complex_mode:
                Z_im = rng.standard_normal((b, b)) * sc
                x0[i0:i0 + b * b] = Z_re.ravel()
                x0[i0 + b * b:i1] = Z_im.ravel()
            else:
                x0[i0:i1] = Z_re.ravel()

    res = minimize(obj_grad, x0, jac=True, method="L-BFGS-B",
                   options={"maxiter": maxiter, "ftol": 1e-16, "gtol": 1e-14})
    _, Ss = unpack(res.x)
    R, K = ka_eval_only(Ss, p)
    return R, Ss, K, res


def psd_eval_and_grad_multi(x, n, ranks, p, complex_mode=False):
    m = len(ranks)
    alpha = 1.0 - 1.0 / p
    dtype = np.complex128 if complex_mode else np.float64
    Zs, Ws = [], []
    T = np.zeros((n, n), dtype=dtype)
    off = 0
    for r in ranks:
        sz = n * r
        if complex_mode:
            Z = x[off:off + sz].reshape(n, r) + 1j * x[off + sz:off + 2 * sz].reshape(n, r)
            off += 2 * sz
        else:
            Z = x[off:off + sz].reshape(n, r)
            off += sz
        Zs.append(Z)
        W = 0.5 * (Z @ Z.conj().T + (Z @ Z.conj().T).conj().T)
        Ws.append(W); T += W
    T = 0.5 * (T + T.conj().T)

    lamT, qT = np.linalg.eigh(T)
    if lamT[0] <= 1e-20 * max(lamT[-1], 1e-30):
        return 1e6, np.zeros_like(x)
    lamT = np.maximum(lamT, 1e-30)
    T_ma = (qT * (lamT ** (-alpha))) @ qT.conj().T

    svds = []
    H = np.zeros((n, n), dtype=dtype)
    for k in range(m):
        Ak = Ws[k] @ T_ma
        uk, sk, vhk = np.linalg.svd(Ak, full_matrices=True)
        svds.append((uk, sk, vhk))
        H += (vhk.conj().T * sk) @ vhk
    H = 0.5 * (H + H.conj().T)

    lamH, qH = np.linalg.eigh(H)
    lamH_pos = np.maximum(lamH, 0.0)
    num_p = float(np.sum(lamT))
    den_p = float(np.sum(lamH_pos ** p))
    val = -(np.log(num_p) - np.log(den_p)) / p

    lamH_pm1 = np.where(lamH_pos > 1e-20, lamH_pos ** (p - 1.0), 0.0)
    M = (qH * lamH_pm1) @ qH.conj().T

    def grad_abs_A(uX, sX, vhX, M_mat):
        M_hat = vhX @ M_mat @ vhX.conj().T
        denom = sX[:, None] + sX[None, :]
        mask = denom > 1e-20
        coeff = np.zeros_like(denom)
        coeff[mask] = (2.0 * sX[:, None] / np.where(mask, denom, 1.0))[mask]
        return (uX @ (coeff * M_hat)) @ vhX

    gAs = [grad_abs_A(uk, sk, vhk, M) for (uk, sk, vhk) in svds]
    G_Tma = np.zeros((n, n), dtype=dtype)
    for k in range(m):
        G_Tma += Ws[k] @ gAs[k]
    G_Tma = 0.5 * (G_Tma + G_Tma.conj().T)

    fa = lamT ** (-alpha)
    diff_lam = lamT[:, None] - lamT[None, :]
    diff_fa = fa[:, None] - fa[None, :]
    D_div = np.where(
        np.abs(diff_lam) > 1e-12 * (lamT[:, None] + lamT[None, :]),
        diff_fa / np.where(np.abs(diff_lam) > 1e-30, diff_lam, 1.0),
        -alpha * (0.5 * (lamT[:, None] + lamT[None, :])) ** (-alpha - 1.0)
    )
    G_T_hat = qT.conj().T @ G_Tma @ qT
    gT_from_den = 0.5 * (qT @ (D_div * G_T_hat) @ qT.conj().T + (qT @ (D_div * G_T_hat) @ qT.conj().T).conj().T)

    grads = []
    for k in range(m):
        gWk_dir = 0.5 * (gAs[k] @ T_ma + (gAs[k] @ T_ma).conj().T)
        gWk = -(1.0 / (p * num_p)) * np.eye(n, dtype=dtype) + (1.0 / den_p) * (gWk_dir + gT_from_den)
        gWk = 0.5 * (gWk + gWk.conj().T)
        gZk = 2.0 * (gWk @ Zs[k])
        if complex_mode:
            grads.append(np.real(gZk).ravel()); grads.append(np.imag(gZk).ravel())
        else:
            grads.append(gZk.ravel())
    return float(val), np.concatenate(grads)


def ka_to_psd_seed(S_list, p):
    r"""
    Exact embedding from Theorem 10(1) proof: converts m Kubo-Ando matrices S_j (N x N)
    into exact mN x mN PSD matrices W_k (Theorem 5) with IDENTICAL Lee ratio!
    A_k = T^{s/2} P_k T^{1/2} where T = diag(S_1, ..., S_m), P_k = (f_k f_k^*) \otimes I_N.
    Wait: S = sum A_k = T^{(s+1)/2} = T^{1/(2-p)}, so T_PSD = S^p = T^s = diag(S_1^s, ..., S_m^s),
    and W_k = A_k S^{p-1} = T^{s/2} P_k T^{1/2 + (p-1)/(2-p)} = T^{s/2} P_k T^{s/2}!!
    CHECK: 1/2 + (p-1)/(2-p) = (2-p + 2p-2)/(2(2-p)) = p/(2(2-p)) = s/2!!
    So W_k = (T^{s/2} (f_k \otimes I_N)) (T^{s/2} (f_k \otimes I_N))^* has exact rank N!!
    """
    m = len(S_list)
    N = S_list[0].shape[0]
    s = p / (2.0 - p)
    n = m * N
    # Discrete Fourier basis f_k (or real orthogonal for m=2!)
    if m == 2:
        F = np.array([[1.0, 1.0], [1.0, -1.0]]) / np.sqrt(2.0)
        is_c = any(np.iscomplexobj(S) for S in S_list)
    else:
        idx = np.arange(m)
        F = np.exp(2j * np.pi * np.outer(idx, idx) / m) / np.sqrt(m)
        is_c = True
    # Build T^{s/2} block diagonal
    S_shalf = []
    for S in S_list:
        ev, Q = np.linalg.eigh(0.5 * (S + S.conj().T))
        ev = np.maximum(ev, 1e-30)
        S_shalf.append((Q * (ev ** (0.5 * s))) @ Q.conj().T)
    Zs = []
    for k in range(m):
        # Z_k (mN x N): j-th N x N block is F[j, k] * S_j^{s/2}
        Z_k = np.vstack([F[j, k] * S_shalf[j] for j in range(m)])
        if not is_c:
            Z_k = np.real(Z_k)
        Zs.append(Z_k)
    return Zs, is_c


# =============================================================================
# PART 2: D-EIGENBASIS GRAPH/CYCLE ANATOMY DIAGNOSTIC
# =============================================================================

def inspect_D_eigenbasis_anatomy(S_list, K, p, kappa, tol_edge=1e-3):
    """
    Transform (S_1, ..., S_m) into the CANONICAL eigenbasis of K = D (sorted descending, d_0 = 1).
    Inside any degenerate eigenspace of K (|d_i - d_j| < 1e-4 * d_i), rotate to diagonalize
    a generic combination sum_j c_j E_j so degenerate tree siblings are NOT spuriously mixed!
    """
    m = len(S_list)
    N = S_list[0].shape[0]
    s = p / (2.0 - p)
    ld, Q = np.linalg.eigh(0.5 * (K + K.conj().T))
    idx = np.argsort(ld)[::-1]
    ld = ld[idx]; Q = Q[:, idx]
    d = ld / ld[0]

    # Canonical basis alignment on degenerate eigenspaces of K using generic sum c_j E_j!
    c_weights = [1.0 + 0.37 * j + 0.13 * j * j for j in range(m)]
    # Compute E_comb in initial Q-basis
    E_comb = np.zeros((N, N), dtype=np.complex128 if any(np.iscomplexobj(S) for S in S_list) else np.float64)
    for j in range(m):
        Sj0 = Q.conj().T @ S_list[j] @ Q / (ld[0] ** (2.0 * kappa - 2.0))
        Sj0 = 0.5 * (Sj0 + Sj0.conj().T)
        Ej0 = herm_pow(Sj0, s, tol=0.0) - (d[:, None] * Sj0) * d[None, :]
        E_comb += c_weights[j] * Ej0
    E_comb = 0.5 * (E_comb + E_comb.conj().T)
    # Find degenerate clusters in d and diagonalize E_comb within each cluster!
    i = 0
    while i < N:
        j_end = i + 1
        while j_end < N and abs(d[j_end] - d[i]) < 1e-4 * max(d[i], 1e-30):
            j_end += 1
        if j_end - i > 1:
            sub = E_comb[i:j_end, i:j_end]
            _, Usub = np.linalg.eigh(0.5 * (sub + sub.conj().T))
            Q[:, i:j_end] = Q[:, i:j_end] @ Usub
        i = j_end

    sd = np.sqrt(d); sm = 1.0 / sd
    X_norms = []
    E_list = []
    off_E_max = 0.0
    block_list = []
    for j in range(m):
        Sj = Q.conj().T @ S_list[j] @ Q / (ld[0] ** (2.0 * kappa - 2.0))
        Sj = 0.5 * (Sj + Sj.conj().T)
        Gj = herm_pow(Sj, 1.0 / (kappa - 1.0), tol=0.0)
        Hj = (sm[:, None] * Gj) * sm[None, :]
        Xj = (sm[:, None] * Hj) * sm[None, :]
        Ej = herm_pow(Sj, s, tol=0.0) - (d[:, None] * Sj) * d[None, :]
        scE = d ** kappa
        E_sc = Ej / np.outer(scE, scE)
        E_list.append(E_sc)
        off_E = float(np.linalg.norm(E_sc - np.diag(np.diag(E_sc))))
        off_E_max = max(off_E_max, off_E)

        diagX = np.sqrt(np.maximum(np.real(np.diag(Xj)), 1e-30))
        Xn = np.abs(Xj) / np.outer(diagX, diagX)
        np.fill_diagonal(Xn, 0.0)
        X_norms.append(Xn)

        vis = [False] * N
        comps = []
        for u in range(N):
            if not vis[u]:
                comp = []; st = [u]; vis[u] = True
                while st:
                    w = st.pop(); comp.append(w)
                    for v in range(N):
                        if not vis[v] and Xn[w, v] > tol_edge:
                            vis[v] = True; st.append(v)
                comps.append(sorted(comp))
        block_list.append(comps)

    max_overlap = 0.0
    max_comm_E = 0.0
    for a in range(m):
        for b in range(a + 1, m):
            max_overlap = max(max_overlap, float(np.max(np.minimum(X_norms[a], X_norms[b]))))
            max_comm_E = max(max_comm_E, float(np.linalg.norm(E_list[a] @ E_list[b] - E_list[b] @ E_list[a])))

    nontriv_blocks = []
    for j in range(m):
        for comp in block_list[j]:
            if len(comp) >= 2:
                nontriv_blocks.append((j, comp))
    V_bc = N + len(nontriv_blocks)
    E_bc = sum(len(comp) for _, comp in nontriv_blocks)
    adj = [[] for _ in range(V_bc)]
    for b_idx, (_, comp) in enumerate(nontriv_blocks):
        b_node = N + b_idx
        for v in comp:
            adj[v].append(b_node); adj[b_node].append(v)
    vis = [False] * V_bc
    C_bc = 0
    for u in range(V_bc):
        if not vis[u]:
            C_bc += 1; st = [u]; vis[u] = True
            while st:
                w = st.pop()
                for nb in adj[w]:
                    if not vis[nb]:
                        vis[nb] = True; st.append(nb)
    beta1 = E_bc - V_bc + C_bc
    return {
        "d": d, "off_E_max": off_E_max, "max_overlap": max_overlap,
        "max_comm_E": max_comm_E, "blocks": block_list, "beta1": beta1,
        "n_nontriv": len(nontriv_blocks),
    }


# =============================================================================
# PART 3: 50-DIGIT MPMATH EXACT EVALUATOR + EXACT LOOP-CLOSURE DERIVATIVES
# =============================================================================

def mp_eigh_herm(M, dps=50):
    mp.mp.dps = dps
    n = M.rows
    is_cplx = any(mp.im(M[i, j]) != 0 for i in range(n) for j in range(n))
    if not is_cplx:
        A = mp.matrix([[mp.re(M[i, j]) for j in range(n)] for i in range(n)])
        ev, Q = mp.eigsy(A, eigvals_only=False)
        return list(ev), Q
    R = mp.matrix(2 * n, 2 * n)
    for i in range(n):
        for j in range(n):
            a = mp.re(M[i, j]); b = mp.im(M[i, j])
            R[i, j] = a; R[i + n, j + n] = a
            R[i, j + n] = -b; R[i + n, j] = b
    ev2, Q2 = mp.eigsy(R, eigvals_only=False)
    ev_out, cols = [], []
    i = 0
    while i < 2 * n:
        lam = ev2[i]; j = i + 1
        while j < 2 * n and abs(ev2[j] - lam) < mp.mpf("1e-22") * max(mp.mpf(1), abs(lam)):
            j += 1
        mult = (j - i) // 2
        basis = []
        for col in range(i, j):
            v = [mp.mpc(Q2[r, col], Q2[r + n, col]) for r in range(n)]
            for bvec in basis:
                ip = mp.fsum(mp.conj(bvec[r]) * v[r] for r in range(n))
                v = [v[r] - ip * bvec[r] for r in range(n)]
            nrm = mp.sqrt(mp.fsum(abs(v[r]) ** 2 for r in range(n)))
            if nrm > mp.mpf("1e-18"):
                basis.append([v[r] / nrm for r in range(n)])
                if len(basis) == mult:
                    break
        for bvec in basis:
            ev_out.append(lam); cols.append(bvec)
        i = j
    Q = mp.matrix(n, n)
    for c_idx in range(n):
        for r_idx in range(n):
            Q[r_idx, c_idx] = cols[c_idx][r_idx]
    return ev_out, Q


def mp_herm_pow(M, power, dps=50):
    mp.mp.dps = dps
    ev, Q = mp_eigh_herm(M, dps=dps)
    n = M.rows
    Qp = mp.matrix(n, n)
    for j in range(n):
        lp = ev[j] ** power
        for i in range(n):
            Qp[i, j] = Q[i, j] * lp
    res = Qp * Q.transpose_conj()
    return mp.mpf("0.5") * (res + res.transpose_conj())


def mp_eval_kubo_ando_mp(S_mp_list, p_frac, dps=50):
    """Exact dps-digit Kubo-Ando evaluation on list of mp.matrix (real or complex Hermitian)."""
    mp.mp.dps = dps
    p = mp.mpf(p_frac[0]) / mp.mpf(p_frac[1])
    s = p / (2 - p)
    m = len(S_mp_list)
    N = S_mp_list[0].rows
    M = mp.zeros(N, N); N_mat = mp.zeros(N, N)
    num = mp.mpf(0)
    S_halves = []
    for S_mp in S_mp_list:
        Sh = mp.mpf("0.5") * (S_mp + S_mp.transpose_conj())
        ev, Q = mp_eigh_herm(Sh, dps=dps)
        assert min(ev) > 0, f"Non-SPD S in mp_eval_kubo_ando_mp: min_ev={min(ev)}"
        num += mp.fsum(e ** s for e in ev)
        Qs = mp.matrix(N, N); Qh = mp.matrix(N, N)
        for j in range(N):
            es = ev[j] ** s; eh = mp.sqrt(ev[j])
            for i in range(N):
                Qs[i, j] = Q[i, j] * es
                Qh[i, j] = Q[i, j] * eh
        M += Qs * Q.transpose_conj()
        N_mat += Sh
        S_h = Qh * Q.transpose_conj()
        S_halves.append(mp.mpf("0.5") * (S_h + S_h.transpose_conj()))

    M = mp.mpf("0.5") * (M + M.transpose_conj())
    N_mat = mp.mpf("0.5") * (N_mat + N_mat.transpose_conj())
    N_half = mp_herm_pow(N_mat, mp.mpf("0.5"), dps=dps)
    N_mhalf = mp_herm_pow(N_mat, mp.mpf("-0.5"), dps=dps)
    C_mat = N_half * M * N_half
    C_mat = mp.mpf("0.5") * (C_mat + C_mat.transpose_conj())
    C_half = mp_herm_pow(C_mat, mp.mpf("0.5"), dps=dps)
    K = N_mhalf * C_half * N_mhalf
    K = mp.mpf("0.5") * (K + K.transpose_conj())

    knk_err = mp.norm(K * N_mat * K - M) / max(mp.mpf(1), mp.norm(M))
    assert knk_err < mp.mpf(10) ** (-(dps - 12)), f"K N K != M: err={knk_err}"

    den = mp.mpf(0)
    for j in range(m):
        Y = S_halves[j] * K * S_halves[j]
        Y = mp.mpf("0.5") * (Y + Y.transpose_conj())
        evY, _ = mp_eigh_herm(Y, dps=dps)
        den += mp.fsum(e ** p for e in evY)
    return (num / den) ** (1 / p)


def mp_eval_direct_schatten_from_ka(S_list_np, p_frac, dps=50):
    """
    Independent direct Schatten-p ratio ||sum A_k||_p / ||sum |A_k|||_p in 50-dps mpmath
    via Theorem 10(1) Fourier construction A_k = T^{s/2} P_k T^{1/2} (ZERO Kubo-Ando shortcut!).
    """
    mp.mp.dps = dps
    p = mp.mpf(p_frac[0]) / mp.mpf(p_frac[1])
    s = p / (2 - p)
    m = len(S_list_np)
    N = S_list_np[0].shape[0]
    n = m * N
    S_half = []; S_shalf = []
    num = mp.mpf(0)
    for S_np in S_list_np:
        is_c = np.iscomplexobj(S_np)
        M = mp.matrix(N, N)
        for i in range(N):
            for j in range(N):
                M[i, j] = mp.mpc(repr(float(np.real(S_np[i, j]))), repr(float(np.imag(S_np[i, j])))) if is_c else mp.mpf(repr(float(S_np[i, j])))
        M = mp.mpf("0.5") * (M + M.transpose_conj())
        ev, Q = mp_eigh_herm(M, dps=dps)
        num += mp.fsum(e ** s for e in ev)
        Qh = mp.matrix(N, N); Qs = mp.matrix(N, N)
        for j in range(N):
            eh = mp.sqrt(ev[j]); es = ev[j] ** (s / 2)
            for i in range(N):
                Qh[i, j] = Q[i, j] * eh; Qs[i, j] = Q[i, j] * es
        S_half.append(Qh * Q.transpose_conj())
        S_shalf.append(Qs * Q.transpose_conj())
    # Fourier matrix F (m x m)
    F = mp.matrix(m, m)
    for j in range(m):
        for k in range(m):
            ang = 2 * mp.pi * j * k / m
            F[j, k] = (mp.cos(ang) + mp.mpc(0, 1) * mp.sin(ang)) / mp.sqrt(m)
    # Build H_sum = sum_{k=0}^{m-1} |A_k| where A_k = (T^{s/2} (f_k \otimes I_N)) (T^{1/2} (f_k \otimes I_N))^*
    # Wait: A_k^* A_k = B_k (C_k^* C_k) B_k^* where B_k = T^{1/2} (f_k \otimes I_N) (n x N), C_k = T^{s/2} (f_k \otimes I_N) (n x N)
    # Even more directly: assemble full n x n A_k, compute A_k^* A_k, take exact Hermitian square root!
    H_sum = mp.zeros(n, n)
    S_sum = mp.zeros(n, n)
    for k in range(m):
        Ck = mp.matrix(n, N); Bk = mp.matrix(n, N)
        for j in range(m):
            fjk = F[j, k]
            for r in range(N):
                for c in range(N):
                    Ck[j * N + r, c] = S_shalf[j][r, c] * fjk
                    Bk[j * N + r, c] = S_half[j][r, c] * fjk
        Ak = Ck * Bk.transpose_conj()
        S_sum += Ak
        Gram = Ak.transpose_conj() * Ak
        Gram = mp.mpf("0.5") * (Gram + Gram.transpose_conj())
        evG, QG = mp_eigh_herm(Gram, dps=dps)
        max_evG = max(mp.re(e) for e in evG)
        cut_evG = max_evG * (mp.mpf(10) ** (-(dps - 6)))
        Qrt = mp.matrix(n, n)
        for j in range(n):
            val_e = mp.re(evG[j])
            rt = mp.sqrt(val_e) if val_e > cut_evG else mp.mpf(0)
            for i in range(n):
                Qrt[i, j] = QG[i, j] * rt
        H_sum += Qrt * QG.transpose_conj()
    H_sum = mp.mpf("0.5") * (H_sum + H_sum.transpose_conj())
    SS = S_sum.transpose_conj() * S_sum
    SS = mp.mpf("0.5") * (SS + SS.transpose_conj())
    evS, _ = mp_eigh_herm(SS, dps=dps)
    evH, _ = mp_eigh_herm(H_sum, dps=dps)
    max_evS = max(mp.re(e) for e in evS)
    max_evH = max(mp.re(e) for e in evH)
    num_direct = mp.fsum(mp.re(e) ** (p / 2) for e in evS if mp.re(e) > max_evS * (mp.mpf(10) ** (-(dps - 6))))
    den_direct = mp.fsum(mp.re(e) ** p for e in evH if mp.re(e) > max_evH * (mp.mpf(10) ** (-(dps - 6))))
    return (num_direct / den_direct) ** (1 / p)


def mp_eval_kubo_ando_from_np(S_list_np, p_frac, dps=50):
    mp.mp.dps = dps
    S_mps = []
    for S_np in S_list_np:
        N = S_np.shape[0]
        is_c = np.iscomplexobj(S_np) and (float(np.max(np.abs(np.imag(S_np)))) > 1e-16)
        M = mp.matrix(N, N)
        for i in range(N):
            for j in range(N):
                if is_c:
                    M[i, j] = mp.mpc(repr(float(np.real(S_np[i, j]))), repr(float(np.imag(S_np[i, j]))))
                else:
                    M[i, j] = mp.mpf(repr(float(np.real(S_np[i, j]))))
        S_mps.append(mp.mpf("0.5") * (M + M.transpose_conj()))
    return mp_eval_kubo_ando_mp(S_mps, p_frac, dps=dps)


def mp_polish_finite_tree_holden(S_list_np, block_partitions, p_frac, dps=50):
    """
    Newton-polish an EXACT finite-N tree Holden solution (D, X_1, ..., X_m, Lam) to 45+ digits
    in mpmath! Because it is a tree with distinct scales (or symmetric siblings),
    Holden equations (4.1)-(4.2) have exact zero residual (< 1e-42)!
    Returns (Lam_mp, C_mp, S_mp_list, res_norm).
    """
    mp.mp.dps = dps
    p = mp.mpf(p_frac[0]) / mp.mpf(p_frac[1])
    kap = p / (2 * (p - 1))
    m = len(block_partitions)
    N = S_list_np[0].shape[0]

    # Initial D, X_j from float64 solution in eigenbasis of K
    R0, K0 = ka_eval_only(S_list_np, float(p))
    ld, Q = np.linalg.eigh(0.5 * (K0 + K0.T))
    # Preserve vertex ordering closest to K0 diagonal!
    # Check if K0 is already nearly diagonal:
    if np.linalg.norm(K0 - np.diag(np.diag(K0))) / np.linalg.norm(K0) < 1e-3:
        d_init = np.diag(K0).copy()
        d0_sc = d_init[0]
        d_init = d_init / d0_sc
        S_work = [S / (d0_sc ** (2.0 * float(kap) - 2.0)) for S in S_list_np]
    else:
        raise ValueError("Tree seed does not have nearly diagonal K0")

    Lam_init = (2.0 ** (2.0 * float(kap) - 1.0)) * (R0 ** (2.0 * float(kap)))
    sd = np.sqrt(d_init); sm = 1.0 / sd
    X_inits = []
    for j in range(m):
        Gj = herm_pow(S_work[j], 1.0 / (float(kap) - 1.0), tol=0.0)
        Hj = (sm[:, None] * Gj) * sm[None, :]
        Xj = (sm[:, None] * Hj) * sm[None, :]
        X_inits.append(0.5 * (Xj + Xj.T))

    # Build variable layout: [Lam, d_1..d_{N-1}, upper tri of each block in block_partitions]
    tri_layout = []
    for j in range(m):
        for B in block_partitions[j]:
            b = len(B)
            for a_i in range(b):
                for b_i in range(a_i, b):
                    tri_layout.append((j, B[a_i], B[b_i]))
    n_unk = N + len(tri_layout)

    def eval_res(xv):
        Lam = xv[0]
        dd = [mp.mpf(1)] + [xv[1 + i] for i in range(N - 1)]
        sdd = [mp.sqrt(v) for v in dd]
        Xs = [mp.zeros(N, N) for _ in range(m)]
        for k, (j, u, v) in enumerate(tri_layout):
            Xs[j][u, v] = xv[N + k]; Xs[j][v, u] = xv[N + k]
        out = []
        E_diag = [mp.mpf(0)] * N
        for j in range(m):
            for B in block_partitions[j]:
                b = len(B)
                # Solve block locally (fast!)
                Db = mp.diag([dd[u] for u in B])
                sdb = [sdd[u] for u in B]
                Hb = mp.matrix(b, b); Gb = mp.matrix(b, b)
                for r1 in range(b):
                    for r2 in range(b):
                        Hb[r1, r2] = sdb[r1] * Xs[j][B[r1], B[r2]] * sdb[r2]
                        Gb[r1, r2] = sdb[r1] * Hb[r1, r2] * sdb[r2]
                Mb = Db + Hb
                Mpow = mp_herm_pow(Mb, 2 * kap - 1, dps=dps)
                Gkm1 = mp_herm_pow(Gb, kap - 1, dps=dps)
                Gk = mp_herm_pow(Gb, kap, dps=dps)
                # R1 on upper triangle of block
                for r1 in range(b):
                    for r2 in range(r1, b):
                        val1 = Mpow[r1, r2] - Lam * sdb[r1] * Gkm1[r1, r2] * sdb[r2]
                        out.append(val1 / ((dd[B[r1]] * dd[B[r2]]) ** (kap - mp.mpf("0.5"))))
                # E_j diagonal contribution (note off-diagonals of E_j vanish automatically by [E_j, D]=0!)
                for r1 in range(b):
                    E_diag[B[r1]] += Gk[r1, r1] - dd[B[r1]] * Gkm1[r1, r1] * dd[B[r1]]
        for i in range(N):
            out.append(E_diag[i] / (dd[i] ** (2 * kap)))
        return mp.matrix(out)

    x_init = [mp.mpf(repr(float(Lam_init)))] + [mp.mpf(repr(float(v))) for v in d_init[1:]]
    for (j, u, v) in tri_layout:
        x_init.append(mp.mpf(repr(float(X_inits[j][u, v]))))
    x = mp.matrix(x_init)

    eps_fd = mp.mpf(10) ** (-(dps // 2))
    for it in range(10):
        F0 = eval_res(x)
        nrm = mp.norm(F0)
        if nrm < mp.mpf(10) ** (-(dps - 8)):
            break
        J = mp.matrix(n_unk, n_unk)
        for col in range(n_unk):
            xp_v = x.copy()
            h = eps_fd * max(mp.mpf(1), abs(x[col]))
            xp_v[col] += h
            Fj = eval_res(xp_v)
            for row in range(n_unk):
                J[row, col] = (Fj[row] - F0[row]) / h
        dx = mp.lu_solve(J, -F0)
        x = x + dx
    F_fin = eval_res(x)
    res_norm = mp.norm(F_fin)
    Lam = x[0]
    C_mp = (Lam / (mp.mpf(2) ** (2 * kap - 1))) ** (1 / (2 * kap))
    dd = [mp.mpf(1)] + [x[1 + i] for i in range(N - 1)]
    sdd = [mp.sqrt(v) for v in dd]
    Xs = [mp.zeros(N, N) for _ in range(m)]
    for k, (j, u, v) in enumerate(tri_layout):
        Xs[j][u, v] = x[N + k]; Xs[j][v, u] = x[N + k]
    S_mps = []
    for j in range(m):
        Sj = mp.zeros(N, N)
        for B in block_partitions[j]:
            b = len(B)
            Gb = mp.matrix(b, b)
            for r1 in range(b):
                for r2 in range(b):
                    Gb[r1, r2] = dd[B[r1]] * Xs[j][B[r1], B[r2]] * dd[B[r2]]
            Gkm1 = mp_herm_pow(Gb, kap - 1, dps=dps)
            for r1 in range(b):
                for r2 in range(b):
                    Sj[B[r1], B[r2]] = Gkm1[r1, r2]
        S_mps.append(Sj)
    return Lam, C_mp, S_mps, res_norm


def mp_loop_closure_derivatives(S_mp_list, j_col, u, v, p_frac, dps=50):
    """
    EXACT 50-DIGIT MPMATH LOOP-CLOSURE PERTURBATION DIAGNOSTIC!
    Perturb S_{j_col}(eps) = S_{j_col} + eps * sqrt(S_uu S_vv) * (e^{i theta} E_{uv} + e^{-i theta} E_{vu})
    for theta in {0, pi/4, pi/2, 3*pi/4, pi}!
    Computes exact R'(0), R''(0), R'''(0) at eps = 1e-9 (cross-checked at 2e-9) AND finite-eps R(+-0.01)!
    """
    mp.mp.dps = dps
    R0 = mp_eval_kubo_ando_mp(S_mp_list, p_frac, dps=dps)
    sc = mp.sqrt(mp.re(S_mp_list[j_col][u, u]) * mp.re(S_mp_list[j_col][v, v]))
    h = mp.mpf("1e-9")

    def eval_at(eps_val, theta):
        phase = mp.cos(theta) + mp.mpc(0, 1) * mp.sin(theta) if theta != 0 and theta != mp.pi else (mp.mpf(1) if theta == 0 else mp.mpf(-1))
        S_new = [M.copy() for M in S_mp_list]
        delta = eps_val * sc * phase
        S_new[j_col][u, v] += delta
        S_new[j_col][v, u] += mp.conj(delta)
        return mp_eval_kubo_ando_mp(S_new, p_frac, dps=dps)

    thetas = [
        ("0 (Re+)", mp.mpf(0)),
        ("pi/4", mp.pi / 4),
        ("pi/2 (Im)", mp.pi / 2),
        ("3pi/4", 3 * mp.pi / 4),
        ("pi (Re-)", mp.pi),
    ]
    out = {}
    for tname, th in thetas:
        rp = eval_at(h, th)
        rm = eval_at(-h, th)
        r2p = eval_at(2 * h, th)
        r2m = eval_at(-2 * h, th)
        # 4th-order stencils (truncation error O(h^4) ~ 1e-36 at h=1e-9!)
        d1 = (r2m - 8 * rm + 8 * rp - r2p) / (12 * h)
        d2 = (-r2m + 16 * rm - 30 * R0 + 16 * rp - r2p) / (12 * h * h)
        d3 = (r2p - 2 * rp + 2 * rm - r2m) / (2 * h * h * h)
        # Finite-amplitude test at eps = 0.01 (safe SPD since |delta| = 0.01 sqrt(S_uu S_vv))
        rf_p = eval_at(mp.mpf("0.01"), th) - R0
        out[tname] = (d1, d2, d3, rf_p)
    return R0, out


# =============================================================================
# PART 4: FULL NON-GAUGE REAL & COMPLEX HESSIAN (ON EXACT POLISHED TREES!)
# =============================================================================

def full_nongauge_hessian(S_list_np, block_partitions, p):
    """
    Compute full non-gauge real AND purely-imaginary Hessian eigenvalues + per-edge
    Schur-complement effective loop-closure curvature (with ALL gauge modes properly
    eliminated first!).
    """
    m = len(S_list_np)
    N = S_list_np[0].shape[0]
    _, R0, g0, K0 = ka_eval_and_grad_S_list(S_list_np, p)
    tree_mask = [np.zeros((N, N), dtype=bool) for _ in range(m)]
    for j in range(m):
        for B in block_partitions[j]:
            for u in B:
                for v in B:
                    tree_mask[j][u, v] = True
    g_tr = max(float(np.max(np.abs(g0[j][tree_mask[j]]))) for j in range(m))
    g_lp = max(float(np.max(np.abs(g0[j][~tree_mask[j]]))) if np.any(~tree_mask[j]) else 0.0 for j in range(m))

    eps_h = 1e-5

    # --- REAL SYMMETRIC ---
    r_basis, r_tree, r_meta = [], [], []
    for j in range(m):
        for u in range(N):
            for v in range(u, N):
                E = np.zeros((N, N))
                if u == v:
                    E[u, u] = 1.0
                else:
                    E[u, v] = E[v, u] = 1.0 / np.sqrt(2.0)
                r_basis.append((j, E)); r_tree.append(bool(tree_mask[j][u, v])); r_meta.append((j, u, v))
    nr = len(r_basis)
    scales_r = np.array([np.sqrt(max(S_list_np[j][u, u] * S_list_np[j][v, v], 1e-28)) for (j, u, v) in r_meta])
    Hr = np.zeros((nr, nr))
    for a, (ja, Ea) in enumerate(r_basis):
        step = eps_h * scales_r[a]
        Sp = [S.copy() for S in S_list_np]; Sp[ja] += step * Ea
        Sm = [S.copy() for S in S_list_np]; Sm[ja] -= step * Ea
        _, _, gp, _ = ka_eval_and_grad_S_list(Sp, p)
        _, _, gm, _ = ka_eval_and_grad_S_list(Sm, p)
        dg = [-(gp[k] - gm[k]) / (2.0 * step) for k in range(m)]
        for b, (jb, Eb) in enumerate(r_basis):
            Hr[b, a] = float(np.sum(dg[jb] * Eb))
    Hr = 0.5 * (Hr + Hr.T)
    # Note: ka_eval_and_grad_S_list returns grad(-log R), so Hr = Hess(log R);
    # at a stationary point Hess(R) = R0 * Hess(log R)!
    Hr_s = R0 * ((scales_r[:, None] * Hr) * scales_r[None, :])

    # Real gauge: scale + O(N) rotations
    gvecs_r = [np.array([float(np.sum(S_list_np[ja] * Ea)) for (ja, Ea) in r_basis])]
    for u in range(N):
        for v in range(u + 1, N):
            Ksk = np.zeros((N, N)); Ksk[u, v] = 1.0; Ksk[v, u] = -1.0
            gvecs_r.append(np.array([float(np.sum((Ksk @ S_list_np[ja] - S_list_np[ja] @ Ksk) * Ea)) for (ja, Ea) in r_basis]))
    Gr_s = np.column_stack(gvecs_r) / scales_r[:, None]
    Ur, sr, _ = np.linalg.svd(Gr_s, full_matrices=True)
    rk_r = int(np.sum(sr > 1e-10 * sr[0]))
    Qr_perp = Ur[:, rk_r:]
    Hr_perp = Qr_perp.T @ Hr_s @ Qr_perp
    eigs_r = np.linalg.eigvalsh(0.5 * (Hr_perp + Hr_perp.T))

    # --- IMAGINARY HERMITIAN ---
    i_basis, i_tree, i_meta = [], [], []
    for j in range(m):
        for u in range(N):
            for v in range(u + 1, N):
                E = np.zeros((N, N), dtype=np.complex128)
                E[u, v] = 1j / np.sqrt(2.0); E[v, u] = -1j / np.sqrt(2.0)
                i_basis.append((j, E)); i_tree.append(bool(tree_mask[j][u, v])); i_meta.append((j, u, v))
    ni = len(i_basis)
    scales_i = np.array([np.sqrt(max(S_list_np[j][u, u] * S_list_np[j][v, v], 1e-28)) for (j, u, v) in i_meta])
    Hi = np.zeros((ni, ni))
    for a, (ja, Ea) in enumerate(i_basis):
        step = eps_h * scales_i[a]
        Sp = [S.astype(np.complex128) for S in S_list_np]; Sp[ja] += step * Ea
        Sm = [S.astype(np.complex128) for S in S_list_np]; Sm[ja] -= step * Ea
        _, _, gp, _ = ka_eval_and_grad_S_list(Sp, p)
        _, _, gm, _ = ka_eval_and_grad_S_list(Sm, p)
        dg = [-(gp[k] - gm[k]) / (2.0 * step) for k in range(m)]
        for b, (jb, Eb) in enumerate(i_basis):
            Hi[b, a] = float(np.real(np.sum(dg[jb] * Eb.conj())))
    Hi = 0.5 * (Hi + Hi.T)
    Hi_s = R0 * ((scales_i[:, None] * Hi) * scales_i[None, :])

    gvecs_i = []
    for u in range(N):
        for v in range(u, N):
            Hs = np.zeros((N, N))
            if u == v: Hs[u, u] = 1.0
            else: Hs[u, v] = Hs[v, u] = 1.0
            gvecs_i.append(np.array([float(np.real(np.sum((1j * (Hs @ S_list_np[ja] - S_list_np[ja] @ Hs)) * Ea.conj()))) for (ja, Ea) in i_basis]))
    Gi_s = np.column_stack(gvecs_i) / scales_i[:, None]
    Ui, si, _ = np.linalg.svd(Gi_s, full_matrices=True)
    rk_i = int(np.sum(si > 1e-10 * si[0]))
    Qi_perp = Ui[:, rk_i:]
    Hi_perp = Qi_perp.T @ Hi_s @ Qi_perp
    eigs_i = np.linalg.eigvalsh(0.5 * (Hi_perp + Hi_perp.T))

    # Effective (relaxed) loop-edge curvature: min over tree perturbations ONLY (never using gauge!).
    # Because gauge modes can mix tree & loop, the exact quadratic response to adding eps*e_loop + d_tree
    # (holding all OTHER loop edges = 0!) is e_loop^T (H_ll - H_lT H_TT^+ H_Tl) e_loop.
    # For a strict local max, H_perp < 0 guarantees H_TT <= 0 (with only 1D scale nullspace in H_TT!)
    # and therefore H_eff = H_ll - H_lT H_TT^+ H_Tl < 0 ALWAYS!
    t_idx_r = [k for k, f in enumerate(r_tree) if f]
    l_idx_r = [k for k, f in enumerate(r_tree) if not f]
    HTT_r = Hr_s[np.ix_(t_idx_r, t_idx_r)]
    et, Qt = np.linalg.eigh(0.5 * (HTT_r + HTT_r.T))
    # Only drop the exact 1D global scale null mode (smallest |eig|)!
    i_drop = int(np.argmin(np.abs(et)))
    inv_et = np.array([0.0 if k == i_drop else 1.0 / et[k] for k in range(len(et))])
    HTT_pinv_r = (Qt * inv_et) @ Qt.T

    t_idx_i = [k for k, f in enumerate(i_tree) if f]
    imag_map = {i_meta[k]: k for k in range(ni)}
    if len(t_idx_i) > 0:
        HTT_i = Hi_s[np.ix_(t_idx_i, t_idx_i)]
        eti, Qti = np.linalg.eigh(0.5 * (HTT_i + HTT_i.T))
        inv_eti = np.where(np.abs(eti) > 1e-13 * max(abs(eti[0]), 1.0), 1.0 / eti, 0.0)
        HTT_pinv_i = (Qti * inv_eti) @ Qti.T
    else:
        HTT_pinv_i = np.zeros((0, 0))

    edge_table = []
    for a in l_idx_r:
        j, u, v = r_meta[a]
        bare_re = 2.0 * Hr_s[a, a]
        hl = Hr_s[t_idx_r, a]
        eff_re = 2.0 * (Hr_s[a, a] - float(hl @ HTT_pinv_r @ hl))
        ia = imag_map[(j, u, v)]
        bare_im = 2.0 * Hi_s[ia, ia]
        if len(t_idx_i) > 0:
            hli = Hi_s[t_idx_i, ia]
            eff_im = 2.0 * (Hi_s[ia, ia] - float(hli @ HTT_pinv_i @ hli))
        else:
            eff_im = bare_im
        edge_table.append((j, (u, v), bare_re, eff_re, bare_im, eff_im))

    return {
        "R0": R0, "g_tr": g_tr, "g_lp": g_lp,
        "max_eig_r": float(np.max(eigs_r)), "max_eig_i": float(np.max(eigs_i)),
        "n_pos_r": int(np.sum(eigs_r > 1e-11)), "n_pos_i": int(np.sum(eigs_i > 1e-11)),
        "top3_r": [float(v) for v in eigs_r[-3:]],
        "top3_i": [float(v) for v in eigs_i[-3:]],
        "edges": edge_table,
    }


# =============================================================================
# PART 5: FIXED DIRECT MULTI-BLOCK HOLDEN SOLVER (INCLUDING DEGENERATE-D!)
# =============================================================================

def solve_direct_holden_loopy(p_val, kappa, m, topology, rng):
    """
    Fixed-dimension Newton/least_squares solver for direct multi-block Holden solutions
    (4.1)-(4.2) on loopy graphs: C_4 (m=2), Overlap3x3_N4 (m=2), C_3 (m=3), K_4 (m=3),
    K_{3,3}=Cay(S_3) (m=3). Tests BOTH distinct-D and degenerate-D ansatze!
    """
    if topology == "C_4_m2":
        N = 4; blocks = [[[0, 1], [2, 3]], [[1, 2], [3, 0]]]
    elif topology == "Overlap3x3_N4_m2":
        N = 4; blocks = [[[0, 1, 2], [3]], [[1, 2, 3], [0]]]
    elif topology == "C_3_m3":
        N = 3; blocks = [[[0, 1], [2]], [[1, 2], [0]], [[2, 0], [1]]]
    elif topology == "K_4_m3":
        N = 4; blocks = [[[0, 1], [2, 3]], [[1, 2], [3, 0]], [[0, 2], [1, 3]]]
    elif topology == "Cay_S3_m3":
        N = 6; blocks = [[[0, 1], [2, 3], [4, 5]], [[1, 2], [3, 4], [5, 0]], [[0, 3], [1, 4], [2, 5]]]
    else:
        raise ValueError(topology)

    Lam1, _ = scalar_1x1(kappa, m)
    tri_layout = []
    off = N
    for j in range(m):
        for B in blocks[j]:
            b = len(B)
            for a_i in range(b):
                for b_i in range(a_i, b):
                    tri_layout.append((j, B[a_i], B[b_i], off))
                    off += 1
    n_vars = off
    n_res = len(tri_layout) + N * (N + 1) // 2

    def unpack(x):
        Lam = x[0]
        d = np.concatenate([[1.0], np.exp(np.clip(x[1:N], -14.0, 4.0))])
        Xs = [np.zeros((N, N)) for _ in range(m)]
        for (j, u, v, idx) in tri_layout:
            Xs[j][u, v] = Xs[j][v, u] = x[idx]
        return Lam, d, Xs

    def residuals(x):
        Lam, d, Xs = unpack(x)
        if Lam <= 2.0 ** (2.0 * kappa - 1.0) * 1.00001 or Lam > 1e4:
            return np.full(n_res, 1e3)
        sd = np.sqrt(d); D = np.diag(d)
        res_list = []
        E_sum = np.zeros((N, N))
        for j in range(m):
            Hj = (sd[:, None] * Xs[j]) * sd[None, :]
            Gj = (sd[:, None] * Hj) * sd[None, :]
            Mp = herm_pow(D + Hj, 2.0 * kappa - 1.0, tol=1e-18)
            Gkm1 = herm_pow(Gj, kappa - 1.0, tol=1e-18)
            Gk = herm_pow(Gj, kappa, tol=1e-18)
            if Mp is None or Gkm1 is None or Gk is None:
                return np.full(n_res, 1e3)
            R1 = Mp - Lam * ((sd[:, None] * Gkm1) * sd[None, :])
            w1 = 1.0 / np.outer(d ** (kappa - 0.5), d ** (kappa - 0.5))
            for B in blocks[j]:
                b = len(B)
                for a_i in range(b):
                    for b_i in range(a_i, b):
                        res_list.append(R1[B[a_i], B[b_i]] * w1[B[a_i], B[b_i]])
            E_sum += Gk - (d[:, None] * Gkm1) * d[None, :]
        w2 = 1.0 / np.outer(d ** kappa, d ** kappa)
        triu = np.triu_indices(N)
        res_list.extend((E_sum * w2)[triu])
        return np.array(res_list)

    xm, xp, _, _ = roots_kappa(Lam1 * 1.0005, kappa)
    found_solutions = []
    for trial in range(18):
        x0 = np.zeros(n_vars)
        x0[0] = Lam1 * (1.0 + rng.uniform(1e-5, 2e-3))
        if trial < 6:
            # 2-level degenerate D (e.g. bipartite [1, d, 1, d] or [1, d, d]!)
            d_lv = rng.uniform(-3.0, -0.3)
            x0[1:N] = [0.0 if (i % 2 == 1 and N % 2 == 0) else d_lv for i in range(N - 1)]
            x0[1:N] += rng.uniform(-0.02, 0.02, size=N - 1)
        elif trial < 12:
            x0[1:N] = -np.arange(1, N) * rng.uniform(0.6, 2.0)
        else:
            x0[1:N] = rng.uniform(-2.5, 0.2, size=N - 1)
        for (j, u, v, idx) in tri_layout:
            if u == v:
                x0[idx] = rng.uniform(0.6 * xm, 1.05 * xp)
            else:
                x0[idx] = rng.uniform(-0.5, 0.5) * np.sqrt(xm * xp)
        sol = least_squares(residuals, x0, xtol=1e-14, ftol=1e-14, gtol=1e-14, max_nfev=2500)
        err = float(np.linalg.norm(sol.fun))
        if err > 1e-9:
            continue
        Lam, d, Xs = unpack(sol.x)
        if not all(np.min(np.linalg.eigvalsh(Xj)) > 1e-10 for Xj in Xs):
            continue
        C_val = (Lam / (2.0 ** (2.0 * kappa - 1.0))) ** (1.0 / (2.0 * kappa))
        sd = np.sqrt(d)
        S_ka = []
        for j in range(m):
            Hj = (sd[:, None] * Xs[j]) * sd[None, :]
            Gj = (sd[:, None] * Hj) * sd[None, :]
            S_ka.append(herm_pow(Gj, kappa - 1.0, tol=0.0))
        R_ka, K_ka = ka_eval_only(S_ka, p_val)
        if abs(R_ka - C_val) > 1e-7:
            continue
        anat = inspect_D_eigenbasis_anatomy(S_ka, K_ka, p_val, kappa, tol_edge=1e-3)
        found_solutions.append((C_val, err, anat["beta1"], anat["off_E_max"], anat["d"], S_ka))
    if not found_solutions:
        return None
    # Prefer genuinely loopy (beta1 > 0) highest C, and also track overall highest C
    found_solutions.sort(key=lambda t: t[0], reverse=True)
    loopy_sols = [s for s in found_solutions if s[2] > 0]
    return found_solutions[0], (loopy_sols[0] if loopy_sols else None)


# =============================================================================
# PART 6: TREE SEEDS & COMPLETE STAGE 2 DRIVER
# =============================================================================

def build_m2_tree_star_r3_N4(kappa, rg_sols):
    Lam, _, d3, X3, _ = rg_sols[3]
    _, _, d2, X2, _ = rg_sols[2]
    xm, xp, _, _ = roots_kappa(Lam, kappa)
    sd3 = np.sqrt(d3); G3km1 = herm_pow((sd3[:, None] * ((sd3[:, None] * X3) * sd3[None, :])) * sd3[None, :], kappa - 1.0, tol=0.0)
    sd2 = np.sqrt(d2); G2km1 = herm_pow((sd2[:, None] * ((sd2[:, None] * X2) * sd2[None, :])) * sd2[None, :], kappa - 1.0, tol=0.0)
    S1 = np.zeros((4, 4)); S2 = np.zeros((4, 4))
    S2[:3, :3] = G3km1
    S1[0, 0] = xp ** (kappa - 1.0)
    S1[np.ix_([1, 3], [1, 3])] = (d3[1] ** (2.0 * kappa - 2.0)) * G2km1
    S1[2, 2] = (xm ** (kappa - 1.0)) * (d3[2] ** (2.0 * kappa - 2.0))
    S2[3, 3] = (xm ** (kappa - 1.0)) * ((d3[1] * d2[1]) ** (2.0 * kappa - 2.0))
    bpart = [[[0], [1, 3], [2]], [[0, 1, 2], [3]]]
    return [S1, S2], bpart


def build_m2_tree_star_r3_N5(kappa, rg_sols):
    Lam, _, d3, X3, _ = rg_sols[3]
    _, _, d2, X2, _ = rg_sols[2]
    xm, xp, _, _ = roots_kappa(Lam, kappa)
    sd3 = np.sqrt(d3); G3km1 = herm_pow((sd3[:, None] * ((sd3[:, None] * X3) * sd3[None, :])) * sd3[None, :], kappa - 1.0, tol=0.0)
    sd2 = np.sqrt(d2); G2km1 = herm_pow((sd2[:, None] * ((sd2[:, None] * X2) * sd2[None, :])) * sd2[None, :], kappa - 1.0, tol=0.0)
    S1 = np.zeros((5, 5)); S2 = np.zeros((5, 5))
    S2[:3, :3] = G3km1
    S1[0, 0] = xp ** (kappa - 1.0)
    S1[np.ix_([1, 3], [1, 3])] = (d3[1] ** (2.0 * kappa - 2.0)) * G2km1
    S1[np.ix_([2, 4], [2, 4])] = (d3[2] ** (2.0 * kappa - 2.0)) * G2km1
    S2[3, 3] = (xm ** (kappa - 1.0)) * ((d3[1] * d2[1]) ** (2.0 * kappa - 2.0))
    S2[4, 4] = (xm ** (kappa - 1.0)) * ((d3[2] * d2[1]) ** (2.0 * kappa - 2.0))
    bpart = [[[0], [1, 3], [2, 4]], [[0, 1, 2], [3], [4]]]
    return [S1, S2], bpart


def build_m3_star_N3(kappa, rg_sols_m3):
    """Exact RG-seeded symmetric star for m=3, N=3: S1 diag, S2=[0,1], S3=[0,2]. Closing (1,2) in S1 makes C_3!"""
    Lam, _, d2, X2, _ = rg_sols_m3[2]
    xm, xp, _, _ = roots_kappa(Lam, kappa)
    sd2 = np.sqrt(d2); G2km1 = herm_pow((sd2[:, None] * ((sd2[:, None] * X2) * sd2[None, :])) * sd2[None, :], kappa - 1.0, tol=0.0)
    S1 = np.diag([xp ** (kappa - 1.0), (xm ** (kappa - 1.0)) * (d2[1] ** (2.0 * kappa - 2.0)),
                  (xm ** (kappa - 1.0)) * (d2[1] ** (2.0 * kappa - 2.0))])
    S2 = np.zeros((3, 3)); S2[np.ix_([0, 1], [0, 1])] = G2km1; S2[2, 2] = (xp ** (kappa - 1.0)) * (d2[1] ** (2.0 * kappa - 2.0))
    S3 = np.zeros((3, 3)); S3[np.ix_([0, 2], [0, 2])] = G2km1; S3[1, 1] = (xp ** (kappa - 1.0)) * (d2[1] ** (2.0 * kappa - 2.0))
    bpart = [[[0], [1], [2]], [[0, 1], [2]], [[0, 2], [1]]]
    return [S1, S2, S3], bpart


def build_m2_path_N4(kappa, rg_sols):
    Lam, _, d2, X2, _ = rg_sols[2]
    xm, xp, _, _ = roots_kappa(Lam, kappa)
    sd2 = np.sqrt(d2); G2km1 = herm_pow((sd2[:, None] * ((sd2[:, None] * X2) * sd2[None, :])) * sd2[None, :], kappa - 1.0, tol=0.0)
    d_n = [d2[1] ** k for k in range(4)]
    S1 = np.zeros((4, 4)); S2 = np.zeros((4, 4))
    S1[0, 0] = xp ** (kappa - 1.0)
    S1[1:3, 1:3] = (d_n[1] ** (2.0 * kappa - 2.0)) * G2km1
    S1[3, 3] = (xm ** (kappa - 1.0)) * (d_n[3] ** (2.0 * kappa - 2.0))
    S2[0:2, 0:2] = G2km1
    S2[2:4, 2:4] = (d_n[2] ** (2.0 * kappa - 2.0)) * G2km1
    bpart = [[[0], [1, 2], [3]], [[0, 1], [2, 3]]]
    return [S1, S2], bpart


def graph_block_partitions():
    graphs = []
    for k in [2, 3, 4, 6]:
        N = 2 * k
        b1 = [[2 * i, 2 * i + 1] for i in range(k)]
        b2 = [[(2 * i + 1) % N, (2 * i + 2) % N] for i in range(k)]
        graphs.append((f"C_{N}", 2, N, [b1, b2]))
    graphs.append(("Overlap3x3_N4", 2, 4, [[[0, 1, 2], [3]], [[1, 2, 3], [0]]]))
    graphs.append(("Overlap3x3_N6", 2, 6, [[[0, 1, 2], [3, 4, 5]], [[1, 2, 3], [4, 5, 0]]]))
    graphs.append(("Hypercube_Q3", 2, 8, [[[0, 1, 2, 3], [4, 5, 6, 7]], [[0, 2, 4, 6], [1, 3, 5, 7]]]))
    graphs.append(("C_3", 3, 3, [[[0, 1], [2]], [[1, 2], [0]], [[2, 0], [1]]]))
    graphs.append(("K_4", 3, 4, [[[0, 1], [2, 3]], [[1, 2], [3, 0]], [[0, 2], [1, 3]]]))
    graphs.append(("C_5", 3, 5, [[[0, 1], [2, 3], [4]], [[1, 2], [3, 4], [0]], [[4, 0], [1], [2], [3]]]))
    graphs.append(("Cay_S3_K33", 3, 6, [[[0, 1], [2, 3], [4, 5]], [[1, 2], [3, 4], [5, 0]], [[0, 3], [1, 4], [2, 5]]]))
    graphs.append(("Cay_D4", 3, 8, [[[0, 4], [1, 7], [2, 6], [3, 5]], [[0, 5], [1, 4], [2, 7], [3, 6]], [[0, 2], [1, 3], [4, 6], [5, 7]]]))
    graphs.append(("Cay_Q8", 3, 8, [[[0, 1, 2, 3], [4, 5, 6, 7]], [[0, 1, 4, 5], [2, 3, 6, 7]], [[0, 1, 6, 7], [2, 3, 4, 5]]]))
    a4_elems = [
        (0, 1, 2, 3), (1, 0, 3, 2), (2, 3, 0, 1), (3, 2, 1, 0),
        (1, 2, 0, 3), (2, 0, 1, 3), (0, 2, 3, 1), (0, 3, 1, 2),
        (1, 3, 2, 0), (3, 0, 2, 1), (2, 1, 3, 0), (3, 1, 0, 2),
    ]
    idx_a4 = {p: i for i, p in enumerate(a4_elems)}
    def orbs(gen):
        seen, res = set(), []
        for i, el in enumerate(a4_elems):
            if i in seen: continue
            o, cur = [], el
            while idx_a4[cur] not in seen:
                j = idx_a4[cur]; seen.add(j); o.append(j)
                cur = tuple(cur[gen[t]] for t in range(4))
            res.append(sorted(o))
        return res
    a4_b1 = orbs((1, 0, 3, 2)); a4_b2 = orbs((1, 2, 0, 3)); a4_b3 = orbs((0, 2, 3, 1)); a4_b4 = orbs((2, 3, 0, 1))
    graphs.append(("Cay_A4_m3", 3, 12, [a4_b1, a4_b2, a4_b3]))
    pet_c1 = [[0, 1], [2, 3], [4, 9], [5, 7], [6, 8]]
    pet_c2 = [[1, 2], [3, 4], [0, 5], [6, 9], [7], [8]]
    pet_c3 = [[4, 0], [1, 6], [2, 7], [3, 8], [5], [9]]
    pet_c4 = [[5, 8], [7, 9], [0], [1], [2], [3], [4], [6]]
    graphs.append(("Petersen_m3", 3, 10, [[[0, 1, 2, 3, 4], [5, 6, 7, 8, 9]], [[0, 5], [1, 6], [2, 7], [3, 8], [4, 9]], pet_c1]))
    graphs.append(("Petersen_m4", 4, 10, [pet_c1, pet_c2, pet_c3, pet_c4]))
    graphs.append(("Cay_A4_m4", 4, 12, [a4_b1, a4_b4, a4_b2, a4_b3]))
    graphs.append(("K5_m4", 4, 5, [[[0, 1], [2, 3], [4]], [[1, 2], [3, 4], [0]], [[2, 4], [0, 3], [1]], [[0, 4], [1, 3], [2]]]))
    graphs.append(("K4_m4_ov", 4, 4, [[[0, 1], [2, 3]], [[1, 2], [3, 0]], [[0, 2], [1, 3]], [[0, 1, 2], [3]]]))
    return graphs


def main():
    t0 = time.time()
    rng = np.random.default_rng(20261128)

    # =========================================================================
    # SECTION 0: COMPLETE RG BENCHMARKS (ALL 15 (p,m) PAIRS INCLUDING p=5/3!)
    # =========================================================================
    print("=" * 96)
    print("SECTION 0: COMPLETE HIGH-RANK RG BENCHMARKS C_{1x1} & C_{RG}(r) ACROSS ALL (p, m)")
    print("=" * 96)
    rg_table = {}
    for p_name, p_frac, p_val, kap in P_LIST:
        for m in [2, 3, 4]:
            sols = solve_rg_cascade(kap, m, r_max=7)
            r_hi = max(sols.keys())
            Lam1, C1 = sols[1][0], sols[1][1]
            Lam_hi, C_hi, d_hi, _, err_hi = sols[r_hi]
            rho = (m - 1.0) * float(np.sum(d_hi[1:] ** (2.0 * kap)))
            rg_table[(p_name, m)] = (sols, C_hi, Lam_hi)
            print(f"  p={p_name:3s} m={m}: C_1x1={C1:.13f} | C_RG(r={r_hi})={C_hi:.13f} | dC(r=2->hi)={C_hi-sols[2][1]:+.3e} | rho={rho:.5f} | res={err_hi:.1e}")

    # =========================================================================
    # SECTION 1 (ATTACK 2A): 50-DIGIT MPMATH EXACT LOOP-CLOSURE DERIVATIVES!
    # =========================================================================
    print("\n" + "=" * 96)
    print("SECTION 1 (ATTACK 2A): 50-DIGIT MPMATH POLISHED TREES & EXACT LOOP-CLOSURE DERIVATIVES")
    print("  Testing EVERY missing loop edge at theta in {0 (Re+), pi/4, pi/2 (Im), 3pi/4, pi (Re-)}")
    print("=" * 96)

    for p_name, p_frac, p_val, kap in P_LIST:
        sols2, C_rg2, _ = rg_table[(p_name, 2)]
        sols3, C_rg3, _ = rg_table[(p_name, 3)]

        # --- (A) m=2, N=4 global-optimal tree star_r3 ---
        seed4, bpart4 = build_m2_tree_star_r3_N4(kap, sols2)
        R4_f, S4_f, _, _ = optimize_ka_blocks(4, bpart4, p_val, init_blocks=seed4, rng=rng, maxiter=5000)
        Lam4_mp, C4_mp, S4_mp, res4 = mp_polish_finite_tree_holden(S4_f, bpart4, p_frac, dps=50)
        S4_np = [np.array([[float(mp.re(M[i, j])) for j in range(4)] for i in range(4)]) for M in S4_mp]
        h4 = full_nongauge_hessian(S4_np, bpart4, p_val)
        print(f"\n  [m=2, N=4 star_r3, p={p_name}] 50-dps polish: C={mp.nstr(C4_mp, 18)} (res={mp.nstr(res4, 2)}, vs RG={float(C4_mp)-C_rg2:+.3e})")
        print(f"    Full non-gauge Hessian: maxEig(Re)={h4['max_eig_r']:+.3e} (nPos={h4['n_pos_r']}) | maxEig(Im)={h4['max_eig_i']:+.3e} (nPos={h4['n_pos_i']})")
        print(f"    Tree grad={h4['g_tr']:.2e}, Off-tree (loop) grad={h4['g_lp']:.2e}")
        print(f"    {'Edge':12s} {'Type':18s} | {'R\"_bare(0)':>12s} {'R\"_eff(0)':>12s} | {'R\"_bare(pi/2)':>13s} {'R\"_eff(pi/2)':>12s} | {'R\"\'(0)':>11s} {'dR(+0.01)':>11s} {'dR(-0.01)':>11s} {'theta-law err':>13s}")
        edge_types_4 = {
            (0, (0, 1)): "par-2cyc(0-1)", (0, (0, 2)): "par-2cyc(0-2)",
            (0, (0, 3)): "leaf-root C4",  (0, (1, 2)): "sib-sib 2cyc",
            (0, (2, 3)): "sib-leaf C4",   (1, (0, 3)): "rank-inc/C4",
            (1, (1, 3)): "par-2cyc(1-3)", (1, (2, 3)): "sib-leaf 2cyc",
        }
        eff_map_4 = {(j, e): (br, er, bi, ei) for (j, e, br, er, bi, ei) in h4["edges"]}
        for (j, (u, v)), etype in edge_types_4.items():
            # Compute exact 50-dps mpmath derivatives on ALL key loop types (and full set for p=3/2, 6/5, 5/4)
            if p_name in ("3/2", "6/5", "5/4") or etype in ("leaf-root C4", "sib-leaf C4", "sib-sib 2cyc", "rank-inc/C4"):
                _, dout = mp_loop_closure_derivatives(S4_mp, j, u, v, p_frac, dps=45)
                d1_0, d2_0, d3_0, dr_p = dout["0 (Re+)"]
                _, d2_45, _, _ = dout["pi/4"]
                _, d2_90, _, _ = dout["pi/2 (Im)"]
                _, _, _, dr_m = dout["pi (Re-)"]
                assert abs(d1_0) < mp.mpf("1e-30"), f"Nonzero R'(0)={d1_0} at exact Holden tree!"
                th_err = abs(d2_45 - mp.mpf("0.5") * (d2_0 + d2_90))
                br, er, bi, ei = eff_map_4[(j, (u, v))]
                if abs(float(d2_0)) > 1e-8:
                    assert abs(br - float(d2_0)) / abs(float(d2_0)) < 5e-3, f"Hessian vs mpmath scale mismatch: {br} vs {float(d2_0)}"
                if abs(float(d2_90)) > 1e-8:
                    assert abs(bi - float(d2_90)) / abs(float(d2_90)) < 5e-3, f"Imag Hessian vs mpmath scale mismatch: {bi} vs {float(d2_90)}"
                print(
                    f"    S{j+1}({u},{v})     {etype:18s} | {float(d2_0):+12.4e} {er:+12.4e} | "
                    f"{float(d2_90):+13.4e} {ei:+12.4e} | {float(d3_0):+11.3e} {float(dr_p):+11.3e} {float(dr_m):+11.3e} {float(th_err):13.2e}"
                )

        # --- (B) m=3, N=3 symmetric star (closing S1(1,2) creates the exact ODD 3-COLOR CYCLE C_3!) ---
        seed3, bpart3 = build_m3_star_N3(kap, sols3)
        R3_f, S3_f, _, _ = optimize_ka_blocks(3, bpart3, p_val, init_blocks=seed3, rng=rng, maxiter=5000)
        Lam3_mp, C3_mp, S3_mp, res3 = mp_polish_finite_tree_holden(S3_f, bpart3, p_frac, dps=50)
        S3_np = [np.array([[float(mp.re(M[i, j])) for j in range(3)] for i in range(3)]) for M in S3_mp]
        h3 = full_nongauge_hessian(S3_np, bpart3, p_val)
        _, dout_c3 = mp_loop_closure_derivatives(S3_mp, 0, 1, 2, p_frac, dps=45)
        d1_c3, d2_0_c3, d3_0_c3, drp_c3 = dout_c3["0 (Re+)"]
        _, d2_45_c3, _, _ = dout_c3["pi/4"]
        _, d2_90_c3, _, _ = dout_c3["pi/2 (Im)"]
        _, _, _, drm_c3 = dout_c3["pi (Re-)"]
        eff_c3 = [row for row in h3["edges"] if row[0] == 0 and row[1] == (1, 2)][0]
        assert abs(eff_c3[2] - float(d2_0_c3)) / abs(float(d2_0_c3)) < 1e-3, f"C3 Hessian vs mpmath mismatch: {eff_c3[2]} vs {float(d2_0_c3)}"
        assert abs(eff_c3[4] - float(d2_90_c3)) / abs(float(d2_90_c3)) < 1e-3, f"C3 imag Hessian vs mpmath mismatch: {eff_c3[4]} vs {float(d2_90_c3)}"
        # 50-dps verification of Theorem B: g_K = m * Lam^{1-p} * (K N_KA + N_KA K)
        mp.mp.dps = 50
        p_mp = mp.mpf(p_frac[0]) / mp.mpf(p_frac[1])
        s_mp = p_mp / (2 - p_mp)
        N_ka_mp = (S3_mp[0] + S3_mp[1] + S3_mp[2]) / 3
        M_ka_mp = (mp_herm_pow(S3_mp[0], s_mp, 50) + mp_herm_pow(S3_mp[1], s_mp, 50) + mp_herm_pow(S3_mp[2], s_mp, 50)) / 3
        Nh_mp = mp_herm_pow(N_ka_mp, mp.mpf("0.5"), 50); Nmh_mp = mp_herm_pow(N_ka_mp, mp.mpf("-0.5"), 50)
        K_mp = Nmh_mp * mp_herm_pow(Nh_mp * M_ka_mp * Nh_mp, mp.mpf("0.5"), 50) * Nmh_mp
        Kh_mp = mp_herm_pow(K_mp, mp.mpf("0.5"), 50); Kmh_mp = mp_herm_pow(K_mp, mp.mpf("-0.5"), 50)
        gK_mp = mp.zeros(3, 3)
        for S_m in S3_mp:
            gK_mp += Kmh_mp * mp_herm_pow(Kh_mp * S_m * Kh_mp, p_mp, 50) * Kmh_mp
        thmB_rhs = 3 * (Lam3_mp ** (1 - p_mp)) * (K_mp * N_ka_mp + N_ka_mp * K_mp)
        thmB_err = mp.norm(gK_mp - thmB_rhs) / mp.norm(gK_mp)
        assert thmB_err < mp.mpf("1e-40"), f"Theorem B identity failed: err={thmB_err}"
        print(f"\n  [m=3, N=3 sym-star -> ODD C_3 CLOSURE S1(1,2), p={p_name}] 50-dps: C={mp.nstr(C3_mp, 18)} (res={mp.nstr(res3, 2)}, ThmB_err={mp.nstr(thmB_err, 2)}, vs RG={float(C3_mp)-C_rg3:+.3e})")
        print(f"    Full non-gauge Hessian: maxEig(Re)={h3['max_eig_r']:+.3e} (nPos={h3['n_pos_r']}) | maxEig(Im)={h3['max_eig_i']:+.3e} (nPos={h3['n_pos_i']})")
        print(
            f"    C_3 closure S1(1,2): R'(0)={float(d1_c3):+.2e} | R\"_bare(0)={float(d2_0_c3):+.5e} R\"_eff(0)={eff_c3[3]:+.5e} | "
            f"R\"_bare(pi/2)={float(d2_90_c3):+.5e} R\"_eff(pi/2)={eff_c3[5]:+.5e} | R\"\'(0)={float(d3_0_c3):+.4e} | "
            f"dR(+0.01)={float(drp_c3):+.4e} dR(-0.01)={float(drm_c3):+.4e}"
        )

        # --- (C) m=2, N=5 branching RG truncation (two leaves 3,4: PURE leaf-to-leaf 6-cycle S2(3,4)!) ---
        if p_name in ("6/5", "5/4", "4/3", "3/2"):
            seed5, bpart5 = build_m2_tree_star_r3_N5(kap, sols2)
            R5_f, S5_f, _, _ = optimize_ka_blocks(5, bpart5, p_val, init_blocks=seed5, rng=rng, maxiter=5000)
            Lam5_mp, C5_mp, S5_mp, res5 = mp_polish_finite_tree_holden(S5_f, bpart5, p_frac, dps=45)
            S5_np = [np.array([[float(mp.re(M[i, j])) for j in range(5)] for i in range(5)]) for M in S5_mp]
            h5 = full_nongauge_hessian(S5_np, bpart5, p_val)
            print(f"\n  [m=2, N=5 star_r3 (2 leaves), p={p_name}] 45-dps: C={mp.nstr(C5_mp, 18)} (res={mp.nstr(res5, 2)})")
            print(f"    Full non-gauge Hessian: maxEig(Re)={h5['max_eig_r']:+.3e} (nPos={h5['n_pos_r']}) | maxEig(Im)={h5['max_eig_i']:+.3e} (nPos={h5['n_pos_i']})")
            # Check which edge(s) are positive vs negative!
            eff_map_5 = {(j, e): (br, er, bi, ei) for (j, e, br, er, bi, ei) in h5["edges"]}
            for (j, (u, v)), etype in [
                ((1, (3, 4)), "leaf-leaf C6!"),
                ((0, (1, 2)), "sib-sib 2cyc"),
                ((0, (0, 3)), "leaf-root C4"),
                ((0, (3, 4)), "leaf-leaf S1"),
                ((1, (0, 3)), "rank-inc(0-3)"),
                ((1, (0, 4)), "rank-inc(0-4)"),
            ]:
                br, er, bi, ei = eff_map_5[(j, (u, v))]
                _, dout5 = mp_loop_closure_derivatives(S5_mp, j, u, v, p_frac, dps=40)
                d1_5, d2_0_5, d3_0_5, drp_5 = dout5["0 (Re+)"]
                _, d2_90_5, _, _ = dout5["pi/2 (Im)"]
                _, _, _, drm_5 = dout5["pi (Re-)"]
                print(
                    f"    S{j+1}({u},{v}) {etype:15s}: R\"_bare(0)={float(d2_0_5):+.4e} R\"_eff(0)={er:+.4e} | "
                    f"R\"_bare(pi/2)={float(d2_90_5):+.4e} R\"_eff(pi/2)={ei:+.4e} | R\"\'(0)={float(d3_0_5):+.3e} | dR(+-0.01)=({float(drp_5):+.3e},{float(drm_5):+.3e})"
                )

    # =========================================================================
    # SECTION 1B (ATTACK 2B): RAW DEPTH-L RG TREE TRUNCATION LOOP PERTURBATION
    # =========================================================================
    print("\n" + "=" * 96)
    print("SECTION 1B (ATTACK 2B): RAW DEPTH-L RG TREE TRUNCATION LOOP-CLOSURE PERTURBATION (45-dps mpmath)")
    print("  Directly on unrelaxed r=3 depth-2 RG tree (N=5) & r=2 depth-3 RG path (N=4) at p=6/5, 5/4, 3/2")
    print("=" * 96)
    for p_name, p_frac, p_val, kap in [("6/5", (6, 5), 1.2, 3.0), ("5/4", (5, 4), 1.25, 2.5), ("3/2", (3, 2), 1.5, 1.5)]:
        sols2, C_rg2, _ = rg_table[(p_name, 2)]
        S5_raw, _ = build_m2_tree_star_r3_N5(kap, sols2)
        S5_raw_mp = [mp.matrix([[mp.mpf(repr(float(M[i, j]))) for j in range(5)] for i in range(5)]) for M in S5_raw]
        R0_raw = mp_eval_kubo_ando_mp(S5_raw_mp, p_frac, dps=45)
        print(f"  [Raw RG r=3 depth-2 N=5, p={p_name}] R0={mp.nstr(R0_raw, 16)} (vs RG_inf={float(R0_raw)-C_rg2:+.3e})")
        for (j, (u, v), etype) in [(1, (3, 4), "leaf-leaf C6"), (0, (1, 2), "sib-sib 2cyc"), (0, (0, 3), "leaf-root C4")]:
            _, do = mp_loop_closure_derivatives(S5_raw_mp, j, u, v, p_frac, dps=42)
            d1_0, d2_0, d3_0, drp = do["0 (Re+)"]
            _, d2_90, _, _ = do["pi/2 (Im)"]
            _, _, _, drm = do["pi (Re-)"]
            print(
                f"    S{j+1}({u},{v}) {etype:13s}: R'(0)={float(d1_0):+.2e} | R\"(0)={float(d2_0):+.4e} | "
                f"R\"(pi/2)={float(d2_90):+.4e} | dR(+-0.01)=({float(drp):+.3e},{float(drm):+.3e})"
            )
        S4_path, _ = build_m2_path_N4(kap, sols2)
        S4_path_mp = [mp.matrix([[mp.mpf(repr(float(M[i, j]))) for j in range(4)] for i in range(4)]) for M in S4_path]
        R0_p4 = mp_eval_kubo_ando_mp(S4_path_mp, p_frac, dps=45)
        _, do4 = mp_loop_closure_derivatives(S4_path_mp, 0, 0, 3, p_frac, dps=42)
        d1_4, d2_4, _, drp4 = do4["0 (Re+)"]
        _, d2_4_90, _, _ = do4["pi/2 (Im)"]
        _, _, _, drm4 = do4["pi (Re-)"]
        print(
            f"  [Raw RG r=2 depth-3 path P4->C4, p={p_name}] R0={mp.nstr(R0_p4, 16)} | "
            f"S1(0,3) C4 closure: R'(0)={float(d1_4):+.2e} | R\"(0)={float(d2_4):+.4e} R\"(pi/2)={float(d2_4_90):+.4e} | dR(+-0.01)=({float(drp4):+.3e},{float(drm4):+.3e})"
        )

    # =========================================================================
    # SECTION 2 (ATTACK 1A): GRAPH/CAYLEY/PETERSEN SWEEP + D-EIGENBASIS ANATOMY!
    # =========================================================================
    print("\n" + "=" * 96)
    print("SECTION 2 (ATTACK 1A): CYCLES, CAYLEY GRAPHS (S_3,D_4,Q_8,A_4), PETERSEN + D-EIGENBASIS ANATOMY")
    print("=" * 96)
    graphs = graph_block_partitions()
    top_candidates = []  # store (p_name, p_frac, m, label, R, C_rg, S_list)
    for p_name, p_frac, p_val, kap in P_LIST:
        sub_g = [g for g in graphs if g[0] in ("C_4", "C_6", "C_3", "K_4", "Petersen_m4")] if p_name == "4/3" else graphs
        for gname, m, N, bpart in sub_g:
            _, C_rg, _ = rg_table[(p_name, m)]
            best_re = 0.0; best_cp = 0.0; best_S = None; best_K = None
            n_starts = 6 if N <= 8 else 4
            for cplx in [False, True]:
                for _ in range(n_starts):
                    Rg, Sg, Kg, _ = optimize_ka_blocks(N, bpart, p_val, complex_mode=cplx, rng=rng, maxiter=2200)
                    if not cplx and Rg > best_re:
                        best_re = Rg
                        if best_re >= best_cp: best_S, best_K = Sg, Kg
                    if cplx and Rg > best_cp:
                        best_cp = Rg
                        if best_cp > best_re: best_S, best_K = Sg, Kg
            best_all = max(best_re, best_cp)
            anat = inspect_D_eigenbasis_anatomy(best_S, best_K, p_val, kap, tol_edge=1e-3)
            diff = best_all - C_rg
            flag = " *** BEATS RG_INF!! ***" if diff > 1e-12 else ""
            if gname in ("C_4", "C_6", "Hypercube_Q3", "C_3", "K_4", "Cay_Q8", "Petersen_m3", "Petersen_m4", "Cay_A4_m4") and p_name != "4/3":
                top_candidates.append((p_name, p_frac, m, gname, best_all, C_rg, best_S))
            print(
                f"  p={p_name:3s} m={m} {gname:14s} (N={N:2d}): Re={best_re:.12f} Cplx={best_cp:.12f} | "
                f"vs RG={diff:+.3e} | D-basis: beta1={anat['beta1']} ovlp={anat['max_overlap']:.1e} offE={anat['off_E_max']:.1e}{flag}"
            )

    # =========================================================================
    # SECTION 2B: PERTURBED Z/2NZ TOTAL-VANISHING RINGS (2N = 4..32, dim 8..64)
    # =========================================================================
    print("\n" + "=" * 96)
    print("SECTION 2B (ATTACK 1A-RING): PERTURBED Z/2NZ TOTAL-VANISHING RINGS (m=2, 2N=4..32 -> dim 8..64)")
    print("=" * 96)
    for p_name, p_frac, p_val, kap in [("6/5", (6, 5), 1.2, 3.0), ("5/4", (5, 4), 1.25, 2.5),
                                       ("3/2", (3, 2), 1.5, 1.5), ("5/3", (5, 3), 5.0 / 3.0, 1.25)]:
        sols2, C_rg2, _ = rg_table[(p_name, 2)]
        _, _, d2, X2, _ = sols2[2]
        sd2 = np.sqrt(d2); G2km1 = herm_pow((sd2[:, None] * ((sd2[:, None] * X2) * sd2[None, :])) * sd2[None, :], kap - 1.0, tol=0.0)
        for twoN in [4, 6, 8, 12, 16, 24, 32]:
            k_blk = twoN // 2
            b1 = [[2 * i, 2 * i + 1] for i in range(k_blk)]
            b2 = [[(2 * i + 1) % twoN, (2 * i + 2) % twoN] for i in range(k_blk)]
            best_r = 0.0; best_tag = ""; best_S_r = None; best_K_r = None
            for mode in ["uniform_pert_real", "rg_soliton_real", "rg_soliton_cplx", "quasiperiodic_real"]:
                cplx = ("cplx" in mode)
                dtype = np.complex128 if cplx else np.float64
                S1 = np.zeros((twoN, twoN), dtype=dtype); S2 = np.zeros((twoN, twoN), dtype=dtype)
                if mode == "uniform_pert_real":
                    for i in range(k_blk):
                        sc1 = (1.0 + 0.15 * np.sin(2.0 * np.pi * i / k_blk)) ** (2.0 * kap - 2.0)
                        S1[2 * i:2 * i + 2, 2 * i:2 * i + 2] = sc1 * G2km1
                        idx2 = [(2 * i + 1) % twoN, (2 * i + 2) % twoN]
                        sc2 = (1.0 + 0.15 * np.cos(2.0 * np.pi * i / k_blk)) ** (2.0 * kap - 2.0)
                        S2[np.ix_(idx2, idx2)] = sc2 * G2km1
                elif mode in ("rg_soliton_real", "rg_soliton_cplx"):
                    dists = [min(i, twoN - i) for i in range(twoN)]
                    d_nodes = [d2[1] ** dists[i] for i in range(twoN)]
                    for blk in b1:
                        u, v = blk; sc = max(d_nodes[u], d_nodes[v]) ** (2.0 * kap - 2.0)
                        bm = sc * G2km1.copy()
                        if d_nodes[u] < d_nodes[v]: bm = bm[::-1, ::-1].copy()
                        S1[np.ix_(blk, blk)] = bm
                    for blk in b2:
                        u, v = blk; sc = max(d_nodes[u], d_nodes[v]) ** (2.0 * kap - 2.0)
                        bm = sc * G2km1.copy()
                        if d_nodes[u] < d_nodes[v]: bm = bm[::-1, ::-1].copy()
                        if cplx and u == twoN - 1 and v == 0:
                            bm = bm.astype(np.complex128); bm[0, 1] *= 1j; bm[1, 0] *= -1j
                        S2[np.ix_(blk, blk)] = bm
                else:
                    phi_g = (1.0 + np.sqrt(5.0)) / 2.0
                    d_nodes = [d2[1] ** (1.5 + 1.5 * np.cos(2.0 * np.pi * i / phi_g)) for i in range(twoN)]
                    for blk in b1:
                        u, v = blk; S1[np.ix_(blk, blk)] = ((0.5 * (d_nodes[u] + d_nodes[v])) ** (2.0 * kap - 2.0)) * G2km1
                    for blk in b2:
                        u, v = blk; S2[np.ix_(blk, blk)] = ((0.5 * (d_nodes[u] + d_nodes[v])) ** (2.0 * kap - 2.0)) * G2km1
                maxit = 1400 if twoN <= 16 else 650
                Rr, Sr, Kr, _ = optimize_ka_blocks(twoN, [b1, b2], p_val, complex_mode=cplx,
                                                   init_blocks=[S1, S2], rng=rng, maxiter=maxit)
                if Rr > best_r:
                    best_r = Rr; best_tag = mode; best_S_r = Sr; best_K_r = Kr
            diff = best_r - C_rg2
            anat_r = inspect_D_eigenbasis_anatomy(best_S_r, best_K_r, p_val, kap, tol_edge=1e-3)
            flag = " *** BEATS RG_INF!! ***" if diff > 1e-12 else ""
            if twoN in (8, 16) and p_name in ("3/2", "6/5"):
                top_candidates.append((p_name, p_frac, 2, f"Ring_Z/{twoN}Z", best_r, C_rg2, best_S_r))
            print(
                f"  Ring p={p_name:3s} Z/{twoN:2d}Z (dim={2*twoN:2d}): best={best_r:.12f} | vs RG={diff:+.3e} | "
                f"mode={best_tag:18s} | beta1={anat_r['beta1']} ovlp={anat_r['max_overlap']:.1e}{flag}"
            )

    # =========================================================================
    # SECTION 3 (ATTACK 1B): DENSE KA (HIERARCHICAL + RANDOM) & DIRECT PSD/POVM!
    # =========================================================================
    print("\n" + "=" * 96)
    print("SECTION 3 (ATTACK 1B): ADVERSARIAL DENSE KA (REAL & CPLX) + DIRECT PSD/POVM (Thm 5, SEEDED!)")
    print("=" * 96)
    for p_name, p_frac, p_val, kap in P_LIST:
        if p_name == "4/3":
            continue
        # 3A: Dense unconstrained KA (Real & Complex) with hierarchical + random starts + D-anatomy!
        for m, Ns in [(2, [3, 4, 5, 6, 8]), (3, [3, 4, 5]), (4, [3, 4])]:
            _, C_rg, _ = rg_table[(p_name, m)]
            for N in Ns:
                best_re = 0.0; best_cp = 0.0; best_S = None; best_K = None
                for cplx in [False, True]:
                    for st in range(6):
                        Rd, Sd, Kd, _ = optimize_ka_dense(N, m, p_val, complex_mode=cplx, rng=rng, maxiter=2200)
                        if not cplx and Rd > best_re:
                            best_re = Rd
                            if best_re >= best_cp: best_S, best_K = Sd, Kd
                        if cplx and Rd > best_cp:
                            best_cp = Rd
                            if best_cp > best_re: best_S, best_K = Sd, Kd
                best_all = max(best_re, best_cp)
                if best_S is None:
                    print(f"  DenseKA p={p_name:3s} m={m} N={N} (dim={m*N:2d}): no valid SPD start converged")
                    continue
                anat = inspect_D_eigenbasis_anatomy(best_S, best_K, p_val, kap, tol_edge=1e-3)
                diff = best_all - C_rg
                flag = " *** BEATS RG_INF!! ***" if diff > 1e-12 else ""
                if (m == 2 and N in (4, 8)) or (m == 3 and N == 5) or (m == 4 and N == 4):
                    top_candidates.append((p_name, p_frac, m, f"DenseKA_N{N}", best_all, C_rg, best_S))
                print(
                    f"  DenseKA p={p_name:3s} m={m} N={N} (dim={m*N:2d}): Re={best_re:.12f} Cplx={best_cp:.12f} "
                    f"(C-R={best_cp-best_re:+.2e}) | vs RG={diff:+.3e} | beta1={anat['beta1']} ovlp={anat['max_overlap']:.1e} commE={anat['max_comm_E']:.1e}{flag}"
                )

        # 3B: Properly-Seeded DIRECT PSD/POVM (Theorem 5 — Escaping Kubo-Ando / Cyclic Manifold!)
        # Seed from exact N=3,4 KA tree embedded into mN x mN PSD/POVM + strong complex non-cyclic noise,
        # PLUS hierarchical random complex/real multi-starts!
        sols2, C_rg2, _ = rg_table[(p_name, 2)]
        sols3, C_rg3, _ = rg_table[(p_name, 3)]
        for m, N_seed in [(2, 4), (3, 3)]:
            _, C_rg, _ = rg_table[(p_name, m)]
            if m == 2:
                S_tr, b_tr = build_m2_tree_star_r3_N4(kap, sols2)
            else:
                S_tr, b_tr = build_m3_star_N3(kap, sols3)
            R_tr, S_tr_opt, _, _ = optimize_ka_blocks(N_seed, b_tr, p_val, init_blocks=S_tr, rng=rng, maxiter=3000)
            Zs_emb, _ = ka_to_psd_seed(S_tr_opt, p_val)
            n_psd = m * N_seed
            ranks = [N_seed] * m
            # Verify embedding exactness!
            x_emb_c = np.concatenate([np.concatenate([np.real(Z).ravel(), np.imag(Z).ravel()]) for Z in Zs_emb])
            v_emb, _ = psd_eval_and_grad_multi(x_emb_c, n_psd, ranks, p_val, complex_mode=True)
            R_emb = float(np.exp(-v_emb))
            assert abs(R_emb - R_tr) < 1e-10, f"PSD embedding mismatch: {R_emb} vs {R_tr}"

            # Now perturb heavily off the cyclic/Kubo-Ando manifold (complex & real) and optimize freely!
            best_psd_re = 0.0; best_psd_cp = 0.0
            for cplx in [False, True]:
                n_x = sum(n_psd * r * (2 if cplx else 1) for r in ranks)
                for tr in range(5):
                    if tr < 3 and (cplx or m == 2):
                        # Perturbed tree embedding (strength 0.01, 0.05, 0.2)
                        noise_lvl = [0.01, 0.05, 0.20][tr]
                        base = x_emb_c if cplx else np.concatenate([np.real(Z).ravel() for Z in Zs_emb])
                        x0 = base + noise_lvl * np.linalg.norm(base) / np.sqrt(n_x) * rng.standard_normal(n_x)
                    else:
                        # Fresh hierarchical multi-scale random start
                        sc = (0.35 ** np.arange(n_psd))
                        parts = []
                        for r in ranks:
                            parts.append((rng.standard_normal((n_psd, r)) * sc[:, None]).ravel())
                            if cplx:
                                parts.append((rng.standard_normal((n_psd, r)) * sc[:, None]).ravel())
                        x0 = np.concatenate(parts)
                    res = minimize(psd_eval_and_grad_multi, x0, args=(n_psd, ranks, p_val, cplx),
                                   jac=True, method="L-BFGS-B", options={"maxiter": 2000, "ftol": 1e-16, "gtol": 1e-13})
                    Rp = float(np.exp(-res.fun)) if res.fun < 1e4 else 0.0
                    if not cplx and Rp > best_psd_re: best_psd_re = Rp
                    if cplx and Rp > best_psd_cp: best_psd_cp = Rp
            best_psd = max(best_psd_re, best_psd_cp)
            print(
                f"  PSD/POVM(Thm5) p={p_name:3s} m={m} n={n_psd}: TreeKA={R_tr:.12f} | "
                f"FreeRe={best_psd_re:.12f} FreeCplx={best_psd_cp:.12f} | Free-Tree={best_psd-R_tr:+.2e} | vs RG={best_psd-C_rg:+.3e}"
            )

    # =========================================================================
    # SECTION 4 (ATTACK 1C): DIRECT MULTI-BLOCK HOLDEN SOLVER ON LOOPY GRAPHS!
    # =========================================================================
    print("\n" + "=" * 96)
    print("SECTION 4 (ATTACK 1C): DIRECT MULTI-BLOCK HOLDEN SOLUTIONS (4.1)-(4.2) ON LOOPY GRAPHS")
    print("=" * 96)
    for p_name, p_frac, p_val, kap in [("6/5", (6, 5), 1.2, 3.0), ("5/4", (5, 4), 1.25, 2.5),
                                       ("3/2", (3, 2), 1.5, 1.5), ("5/3", (5, 3), 5.0 / 3.0, 1.25)]:
        for m, topo in [(2, "C_4_m2"), (2, "Overlap3x3_N4_m2"), (3, "C_3_m3"), (3, "K_4_m3"), (3, "Cay_S3_m3")]:
            _, C_rg, _ = rg_table[(p_name, m)]
            res_h = solve_direct_holden_loopy(p_val, kap, m, topo, rng)
            if res_h is None:
                print(f"  Holden p={p_name:3s} m={m} {topo:16s}: no converged SPD solution")
            else:
                best_any, best_lp = res_h
                C_a, err_a, b1_a, offE_a, d_a, _ = best_any
                lp_str = f"LOOPY(b1={best_lp[2]}) C={best_lp[0]:.12f} (vs RG {best_lp[0]-C_rg:+.3e})" if best_lp else "NO genuine loopy (beta1>0) sol found"
                print(
                    f"  Holden p={p_name:3s} m={m} {topo:16s}: best C={C_a:.12f} (vs RG {C_a-C_rg:+.3e}, res={err_a:.1e}, b1={b1_a}) | {lp_str}"
                )

    # =========================================================================
    # SECTION 5: 50-DIGIT MPMATH INDEPENDENT VERIFICATION OF TOP CANDIDATES!
    # =========================================================================
    print("\n" + "=" * 96)
    print("SECTION 5: 50-DIGIT MPMATH INDEPENDENT VERIFICATION (KUBO-ANDO + DIRECT SCHATTEN-p NORM)")
    print("=" * 96)
    any_beats_rg = False
    for idx_c, (p_name, p_frac, m, label, R_np, C_rg, S_list) in enumerate(top_candidates):
        R_mp = mp_eval_kubo_ando_from_np(S_list, p_frac, dps=50)
        diff_np_mp = abs(float(R_mp) - R_np)
        diff_rg = float(R_mp) - C_rg
        if diff_rg > 1e-12:
            any_beats_rg = True
        sch_str = ""
        # Direct Schatten-p cross-check on compact candidates (m*N <= 12) to verify zero Kubo-Ando discrepancy!
        if m * S_list[0].shape[0] <= 12 and label in ("C_4", "C_3", "K_4", "DenseKA_N4"):
            R_sch = mp_eval_direct_schatten_from_ka(S_list, p_frac, dps=50)
            sch_str = f" | |Schatten-KA|={float(abs(R_sch - R_mp)):.1e}"
            assert abs(R_sch - R_mp) < mp.mpf("1e-35"), f"Schatten vs KA mismatch: {abs(R_sch-R_mp)}"
        print(
            f"  50-dps {p_name:3s} m={m} {label:14s}: R_mp={mp.nstr(R_mp, 16)} | "
            f"|mp-np|={diff_np_mp:.1e}{sch_str} | vs C_RG={diff_rg:+.3e}"
        )

    print("\n" + "=" * 96)
    print(f"FINAL VERDICT: ANY CANDIDATE BEATING C_RG_inf (>1e-12)?  {any_beats_rg}")
    print(f"Total runtime: {time.time() - t0:.1f}s")
    print("=" * 96)


if __name__ == "__main__":
    main()
