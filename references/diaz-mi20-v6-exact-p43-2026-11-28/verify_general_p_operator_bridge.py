"""
Self-Contained Verification Suite for `general_p_operator_bridge.md` (Open Problem MI-20).
Dependencies: standard library + numpy, scipy, mpmath ONLY (zero external scratch imports).

Verifies all 5 mathematical sections with strict assertions:
  Suite 1: Uninverted Completely Positive (CP) Operator Bridge (Thm 1.1, multiplicative & affine)
           over genuinely complex Hermitian matrices (including degenerate & non-top eigenvalues).
  Suite 2: Exact p = 3/2 X-basis & Q-basis reductions (Prop 2.1, Thm 2.2, Prop 2.3), Pick kernel
           K_N(q,r) PSDness, coupled r=2 & r=3 complex-rotated RG solutions, and finite-grid Level-0
           CP-kernel SDP evaluation (explicitly labeled numerical) + Envelope-theorem delta-slope.
  Suite 3: Five-Line Purely Analytic Perfect-Square Theorem at p = 3/2 (Thm 3.1, zero D<=I).
  Suite 4: Universal Non-Asymptotic All-p, All-m Bound & Exact Large-m Law (Lem 4.1-4.2, Thm 4.3),
           verified on noncommuting RG solutions and across m up to 10^6 + exact +1/2 second term.
  Suite 5: 100-digit mpmath verification of the 10-line Super-Exponential p -> 2^- Collapse Theorem
           (Thm 5.1, Cor 5.2), exact prefactor e^{-2 eta_m}, g0/xm -> e, and exact left derivative.
"""

import numpy as np
import mpmath as mp
from scipy.optimize import brentq, root


# =============================================================================
# Helpers: Exact Scalar Roots, 1x1 Lower Bounds, and Coupled RG Fixed Points
# =============================================================================

def roots_kappa(Lam, kappa):
    """Exact roots 0 < x_- < (k-1)/k < 1 < x_+ of (1+x)^{2k-1} = Lam * x^{k-1} in log-space."""
    t_min = np.log((kappa - 1.0) / kappa)
    logL = np.log(Lam)
    fn = lambda t: (2.0 * kappa - 1.0) * np.logaddexp(0.0, t) - (kappa - 1.0) * t - logL
    assert fn(t_min) < 0.0, f"Lam={Lam} must exceed minimum of phi_kappa"
    lo, hi = t_min - 1.0, t_min + 1.0
    while fn(lo) < 0.0:
        lo -= 20.0
    while fn(hi) < 0.0:
        hi += 20.0
    xm = np.exp(brentq(fn, lo, t_min, xtol=1e-15, rtol=1e-15))
    xp = np.exp(brentq(fn, t_min, hi, xtol=1e-15, rtol=1e-15))
    sigm = (xm ** (kappa - 1.0)) * (xm - 1.0)
    sigp = (xp ** (kappa - 1.0)) * (xp - 1.0)
    return xm, xp, sigm, sigp


def scalar_1x1(kappa, m):
    """Exact 1x1 scalar extremal (Lam_1, C_1x1) solving sig_+(Lam) + (m-1)*sig_-(Lam) = 0."""
    Lam0 = 2.0 ** (2.0 * kappa - 1.0)
    hi = max(Lam0 * 2.0, 2.0 * np.sqrt(m) + 4.0)
    while roots_kappa(hi, kappa)[3] + (m - 1.0) * roots_kappa(hi, kappa)[2] < 0.0:
        hi *= 2.0
    Lam1 = brentq(
        lambda L: roots_kappa(L, kappa)[3] + (m - 1.0) * roots_kappa(L, kappa)[2],
        Lam0 + 1e-12, hi, xtol=1e-15, rtol=1e-15
    )
    C1 = (Lam1 / Lam0) ** (1.0 / (2.0 * kappa))
    return Lam1, C1


def random_unitary(n, rng):
    """Haar-like random complex unitary n x n matrix."""
    Z = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
    Q, R = np.linalg.qr(Z)
    ph = np.diag(R) / np.abs(np.diag(R))
    return Q * ph[None, :]


def solve_rg_p32_coupled(r, m=2):
    """Solve genuinely coupled rank-r RG block fixed point at p=3/2 via progressive r-lifting."""
    Lam0, _ = scalar_1x1(1.5, m)

    def unpack(z, rr):
        Lam = np.exp(z[0]) + 4.0
        ds = np.concatenate([[1.0], np.exp(z[1:rr])])
        idx = rr
        L = np.zeros((rr, rr))
        for i in range(rr):
            L[i, i] = np.exp(z[idx]); idx += 1
            for j in range(i):
                L[i, j] = z[idx]; idx += 1
        Q = L @ L.T
        return Lam, ds, Q

    def pack(Lam, ds, Q):
        rr = len(ds)
        L = np.linalg.cholesky(0.5 * (Q + Q.T))
        z = [np.log(Lam - 4.0)] + [np.log(ds[i]) for i in range(1, rr)]
        for i in range(rr):
            z.append(np.log(L[i, i]))
            for j in range(i):
                z.append(L[i, j])
        return np.array(z)

    def res(z, rr):
        Lam, ds, Q = unpack(z, rr)
        D = np.diag(ds)
        _, xp, _, sigp = roots_kappa(Lam, 1.5)
        H = Q @ D @ Q
        M = D + H
        R1 = M @ M - Lam * (D @ Q @ D)
        F = Q @ D @ Q @ D @ Q - D @ Q @ D
        out = [R1[i, j] for i in range(rr) for j in range(i, rr)]
        out.append(F[0, 0] + sigp / (m - 1.0))
        for i in range(1, rr):
            out.append(F[i, i] - sigp * (ds[i] ** 2))
        return np.array(out)

    # Start at r = 2
    z2 = np.array([np.log(Lam0 - 4.0 + 0.002), np.log(0.075), np.log(0.50), np.log(0.60), -0.20])
    sol = root(lambda z: res(z, 2), z2, method="hybr", tol=1e-14)
    Lam, ds, Q = unpack(sol.x, 2)
    assert np.linalg.norm(res(sol.x, 2)) < 1e-12

    # Progressive lift to target r with coupled off-diagonal seed
    for rr in range(3, r + 1):
        ds_new = np.concatenate([ds, [ds[-1] * 0.16]])
        Q_new = np.zeros((rr, rr))
        Q_new[:rr - 1, :rr - 1] = Q
        Q_new[rr - 1, rr - 1] = Q[rr - 2, rr - 2] + 0.25
        Q_new[rr - 2, rr - 1] = Q_new[rr - 1, rr - 2] = -0.18
        if rr >= 3:
            Q_new[0, rr - 1] = Q_new[rr - 1, 0] = 0.04
        z_init = pack(Lam, ds_new, Q_new)
        sol = root(lambda z: res(z, rr), z_init, method="hybr", tol=1e-14)
        Lam, ds, Q = unpack(sol.x, rr)
        assert np.linalg.norm(res(sol.x, rr)) < 1e-11
        # Confirm strictly coupled (all off-diagonal entries of Q in last row nonzero)
        assert np.linalg.norm(Q[-1, :-1]) > 1e-3, f"r={rr} collapsed to decoupled block!"
    return Lam, ds, Q, float(np.linalg.norm(res(sol.x, r)))


def solve_rg_general_r2(kappa, m=2):
    """Solve coupled r=2 RG fixed point for general kappa > 1 via X-parametrization."""
    Lam0, _ = scalar_1x1(kappa, m)
    Lam_floor = 2.0 ** (2.0 * kappa - 1.0)

    def unpack(z):
        Lam = np.exp(z[0]) + Lam_floor
        d1 = np.exp(z[1])
        L = np.array([[np.exp(z[2]), 0.0], [z[4], np.exp(z[3])]])
        X = L @ L.T
        Dh = np.diag([1.0, np.sqrt(d1)])
        H = Dh @ X @ Dh
        return Lam, d1, H

    def mat_pow(A, p):
        ev, V = np.linalg.eigh(0.5 * (A + A.T))
        return (V * (np.maximum(ev, 1e-30) ** p)) @ V.T

    def res(z):
        Lam, d1, H = unpack(z)
        D = np.diag([1.0, d1])
        Dh = np.diag([1.0, np.sqrt(d1)])
        G = Dh @ H @ Dh
        M = D + H
        R1 = mat_pow(M, 2.0 * kappa - 1.0) - Lam * (Dh @ mat_pow(G, kappa - 1.0) @ Dh)
        E = mat_pow(G, kappa) - D @ mat_pow(G, kappa - 1.0) @ D
        _, _, _, sigp = roots_kappa(Lam, kappa)
        return np.array([
            R1[0, 0], R1[0, 1], R1[1, 1],
            E[0, 0] + sigp / (m - 1.0),
            E[1, 1] - sigp * (d1 ** (2.0 * kappa)),
        ])

    xm, xp, _, _ = roots_kappa(Lam0, kappa)
    # In X-variables, X_00 ~ xm, X_11 ~ 0.6*xp + 0.4*xm, off-diag ~ -0.35*sqrt(xm*xp)
    z0 = np.array([
        np.log(Lam0 - Lam_floor + 0.005 * (Lam0 - Lam_floor)),
        np.log(0.08 if kappa < 1.8 else (0.25 if kappa < 2.5 else 0.45)),
        np.log(np.sqrt(max(xm * 1.15, 0.02))),
        np.log(np.sqrt(max(0.65 * xp + 0.35 * xm, 0.1))),
        -0.35 * np.sqrt(xm * xp),
    ])
    sol = root(res, z0, method="hybr", tol=1e-13)
    if np.linalg.norm(res(sol.x)) > 1e-11:
        sol = root(res, z0, method="lm", tol=1e-13)
    Lam, d1, H = unpack(sol.x)
    assert np.linalg.norm(res(sol.x)) < 1e-11, f"RG r=2 failed at kappa={kappa}: res={np.linalg.norm(res(sol.x))}"
    return Lam, d1, H


# =============================================================================
# Mehrotra HKM Primal-Dual SDP Solver (for Suite 2 numerical Level-0 eval)
# =============================================================================

def solve_dual_sdp(c_vec, F0, Fk_arr, max_iter=150, tol=1e-10):
    m_vars = len(c_vec)
    n_blk = len(F0)
    sizes = [f.shape[0] for f in F0]
    tot_dim = sum(sizes)

    y = np.zeros(m_vars)
    y[0] = 5.0
    S = [np.eye(s) for s in sizes]
    X = [np.eye(s) for s in sizes]

    def max_step(M, dM):
        ev, V = np.linalg.eigh(0.5 * (M + M.T))
        ev = np.maximum(ev, 1e-15)
        Mh = V @ np.diag(ev ** -0.5) @ V.T
        H = Mh @ (0.5 * (dM + dM.T)) @ Mh
        lam = np.linalg.eigvalsh(0.5 * (H + H.T))[0]
        return 1.0 if lam >= 0 else min(1.0, -0.95 / lam)

    p_err = d_err = gap = 1e9
    for it in range(max_iter):
        rd = [F0[b] + np.tensordot(y, Fk_arr[b], axes=([0], [0])) - S[b] for b in range(n_blk)]
        rp = c_vec - sum(np.einsum("kij,ij->k", Fk_arr[b], X[b]) for b in range(n_blk))
        mu = sum(np.sum(X[b] * S[b]) for b in range(n_blk)) / tot_dim
        p_err = float(np.linalg.norm(rp))
        d_err = float(max(np.linalg.norm(r) for r in rd))
        p_obj = float(np.dot(c_vec, y))
        d_obj = -sum(float(np.sum(F0[b] * X[b])) for b in range(n_blk))
        gap = abs(p_obj - d_obj) / max(1.0, abs(p_obj))
        if p_err < tol and d_err < tol and gap < tol:
            break

        Sinv = []
        for b in range(n_blk):
            ev, V = np.linalg.eigh(0.5 * (S[b] + S[b].T))
            ev = np.maximum(ev, 1e-14)
            Sinv.append((V / ev) @ V.T)

        M_schur = np.zeros((m_vars, m_vars))
        for b in range(n_blk):
            AS = np.einsum("kij,jl->kil", Fk_arr[b], Sinv[b])
            BX = np.einsum("lij,jm->lim", Fk_arr[b], X[b])
            M_schur += np.einsum("kij,lji->kl", AS, BX)
        M_schur = 0.5 * (M_schur + M_schur.T)
        mev, mV = np.linalg.eigh(M_schur)
        reg = max(1e-13 * max(mev[-1], 1.0), 1e-15)
        mev_inv = 1.0 / np.maximum(mev, reg)

        def solve_M(rhs):
            return mV @ (mev_inv * (mV.T @ rhs))

        def solve_dir(sigma_val, corr_R=None):
            rhs = -rp.copy()
            R_list = []
            for b in range(n_blk):
                Rb = (sigma_val * mu * Sinv[b] - X[b]) if corr_R is None else corr_R[b]
                R_list.append(Rb)
                T_b = Rb - Sinv[b] @ rd[b] @ X[b]
                T_b = 0.5 * (T_b + T_b.T)
                rhs += np.einsum("kij,ij->k", Fk_arr[b], T_b)
            dy = solve_M(rhs)
            dS = [np.tensordot(dy, Fk_arr[b], axes=([0], [0])) + rd[b] for b in range(n_blk)]
            dX = []
            for b in range(n_blk):
                dx = R_list[b] - Sinv[b] @ dS[b] @ X[b]
                dX.append(0.5 * (dx + dx.T))
            return dy, dS, dX

        dy_p, dS_p, dX_p = solve_dir(0.0)
        ap = min(max_step(X[b], dX_p[b]) for b in range(n_blk))
        ad = min(max_step(S[b], dS_p[b]) for b in range(n_blk))
        mu_aff = sum(np.sum((X[b] + ap * dX_p[b]) * (S[b] + ad * dS_p[b])) for b in range(n_blk)) / tot_dim
        sigma = min(0.8, max(1e-3, (mu_aff / max(mu, 1e-30)) ** 3))

        if p_err + d_err > 1e-2 or min(ap, ad) < 1e-2:
            dy, dS, dX = solve_dir(sigma)
        else:
            corr_R = [sigma * mu * Sinv[b] - X[b] - Sinv[b] @ dS_p[b] @ dX_p[b] for b in range(n_blk)]
            dy, dS, dX = solve_dir(sigma, corr_R=corr_R)

        ap = min(max_step(X[b], dX[b]) for b in range(n_blk))
        ad = min(max_step(S[b], dS[b]) for b in range(n_blk))
        y += ad * dy
        for b in range(n_blk):
            S[b] = 0.5 * ((S[b] + ad * dS[b]) + (S[b] + ad * dS[b]).T)
            X[b] = 0.5 * ((X[b] + ap * dX[b]) + (X[b] + ap * dX[b]).T)

    return y, S, X, p_err, d_err, gap, it


def solve_uninverted_2x2_sdp(Lam, sig, nodes, basis="Q"):
    """Level-0 uninverted 2x2 CP-kernel bridge SDP (ZERO D <= I)."""
    N = len(nodes)
    X1, X2 = np.meshgrid(nodes, nodes, indexing="ij")
    _, xp, _, _ = roots_kappa(Lam, 1.5)
    qp = np.sqrt(xp)

    if basis == "Q":
        alpha = -1.0 / (X1 * X2)
        beta = (Lam - X1 - X2) / (X1 * X2)
        gam = 1.0 - X1 * X2
        sig_coeff = sig
        b_lo, b_hi, scale_B = 0.0, qp, 1.0
    elif basis == "X":
        alpha = -(Lam * Lam) / (X1 * X2)
        beta = +(Lam * Lam) / (X1 * X2)
        gam = 1.0 - (X1 - 1.0) * (X2 - 1.0)
        sig_coeff = Lam * sig
        b_lo, b_hi, scale_B = 1.0, 1.0 + xp, Lam
    else:
        raise ValueError(basis)

    pairs = [(i, j) for i in range(N) for j in range(i, N)]
    n_sym = len(pairs)
    m_vars = 2 * n_sym
    # Blocks: 0: [[W0,W1],[W1,W2]], 1: b_hi W0 - W1, 2: b_hi W1 - W2, 3: W1 - b_lo W0, 4: W2 - b_lo W1, 5: [[t,p^T],[p,B_hat]]
    sizes = [2 * N, N, N, N, N, N + 1]
    n_blk = len(sizes)
    F0 = [np.zeros((s, s)) for s in sizes]
    Fk = [[np.zeros((s, s)) for _ in range(m_vars)] for s in sizes]

    def put_sym(M, r, c, val):
        M[r, c] += val
        if r != c:
            M[c, r] += val

    def add_W0(dest, coeff, i, j):
        put_sym(dest[0], i, j, coeff)
        put_sym(dest[0], N + i, N + j, coeff * alpha[i, j])
        put_sym(dest[1], i, j, coeff * b_hi)
        put_sym(dest[2], i, j, -coeff * alpha[i, j])
        put_sym(dest[3], i, j, -coeff * b_lo)
        put_sym(dest[4], i, j, coeff * alpha[i, j])
        put_sym(dest[5], 1 + i, 1 + j, coeff * sig_coeff)
        dest[5][0, 1 + i] += coeff
        dest[5][1 + i, 0] += coeff
        if i != j:
            dest[5][0, 1 + j] += coeff
            dest[5][1 + j, 0] += coeff

    def add_W1(dest, coeff, i, j):
        for (r, c) in ([(i, j)] if i == j else [(i, j), (j, i)]):
            dest[0][r, N + c] += coeff
            dest[0][N + c, r] += coeff
        put_sym(dest[0], N + i, N + j, coeff * beta[i, j])
        put_sym(dest[1], i, j, -coeff)
        put_sym(dest[2], i, j, coeff * (b_hi - beta[i, j]))
        put_sym(dest[3], i, j, coeff)
        put_sym(dest[4], i, j, coeff * (beta[i, j] - b_lo))
        put_sym(dest[5], 1 + i, 1 + j, coeff * gam[i, j])

    add_W0(F0, 1.0, 0, 0)
    Fk[5][0][0, 0] = 1.0
    c_vec = np.zeros(m_vars)
    c_vec[0] = 1.0

    for idx, (i, j) in enumerate(pairs[1:]):
        k = 1 + idx
        mult = 1.0 if i == j else 2.0
        dest = [Fk[b][k] for b in range(n_blk)]
        add_W0(dest, 1.0, i, j)
        add_W0(dest, -mult, 0, 0)

    for idx, (i, j) in enumerate(pairs):
        k = n_sym + idx
        dest = [Fk[b][k] for b in range(n_blk)]
        add_W1(dest, 1.0, i, j)

    Fk_arr = [np.array(Fk[b]) for b in range(n_blk)]
    y, S, X, pe, de, gap, it = solve_dual_sdp(c_vec, F0, Fk_arr, max_iter=100, tol=1e-9)
    t_opt = float(y[0])
    T_bound = 1.0 / (scale_B * t_opt) if t_opt > 0 else np.inf
    return T_bound, t_opt, X, S, max(pe, de, gap), it


# =============================================================================
# SUITE 1: Uninverted CP Operator Bridge (Theorem 1.1) over C^n
# =============================================================================

def suite_1_cp_operator_bridge():
    print("=== SUITE 1: UNINVERTED CP OPERATOR BRIDGE (THEOREM 1.1) OVER C^n ===")
    rng = np.random.default_rng(20261128)
    min_margin_mult = np.inf
    min_margin_aff = np.inf
    n_aff = 0

    for trial in range(200):
        n = int(rng.integers(3, 8))
        # Build D with deliberate degenerate eigenspaces AND non-top eigenvalues (no D <= I!)
        d_vals = np.array([3.7, 3.7] + list(rng.uniform(0.05, 3.0, size=n - 2)))
        U_D = random_unitary(n, rng)
        D = U_D @ np.diag(d_vals) @ U_D.conj().T
        D2 = D @ D

        # Build E_hat commuting with D (non-diagonal within the degenerate d=3.7 block!)
        E_hat_blk = np.zeros((n, n), dtype=complex)
        Z2 = rng.standard_normal((2, 2)) + 1j * rng.standard_normal((2, 2))
        E_hat_blk[:2, :2] = 0.5 * (Z2 + Z2.conj().T)
        for i in range(2, n):
            E_hat_blk[i, i] = rng.normal()
        E_hat = U_D @ E_hat_blk @ U_D.conj().T
        assert np.linalg.norm(E_hat @ D - D @ E_hat) < 1e-12

        # Pick sig >= lam_max(E_hat) so B_sig = D (sig I - E_hat) D >= 0
        e_eigs, _ = np.linalg.eigh(E_hat_blk)
        sig = float(np.max(e_eigs)) + float(rng.uniform(0.05, 1.0))
        B_sig = D @ (sig * np.eye(n) - E_hat) @ D
        B_sig = 0.5 * (B_sig + B_sig.conj().T)
        assert np.min(np.linalg.eigvalsh(B_sig)) >= -1e-12

        # Build CP operator sum_{l=0}^r H_l B_sig H_l with r = 3 complex Hermitian H_l
        r = 3
        H_list = []
        for l in range(r + 1):
            Z = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
            H = 0.5 * (Z + Z.conj().T)
            if l == 0:
                H_pos = H + (abs(np.min(np.linalg.eigvalsh(H))) + rng.uniform(0.2, 1.0)) * np.eye(n)
                H_list.append(H_pos)
            else:
                H_list.append(0.3 * H)

        CP_B = sum(H @ B_sig @ H for H in H_list)
        CP_B = 0.5 * (CP_B + CP_B.conj().T)

        # (a) Multiplicative form: exact smallest C s.t. CP_B <= C D^2 is lam_max(D^{-1} CP_B D^{-1})
        Dinv = U_D @ np.diag(1.0 / d_vals) @ U_D.conj().T
        C_min = float(np.max(np.linalg.eigvalsh(0.5 * (Dinv @ CP_B @ Dinv + (Dinv @ CP_B @ Dinv).conj().T))))
        g_min = float(np.min(np.linalg.eigvalsh(H_list[0])))
        assert g_min > 0.0

        # Check ALL joint eigenvectors (including degenerate top block AND non-top eigenvalues!)
        ev_blk, V_blk = np.linalg.eigh(E_hat_blk[:2, :2])
        joint_vecs = [U_D[:, :2] @ V_blk[:, 0], U_D[:, :2] @ V_blk[:, 1]] + [U_D[:, i] for i in range(2, n)]
        joint_e = [ev_blk[0], ev_blk[1]] + [float(np.real(E_hat_blk[i, i])) for i in range(2, n)]
        for w, ew in zip(joint_vecs, joint_e):
            margin = (C_min / (g_min ** 2)) - (sig - ew)
            min_margin_mult = min(min_margin_mult, margin)
            assert margin >= -1e-11, f"Multiplicative bridge failed: margin={margin}"

        # (b) Affine form: construct H0_aff so A_lin = D^{-1}(H0_aff D^2 + D^2 H0_aff)D^{-1} > 0,
        # verify automatic H0_aff_s >= (t_aff / 2) I AND (1/t_aff) >= sig - e_w for all joint eigenvectors!
        Z_pert = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
        H_pert = 0.5 * (Z_pert + Z_pert.conj().T)
        H0_aff = np.eye(n) + (0.4 / (np.max(d_vals) / np.min(d_vals) * (np.linalg.norm(H_pert, 2) + 1e-6))) * H_pert
        CP_aff_unit = H0_aff @ B_sig @ H0_aff + sum(H @ B_sig @ H for H in H_list[1:])
        A_lin = Dinv @ (H0_aff @ D2 + D2 @ H0_aff) @ Dinv
        A_lin = 0.5 * (A_lin + A_lin.conj().T)
        assert np.min(np.linalg.eigvalsh(A_lin)) > 0.1
        Q_mat = 0.5 * (Dinv @ CP_aff_unit @ Dinv + (Dinv @ CP_aff_unit @ Dinv).conj().T)
        s = 0.5 * float(np.min(np.linalg.eigvalsh(A_lin))) / (float(np.max(np.linalg.eigvalsh(Q_mat))) + 1.0)
        t_aff = float(np.min(np.linalg.eigvalsh(s * A_lin - (s * s) * Q_mat)))
        assert t_aff > 0.0
        assert np.min(np.linalg.eigvalsh(s * H0_aff)) >= 0.5 * t_aff - 1e-12
        n_aff += 1
        for w, ew in zip(joint_vecs, joint_e):
            margin = (1.0 / t_aff) - (sig - ew)
            min_margin_aff = min(min_margin_aff, margin)
            assert margin >= -1e-11, f"Affine bridge failed: margin={margin}"

    assert n_aff == 200
    print(f"  200 complex Hermitian trials (all {n_aff} mult & affine; degenerate & non-top eigenvalues, no D<=I): 0 violations!")
    print(f"  Min margin (Multiplicative CP): {min_margin_mult:+.4e} | Min margin (Affine CP): {min_margin_aff:+.4e}")


# =============================================================================
# SUITE 2: Exact p=3/2 X-basis & Q-basis Reductions, Pick Kernel, Level-0 SDP
# =============================================================================

def suite_2_p32_operator_bridge():
    print("\n=== SUITE 2: EXACT p = 3/2 X-BASIS & Q-BASIS REDUCTIONS & CP-KERNEL BRIDGE ===")
    rng = np.random.default_rng(314159)

    # 2A. Verify Prop 2.1 identities on genuinely COMPLEX Hermitian rotated coupled r=2 and r=3 RG solutions
    for r in [2, 3]:
        Lam, ds, Q_real, rg_res = solve_rg_p32_coupled(r, m=2)
        V = random_unitary(r, rng)
        D = V @ np.diag(ds) @ V.conj().T
        Dhi = V @ np.diag(1.0 / np.sqrt(ds)) @ V.conj().T
        Q = V @ Q_real @ V.conj().T
        H = Q @ D @ Q
        X = Dhi @ H @ Dhi
        W = np.eye(r) + X
        F = Q @ D @ Q @ D @ Q - D @ Q @ D
        _, xp, _, sigp = roots_kappa(Lam, 1.5)
        qp = np.sqrt(xp)

        # Operator identities (Prop 2.1)
        err_W = np.linalg.norm(W @ D @ W @ W @ D @ W - (Lam ** 2) * (D @ X @ D))
        err_F = np.linalg.norm(Lam * F - (W @ D @ W @ D @ W - D @ W @ D @ W - W @ D @ W @ D))

        # Eigenbasis reductions (over C!)
        qs, UQ = np.linalg.eigh(0.5 * (Q + Q.conj().T))
        ws, UX = np.linalg.eigh(0.5 * (W + W.conj().T))
        assert np.all(qs > 0) and np.max(qs) <= qp + 1e-12
        assert np.min(ws) > 1.0 and np.max(ws) <= 1.0 + xp + 1e-12

        AQ = UQ.conj().T @ D @ UQ
        AX = UX.conj().T @ D @ UX
        SQ0, SQ1, SQ2 = AQ @ AQ, AQ @ np.diag(qs) @ AQ, AQ @ np.diag(qs ** 2) @ AQ
        RX0, RX1, RX2 = AX @ AX, AX @ np.diag(ws) @ AX, AX @ np.diag(ws ** 2) @ AX

        Q1, Q2 = np.meshgrid(qs, qs, indexing="ij")
        W1, W2 = np.meshgrid(ws, ws, indexing="ij")
        err_Q2 = np.linalg.norm(SQ2 - ((-1.0 / (Q1 * Q2)) * SQ0 + ((Lam - Q1 - Q2) / (Q1 * Q2)) * SQ1))
        err_X2 = np.linalg.norm(RX2 - ((Lam * Lam / (W1 * W2)) * (RX1 - RX0)))
        # Exact pure-congruence check: R2 = Lam^2 W^{-1} (R1 - R0) W^{-1}
        err_cong = np.linalg.norm(RX2 - (Lam ** 2) * (np.diag(1.0 / ws) @ (RX1 - RX0) @ np.diag(1.0 / ws)))
        err_BX = np.linalg.norm(
            Lam * (UX.conj().T @ (sigp * D @ D - F) @ UX)
            - (Lam * sigp * RX0 + (1.0 - (W1 - 1.0) * (W2 - 1.0)) * RX1)
        )
        assert max(err_W, err_F, err_Q2, err_X2, err_cong, err_BX) < 1e-13
        print(f"  Coupled r={r} (complex Hermitian): Lam={Lam:.12f}, res={rg_res:.1e} | max identity err = {max(err_W, err_F, err_Q2, err_X2, err_cong, err_BX):.2e}")

    # 2B. Verify Prop 2.3(2): exact PSDness of boundary Pick kernel K_N(q,r) = 1/(Lam - q - r - qp q r)
    for m in [2, 3, 4, 10, 50]:
        Lam, _ = scalar_1x1(1.5, m)
        _, xp, _, _ = roots_kappa(Lam, 1.5)
        qp = np.sqrt(xp)
        qs = np.linspace(0.0, qp, 30)
        Q1, Q2 = np.meshgrid(qs, qs, indexing="ij")
        K_N = 1.0 / (Lam - Q1 - Q2 - qp * Q1 * Q2)
        min_ev = float(np.min(np.linalg.eigvalsh(K_N)))
        assert min_ev >= -1e-14, f"K_N not PSD at m={m}: min_ev={min_ev}"
    print("  Boundary Pick kernel K_N(q,r) = 1/(Lam - q - r - qp q r): strictly PSD on [0, qp]^2 for all m tested!")

    # 2C. Numerical Finite-Grid Level-0 CP-Kernel SDP (N=10 Chebyshev nodes): Q-basis vs X-basis + dual D1/D2 + delta-slope!
    print("  [Numerical evaluation on N=10 Chebyshev grid — NOT a continuous mpmath.iv certificate]:")
    Lam_rg3, _, _, _ = solve_rg_p32_coupled(3, m=2)
    for m in [2, 3, 4, 10, 50]:
        Lam = Lam_rg3 if m == 2 else scalar_1x1(1.5, m)[0]
        _, xp, _, sigp = roots_kappa(Lam, 1.5)
        qp = np.sqrt(xp)
        N = 10
        cheb = 0.5 * (1.0 - np.cos(np.pi * (2 * np.arange(N) + 1) / (2 * N)))
        qs = 0.03 * qp + 0.96 * qp * cheb
        ws = 1.0 + 0.01 * xp + 0.98 * xp * cheb

        TQ, tQ, XQ, SQ, errQ, _ = solve_uninverted_2x2_sdp(Lam, sigp, qs, basis="Q")
        TX, tX, _, _, errX, _ = solve_uninverted_2x2_sdp(Lam, sigp, ws, basis="X")
        target = (m / (m - 1.0)) * sigp
        assert TQ < TX, f"Q-basis should beat X-basis at m={m}!"

        # Check Envelope-Theorem delta-slope: dT/dsig = <H_B^*, W_0^*> / t^2 >= 1 vs finite diff!
        B_dual = XQ[5] / XQ[5][0, 0]
        H_B = B_dual[1:, 1:]
        g = -B_dual[0, 1:]
        W0_opt = SQ[0][:N, :N]
        assert np.min(np.linalg.eigvalsh(H_B - np.outer(g, g))) >= -1e-10
        # Verify Level-1 redundancy W0 >= p p^T automatically!
        p_opt = W0_opt @ np.ones(N)
        assert np.min(np.linalg.eigvalsh(W0_opt - np.outer(p_opt, p_opt))) >= -1e-9

        slope_env = float(np.sum(H_B * W0_opt)) / (tQ * tQ)
        d_sig = 0.01 * sigp
        TQ_p, _, _, _, _, _ = solve_uninverted_2x2_sdp(Lam, sigp + d_sig, qs, basis="Q")
        slope_fd = (TQ_p - TQ) / d_sig
        assert slope_env >= 1.0 - 1e-4 and slope_env < m / (m - 1.0)
        assert abs(slope_env - slope_fd) < 0.03, f"Slope mismatch: env={slope_env} vs fd={slope_fd}"

        # Verify polynomial dual (D1) residual in Q-basis
        M_2x2 = XQ[0] / XQ[5][0, 0]
        N1 = XQ[2] / XQ[5][0, 0]
        Qinv = np.diag(1.0 / qs)
        M01_t = M_2x2[:N, N:] @ Qinv
        M11_t = Qinv @ M_2x2[N:, N:] @ Qinv
        N1_t = Qinv @ N1 @ Qinv
        Q1, Q2 = np.meshgrid(qs, qs, indexing="ij")
        res_D1 = (
            (1.0 - Q1 * Q2) * H_B
            + Q2 * M01_t + Q1 * M01_t.T
            + (Lam - Q1 - Q2) * M11_t
            + (qp * Q1 * Q2 - Lam + Q1 + Q2) * N1_t
        )
        assert np.linalg.norm(res_D1) < 1e-3
        print(
            f"    m={m:2d}: target={target:.7f} | Q-L0={TQ:.7f} (+{TQ-target:.2e}) | "
            f"X-L0={TX:.7f} (+{TX-target:.2e}) | env_slope={slope_env:.5f} (fd={slope_fd:.5f}) < {m/(m-1):.4f}"
        )


# =============================================================================
# SUITE 3: Five-Line Purely Analytic Perfect-Square Theorem at p = 3/2 (Thm 3.1)
# =============================================================================

def suite_3_p32_perfect_square():
    print("\n=== SUITE 3: FIVE-LINE PERFECT-SQUARE THEOREM AT p = 3/2 (THEOREM 3.1) ===")
    # Verify exact existence bracket F(2/Lam) > 14/256 for all Lam > 4
    for L in [4.0001, 4.45337, 5.0, 10.0, 100.0]:
        F_hi = 3.0 / 8.0 - 5.0 / (L ** 2) - 2.0 / (L ** 4)
        assert F_hi > 14.0 / 256.0 - 1e-4

    def u_p32(L):
        F = lambda u: L * u - 13.0 / 8.0 - 1.25 * u * u - 0.125 * (u ** 4)
        assert F(0.0) < 0.0 < F(2.0 / L)
        return brentq(F, 0.0, 2.0 / L, xtol=1e-15, rtol=1e-15)

    for m in [2, 3, 4, 10, 50, 1000]:
        Lam1, C1 = scalar_1x1(1.5, m)
        # Solve Lam * sig_+(Lam) / (m-1) = 1 + u(Lam)^2 / 2
        def gap(L):
            _, _, _, sp = roots_kappa(L, 1.5)
            u = u_p32(L)
            return L * sp / (m - 1.0) - (1.0 + 0.5 * u * u)
        hi = Lam1 * 1.5
        while gap(hi) < 0.0:
            hi *= 1.5
        Lam_ub = brentq(gap, Lam1, hi, xtol=1e-15, rtol=1e-15)
        C_ub = (Lam_ub / 4.0) ** (1.0 / 3.0)

        # Also check closed-form weaker bound Lam * sig_+(Lam) / (m-1) <= 1 + 2 / Lam^2
        def gap_cf(L):
            _, _, _, sp = roots_kappa(L, 1.5)
            return L * sp / (m - 1.0) - (1.0 + 2.0 / (L * L))
        hi_cf = Lam_ub * 1.5
        while gap_cf(hi_cf) < 0.0:
            hi_cf *= 1.5
        Lam_cf = brentq(gap_cf, Lam_ub, hi_cf, xtol=1e-15, rtol=1e-15)
        C_cf = (Lam_cf / 4.0) ** (1.0 / 3.0)
        assert C1 < C_ub < C_cf

        # Verify BOTH exact perfect-square identities at Lam_ub on dense grids!
        u = u_p32(Lam_ub)
        alpha, beta, gamma, lam1 = -u, (3.0 + u * u) / (2.0 * Lam_ub), -1.0 / (2.0 * Lam_ub), ((1.0 + u * u) ** 2) / (8.0 * Lam_ub)
        gs = np.geomspace(1e-8, 100.0, 20000)
        Pmu = (np.sqrt(gs) - gs ** 1.5) - alpha * gs - beta * Lam_ub * np.sqrt(gs) - gamma * Lam_ub * (np.sqrt(gs) + gs ** 1.5)
        Pmu_sq = -0.5 * np.sqrt(gs) * ((np.sqrt(gs) - u) ** 2)
        assert np.max(np.abs(Pmu - Pmu_sq)) < 1e-11 * np.max(np.abs(Pmu) + 1.0)
        assert np.max(Pmu) <= 1e-14

        ts = np.geomspace(1e-5, 100.0, 20000)
        Pnu_lhs = Lam_ub * (alpha * ts + beta * (ts ** 2) + gamma * (ts ** 3) - lam1 * (1.0 / ts - 1.0) - alpha)
        Pnu_sq = (1.0 + 0.5 * u * u) - ((ts - 1.0) ** 2) / (2.0 * ts) * ((ts - 0.5 * (1.0 + u * u)) ** 2)
        assert np.max(np.abs(Pnu_lhs - Pnu_sq)) < 1e-10 * np.max(np.abs(Pnu_lhs) + 1.0)
        assert np.max(Pnu_lhs) <= 1.0 + 0.5 * u * u + 1e-12

        print(f"  m={m:4d}: C_1x1={C1:.7f} | Thm3.1(exact u)={C_ub:.7f} (+{C_ub-C1:.2e}) | Thm3.1(1+2/L^2)={C_cf:.7f} (+{C_cf-C1:.2e})")


# =============================================================================
# SUITE 4: Universal All-p, All-m Bound & Exact Large-m Law (Thm 4.3)
# =============================================================================

def K_kappa_analytic(k):
    if k <= 1.5:
        return 0.0
    elif k < 2.0:
        return min((k - 1.0) * (2.0 * k - 3.0), (2.0 * k - 1.0) * ((2.0 - 3.0 / k) ** (2.0 * k - 3.0)))
    elif abs(k - 2.0) < 1e-14:
        return 2.0 / (3.0 * np.sqrt(3.0))
    else:
        return 2.0 * (2.0 * k - 1.0) * ((2.0 - 3.0 / k) ** (2.0 * k - 3.0))


def suite_4_universal_all_p_large_m():
    print("\n=== SUITE 4: UNIVERSAL ALL-p, ALL-m BOUND & EXACT LARGE-m LAW (LEM 4.1-4.2, THM 4.3) ===")
    # 4A. Verify Lemma 4.1 across 15 exponents p in [1.05, 1.98]
    ts = np.concatenate([
        np.geomspace(1e-6, 0.99999, 25000),
        np.linspace(1.00001, 2.5, 25000),
        np.geomspace(2.5, 100.0, 10000),
    ])
    for p in [1.05, 1.1, 1.15, 1.2, 1.25, 1.3, 4.0 / 3.0, 1.4, 1.45, 1.5, 1.6, 1.75, 1.85, 1.9, 1.98]:
        k = p / (2.0 * (p - 1.0))
        K_an = K_kappa_analytic(k)
        g = (2.0 - ts) * (ts ** (2.0 * k - 1.0)) - 1.0 - 2.0 * (k - 1.0) * (ts - 1.0)
        R = ts * g / ((ts - 1.0) ** 2)
        R1 = (2.0 * k - 1.0) * (k - 2.0)
        K_exact = max(0.0, float(np.max(R)), float(R1))
        assert K_an >= K_exact - 1e-12, f"Lemma 4.1 failed at p={p}: K_an={K_an} < K_exact={K_exact}"
        if k <= 1.5:
            assert K_exact <= 1e-14
        if abs(k - 2.0) < 1e-14:
            assert abs(K_exact - 2.0 / (3.0 * np.sqrt(3.0))) < 1e-9
    print("  Lemma 4.1 (K_kappa^an >= sup_{t>0} R_kappa(t)): PASSED across all 15 exponents p in [1.05, 1.98]!")

    # 4B. Verify every step of Lemma 4.2 & Theorem 4.3 on real noncommuting complex-rotated RG solutions
    rng = np.random.default_rng(4242)
    for p_label, k in [("3/2", 1.5), ("4/3", 2.0), ("6/5", 3.0)]:
        Lam, d1, H_real = solve_rg_general_r2(k, m=2)
        V = random_unitary(2, rng)
        D = V @ np.diag([1.0, d1]) @ V.conj().T
        Dh = V @ np.diag([1.0, np.sqrt(d1)]) @ V.conj().T
        H = V @ H_real @ V.conj().T
        G = Dh @ H @ Dh
        M = D + H
        v0 = V[:, 0]  # unit eigenvector of D with eigenvalue 1
        assert np.linalg.norm(D @ v0 - v0) < 1e-14

        def mat_pow_c(A, pw):
            ev, U = np.linalg.eigh(0.5 * (A + A.conj().T))
            return (U * (np.maximum(ev, 1e-30) ** pw)) @ U.conj().T

        E = mat_pow_c(G, k) - D @ mat_pow_c(G, k - 1.0) @ D
        psi = float(np.real(-v0.conj() @ E @ v0))
        eps = float(np.real(v0.conj() @ H @ v0))
        m_inv = float(np.real(v0.conj() @ np.linalg.inv(M) @ v0))
        m_2km1 = float(np.real(v0.conj() @ mat_pow_c(M, 2.0 * k - 1.0) @ v0))
        Lam0 = 2.0 ** (2.0 * k - 1.0)
        K_an = K_kappa_analytic(k)
        eps_ub = ((Lam0 - Lam * psi) / Lam) ** (1.0 / k)

        assert m_inv < 1.0
        assert m_2km1 < Lam0
        assert eps < eps_ub
        rhs_bound = (1.0 + eps_ub) ** (2.0 * k - 2.0) if k <= 1.5 else 1.0 + (2.0 * k - 2.0 + K_an) * eps_ub
        assert Lam * psi <= rhs_bound + 1e-12
        print(f"  RG r=2 (complex, p={p_label}): <M^-1>={m_inv:.5f}<1, eps={eps:.5f}<{eps_ub:.5f}, Lam*psi={Lam*psi:.6f}<={rhs_bound:.6f}")

    # 4C. Verify Exact Large-m Scaling Law + universal +1/2 second term (p in [3/2, 2))
    print("  Exact Large-m Scaling Law verification (m = 10^6):")
    for p in [1.1, 1.2, 4.0 / 3.0, 1.5, 1.75, 1.9]:
        k = p / (2.0 * (p - 1.0))
        K_an = K_kappa_analytic(k)
        Lam0 = 2.0 ** (2.0 * k - 1.0)
        c_exact = 2.0 ** (-1.0 / p)
        alpha = 0.5 * (1.0 - 1.0 / p)
        err_exp = 1.0 - 1.0 / p

        m = 1000000
        Lam1, C1 = scalar_1x1(k, m)
        def gap_B(L):
            _, _, _, sp = roots_kappa(L, k)
            lhs = L * sp / (m - 1.0)
            if lhs >= Lam0:
                return 1.0
            e_ub = ((Lam0 - lhs) / L) ** (1.0 / k)
            rhs = (1.0 + e_ub) ** (2.0 * k - 2.0) if k <= 1.5 else 1.0 + (2.0 * k - 2.0 + K_an) * e_ub
            return lhs - rhs
        hi = max(Lam1 * 2.0, 2.0 * np.sqrt(m) + 10.0)
        while gap_B(hi) < 0.0:
            hi *= 2.0
        Lam_ub = brentq(gap_B, Lam1, hi, xtol=1e-14)
        C_ub = (Lam_ub / Lam0) ** (1.0 / (2.0 * k))

        scale = c_exact * (m ** alpha)
        c_interp = 2.0 ** (-(1.0 - 1.0 / p))
        assert C1 <= C_ub
        assert abs(C1 / scale - 1.0) < 0.25 and abs(C_ub / scale - 1.0) < 0.45
        assert c_exact < c_interp
        # Check exact two-term bound at p = 3/2 (Thm 3.1) and p in {1.75, 1.9} (Thm 5.1)
        extra = ""
        if abs(p - 1.5) < 1e-12:
            def gap_sq(L):
                _, _, _, sp = roots_kappa(L, 1.5)
                u = brentq(lambda u: L * u - 13.0 / 8.0 - 1.25 * u * u - 0.125 * (u ** 4), 0.0, 2.0 / L, xtol=1e-15)
                return L * sp / (m - 1.0) - (1.0 + 0.5 * u * u)
            L_sq = brentq(gap_sq, Lam1, Lam_ub, xtol=1e-14)
            C_sq = (L_sq / 4.0) ** (1.0 / 3.0)
            s2_lb = (C1 / scale - 1.0) * (m ** err_exp)
            s2_ub = (C_sq / scale - 1.0) * (m ** err_exp)
            assert abs(s2_lb - 0.5) < 0.005 and abs(s2_ub - 0.5) < 0.005
            extra = f" | 2nd-term coeff: lb={s2_lb:.5f}, ub(Thm3.1)={s2_ub:.5f} (exact 0.50000)"
        elif p > 1.5:
            c2 = 3.0 - 2.0 * k
            B_c = (2.0 * k - 1.0) * (k - 1.0) * c2 / (2.0 - k)
            def gap_51(L):
                _, _, _, sp = roots_kappa(L, k)
                Ac = (c2 / (2.0 - k)) * L
                # Estimate g0 ~ Ac^{-1/(k-1)}; if < 1e-16, exact g0 is sub-float64 (< 1e-15)
                log_g0_est = -np.log(Ac) / (k - 1.0)
                if log_g0_est < -36.0:
                    g0 = np.exp(log_g0_est) * (1.0 + 1e-12)
                else:
                    gp = ((k - 1.0) * Ac / B_c) ** (1.0 / (2.0 - k))
                    g0 = brentq(lambda g: Ac * (g ** (k - 1.0)) - B_c * g - 1.0, 0.0, gp, xtol=1e-15)
                return L * sp / (m - 1.0) - (1.0 + B_c * g0)
            if gap_51(Lam1) >= 0.0:
                # Sub-float64 gap (B_c * g0 < 1e-15): Lam_51 == Lam1 to float64 precision
                L_51 = Lam1
            else:
                L_51 = brentq(gap_51, Lam1, Lam_ub, xtol=1e-14)
            C_51 = (L_51 / Lam0) ** (1.0 / (2.0 * k))
            s2_lb = (C1 / scale - 1.0) * (m ** err_exp)
            s2_ub = (C_51 / scale - 1.0) * (m ** err_exp)
            assert abs(s2_lb - 0.5) < 0.002 and abs(s2_ub - 0.5) < 0.002
            extra = f" | 2nd-term coeff: lb={s2_lb:.5f}, ub(Thm5.1)={s2_ub:.5f} (exact 0.50000)"
        print(f"    p={p:.4f}: C_lb/scale={C1/scale:.6f}, C_ub(Thm4.3)/scale={C_ub/scale:.6f} (c_interp/c_exact={c_interp/c_exact:.4f}){extra}")


# =============================================================================
# SUITE 5: 100-Digit mpmath Super-Exponential p -> 2^- Collapse (Thm 5.1, Cor 5.2)
# =============================================================================

def suite_5_superexp_p_to_2():
    print("\n=== SUITE 5: 100-DIGIT MPMATH SUPER-EXPONENTIAL p -> 2^- COLLAPSE (THM 5.1, COR 5.2) ===")
    # 5A. Dense-grid verification of P_mu(g) <= 0 and h(t) <= 1 + B g0 on (0, inf)
    for m in [2, 10]:
        for p in [1.55, 1.6, 1.7, 1.8, 1.85, 1.9]:
            k = p / (2.0 * (p - 1.0))
            Lam1, _ = scalar_1x1(k, m)
            c2 = 3.0 - 2.0 * k
            Ac = (c2 / (2.0 - k)) * Lam1
            Bc = (2.0 * k - 1.0) * (k - 1.0) * c2 / (2.0 - k)
            gp = ((k - 1.0) * Ac / Bc) ** (1.0 / (2.0 - k))
            g_cap = (2.0 * k - 1.0) / Bc
            g_lim = min(gp, g_cap)
            assert Ac * (g_lim ** (k - 1.0)) - Bc * g_lim > 1.0
            g0 = brentq(lambda g: Ac * (g ** (k - 1.0)) - Bc * g - 1.0, 0.0, g_lim, xtol=1e-15, rtol=1e-15)
            abs_c1 = Bc * g0 / (2.0 * k - 1.0)
            r = 1.0 + Bc * g0
            assert abs_c1 < 1.0
            gs = np.geomspace(max(1e-30, g0 * 1e-6), 100.0, 15000)
            Pmu = -abs_c1 * (gs ** (k - 1.0)) - c2 * (gs ** k) + (c2 / (2.0 - k)) * (g0 ** (k - 1.0)) * gs
            ts = np.concatenate([np.geomspace(1e-8, 0.9999, 8000), np.linspace(0.9999, 3.0, 8000), np.geomspace(3.0, 100.0, 2000)])
            ht = -r * (ts - 1.0) + (2.0 * k - 1.0 + abs_c1) * (ts ** (2.0 * k - 1.0)) - 2.0 * (k - 1.0) * (ts ** (2.0 * k))
            assert np.max(Pmu) <= 1e-12 and np.max(ht) <= r + 1e-12
    print("  Dense-grid verification of P_mu(g) <= 0 and h(t) <= 1 + B g0 on (0, inf): PASSED!")

    # 5B. 100-digit mpmath verification up to p = 1.98 (gaps down to 10^-65!)
    mp.mp.dps = 100
    for m in [2, 10]:
        sqrt_m = mp.sqrt(m)
        C2_m = mp.sqrt((1 + sqrt_m) / 2)
        eta_m = (sqrt_m + 1) / (2 * sqrt_m) * mp.log(1 + sqrt_m) - mp.log(m) / 4
        exact_slope = mp.log(1 + sqrt_m) / (4 * sqrt_m) - mp.log(2) / 4 - mp.log(m) / 8
        print(f"  m = {m} (C_2(m) = {mp.nstr(C2_m, 10)}, exact left slope = {mp.nstr(exact_slope, 8)}):")

        for p_str in ["1.8", "1.9", "1.95", "1.98"]:
            p = mp.mpf(p_str)
            k = p / (2 * (p - 1))
            Lam0 = mp.power(2, 2 * k - 1)
            t_min = mp.log((k - 1) / k)

            def roots_mp(L):
                logL = mp.log(L)
                def fn(t):
                    return (2 * k - 1) * mp.log(1 + mp.exp(t)) - (k - 1) * t - logL
                def dfn(t):
                    et = mp.exp(t)
                    return (2 * k - 1) * et / (1 + et) - (k - 1)
                # Bracket + Newton for t_- < t_min
                lo, hi = t_min - 1, t_min
                while fn(lo) < 0:
                    lo -= 40
                for _ in range(18):
                    mid = (lo + hi) / 2
                    if fn(mid) > 0:
                        lo = mid
                    else:
                        hi = mid
                t = (lo + hi) / 2
                for _ in range(14):
                    t -= fn(t) / dfn(t)
                xm = mp.exp(t)
                # Bracket + Newton for t_+ > t_min
                lo, hi = t_min, t_min + 1
                while fn(hi) < 0:
                    hi += 40
                for _ in range(18):
                    mid = (lo + hi) / 2
                    if fn(mid) < 0:
                        lo = mid
                    else:
                        hi = mid
                t = (lo + hi) / 2
                for _ in range(14):
                    t -= fn(t) / dfn(t)
                xp = mp.exp(t)
                return xm, xp, mp.power(xp, k - 1) * (xp - 1), mp.power(xm, k - 1) * (xm - 1)

            def secant_mp(f_eval, a, b):
                fa, fb = f_eval(a), f_eval(b)
                assert fa < 0 < fb
                for _ in range(20):
                    mid = (a + b) / 2
                    fm = f_eval(mid)
                    if fm < 0:
                        a, fa = mid, fm
                    else:
                        b, fb = mid, fm
                x0, x1 = a, b
                f0, f1 = fa, fb
                for _ in range(18):
                    if abs(f1 - f0) < mp.mpf("1e-95") or abs(f1) < mp.mpf("1e-92"):
                        break
                    x2 = x1 - f1 * (x1 - x0) / (f1 - f0)
                    if not (a < x2 < b):
                        x2 = (a + b) / 2
                    f2 = f_eval(x2)
                    if f2 < 0:
                        a = x2
                    else:
                        b = x2
                    x0, f0, x1, f1 = x1, f1, x2, f2
                return x1

            Lam1 = secant_mp(
                lambda L: roots_mp(L)[2] + (m - 1) * roots_mp(L)[3],
                Lam0 + mp.mpf("1e-30"), mp.mpf(4 * m + 10)
            )
            C1 = mp.power(Lam1 / Lam0, 1 / (2 * k))
            xm, xp, sigp, sigm = roots_mp(Lam1)

            c2 = 3 - 2 * k
            Bc = (2 * k - 1) * (k - 1) * c2 / (2 - k)

            def g0_mp(L):
                Ac = (c2 / (2 - k)) * L
                gp = mp.power((k - 1) * Ac / Bc, 1 / (2 - k))
                g_lim = min(gp, (2 * k - 1) / Bc)
                # Solve in u = g^{k-1} so derivative is O(1) even when g ~ 10^-65!
                # Ac * u - Bc * u^{1/(k-1)} = 1  =>  start at u = 1 / Ac and iterate Newton 12 times!
                u = mp.mpf(1) / Ac
                inv_km1 = mp.mpf(1) / (k - 1)
                for _ in range(14):
                    g = mp.power(u, inv_km1)
                    f = Ac * u - Bc * g - 1
                    df = Ac - Bc * inv_km1 * mp.power(u, inv_km1 - 1)
                    u -= f / df
                g_root = mp.power(u, inv_km1)
                assert 0 < g_root < g_lim
                assert abs(Ac * mp.power(g_root, k - 1) - Bc * g_root - 1) < mp.mpf("1e-90")
                return g_root

            Lam_ub = secant_mp(
                lambda L: L * roots_mp(L)[2] / (m - 1) - (1 + Bc * g0_mp(L)),
                Lam1, Lam1 * 2
            )
            C_ub = mp.power(Lam_ub / Lam0, 1 / (2 * k))
            g0_val = g0_mp(Lam1)
            gap = C_ub - C1
            assert gap > 0

            # Verify asymptotic formulas
            xm_asymp = mp.exp(-2 * eta_m) * mp.power(1 + sqrt_m, -2 * (p - 1) / (2 - p))
            ratio_g0_xm = g0_val / xm
            ratio_xm_asymp = xm / xm_asymp
            num_slope = (mp.log(C1) - mp.log(C2_m)) / (2 - p)
            if p_str == "1.98":
                assert abs(ratio_g0_xm - mp.e) < 0.06
                assert abs(ratio_xm_asymp - 1) < 0.05
                assert abs(num_slope - exact_slope) < 0.005
                assert gap < mp.mpf("1e-40")
            print(
                f"    p={p_str}: gap={mp.nstr(gap, 5):12s} | g0/xm={mp.nstr(ratio_g0_xm, 6)} (e={mp.nstr(mp.e, 6)}) | "
                f"xm/asymp={mp.nstr(ratio_xm_asymp, 6)} | slope={mp.nstr(num_slope, 7)}"
            )


if __name__ == "__main__":
    suite_1_cp_operator_bridge()
    suite_2_p32_operator_bridge()
    suite_3_p32_perfect_square()
    suite_4_universal_all_p_large_m()
    suite_5_superexp_p_to_2()
    print("\nALL 5 SUITES PASSED WITH ZERO ERRORS!")
