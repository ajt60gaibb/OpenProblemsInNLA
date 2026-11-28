r"""
================================================================================
100% ZERO-FLOAT, ZERO-GAP, ALL-DIMENSIONS (n >= 1), ALL-LAMBDA RIGOROUS mpmath.iv
CERTIFICATION OF TIGHT TWO-SIDED ENCLOSURES FOR C_p(m) AT NEW RATIONAL EXPONENTS:
  - p = 6/5 (kappa = 3),    m = 2, 3, 4
  - p = 5/4 (kappa = 5/2),  m = 2, 3, 4
  - p = 3/2 (kappa = 3/2),  m = 2, 3, 4   (TIGHTENED >2x OVER PRIOR!)
  - p = 5/3 (kappa = 5/4),  m = 2, 3, 4

ARCHITECTURE (STRICT SEPARATION OF UNTRUSTED ORACLE vs ZERO-FLOAT VERIFIER):
  - SECTION A (UNTRUSTED ORACLES, `oracle_*`): uses float64 numpy/scipy strictly
    to search for candidate witness objects (explicit SPD matrices T_j and R_0,
    5-scalar LP multipliers, dual NC-SOS Gram factors & ideal multipliers), and
    converts every witness number into exact decimal mp.mpf values BEFORE passing
    to Section B.
  - SECTION B (100% PURE ZERO-FLOAT `mpmath.iv` VERIFIERS, `iv_*` / `certify_*`):
    ZERO `float()`, ZERO `numpy`, ZERO `scipy`, ZERO uncertified plain `mp` bounds!
    Every inequality is checked in outward-rounded `mpmath.iv` interval arithmetic.

COMPLETE UNCONDITIONAL MATHEMATICAL PROOF CHAIN (ALL n >= 1, ALL COMPLEX HERMITIAN):
  LOWER BOUNDS (Unified Fourier / Kubo-Ando Theorem for p = 2a/(a+b) in (1, 2)):
    For explicit real symmetric N x N matrices T_0, ..., T_{m-1} > 0 (certified
    strictly PD via exact `mpmath.iv` Cholesky) and DFT projections P_k = (f_k f_k^*) x I_N,
    A_k := T^{a/2} P_k T^{b/2} (T = diag(T_0, ..., T_{m-1})) satisfies exactly:
      ||sum A_k||_p^p = sum_j Tr(T_j^a),  ||sum |A_k|||_p^p = sum_j Tr((K^{1/2} T_j^b K^{1/2})^p),
    where K = M # N_sum^{-1} (M = sum T_j^a, N_sum = sum T_j^b).
    Certifying R_0 > 0 and (1+tau)^2 R_0^2 N_sum R_0^2 - M > 0 in `mpmath.iv` Cholesky
    proves K <= (1+tau) R_0^2 by operator monotonicity of Kubo-Ando geometric mean,
    and Weyl + Ostrowski (immune to repeated eigenvalues!) encloses Tr((R_0 T_j^b R_0)^p),
    yielding 100% unconditional C_p(m) >= (Num_lo / Den_ub)^{1/p}.

  UPPER BOUNDS (Dimension-Free ALL-n >= 1, ALL-Lambda >= Lam_cert):
    1) Holden Theorem 3.1 (kappa = p/(2(p-1)) > 1): any finite-dim maximizer achieving
       C > 1 yields D > 0, H_1, ..., H_m > 0 solving (D+H_j)^{2k-1} = Lam D^{1/2} G_j^{k-1} D^{1/2}
       (G_j = D^{1/2} H_j D^{1/2}, Lam = 2^{2k-1} C^{2k}), E_j = G_j^k - D G_j^{k-1} D,
       [E_j, D] = 0, sum_j E_j = 0.
    2) Complex interpolation (6-line Hadamard Three-Lines proof between C_1(m) = 1 and
       C_2(m) = sqrt((1 + sqrt(m))/2)) proves unconditionally:
         Lam <= Lam_interp(p, m) := 2^{2k-2} * (1 + sqrt(m)).
    3) Exact Operator Norm Bounds (all kappa > 1, all n >= 1, NO D <= I assumed):
         0 < H_j <= x_+(Lam) D,  0 < G_j <= x_+(Lam) D^2,  0 < D+H_j <= (1+x_+(Lam)) D.
       (1 < k <= 2: Lowner-Heinz; k >= 2: self-contained 3-line polar/antitonicity proof
       via C = G^{-1} >= (lam D^2)^{-1} = D_0, T = C^{(k-1)/2} D_0^{1/4}, s = (k-2)/(k-1/2).)
       Corollaries: Q_j = D^{-1/2} G_j^{1/2} D^{-1/2} <= sqrt(x_+(Lam)) I (p=5/4, 3/2);
       B_j = G_j^{1/4} <= x_+(Lam)^{1/4} D^{1/2} (p=5/3).
    4) Universal 5-Scalar Stage-1 Bound (NO D <= I assumed, any eigenvector D v = v):
       Since M = D + H > D > 0 => E_nu[M^{-1}] < 1, plus E_nu[M] = 1 + E_mu[G],
       E_nu[M^{2k-1}] = Lam E_mu[G^{k-1}], E_nu[M^{2k}] = Lam E_mu[G^{k-1} + G^k]:
         -<v, E_j v> <= sup_{t>0} f_M(t) + sup_{g>0} f_G(g) + lam1 - a <= L_all(Lam),
       certified over ALL (0, inf) (with monotone tail certification) in `mpmath.iv`.
       Hence -L_all(Lam) D^{2k} <= E_j <= (m-1) L_all(Lam) D^{2k} for all j.
    5) Universal Positivity Rigidity at V_+ = ker(D - I) (6-line proof, ALL k > 1, ALL n >= 1):
       Rescaling 0 < D <= I, any unit eigenvector v in V_+ of E_j with lam_0 >= 0 satisfies
       Var(G_j^k) <= Var(G_j^{k-1}) (from ||G_j^k v - lam_0 v||^2 = ||D G_j^{k-1} v||^2 <= ||G_j^{k-1} v||^2),
       while log-convexity of s -> E[G_j^s] gives Var(G_j^k) >= (m_k/m_{k-1})^2 Var(G_j^{k-1})
       strictly unless G_j v = x v. Thus some j_0 has lam_0 = +sig_+(Lam), forcing some
       k_0 != j_0 to satisfy <v, E_{k_0} v> <= -sig_+(Lam)/(m-1).
    6) Gap-Free Continuous Coverage of ALL Lam in [Lam_cert, Lam_interp(p, m)]:
       - Tail [Lam_s1, Lam_interp]: certified directly by Stage-1 L_all(Lam) < sig_+(Lam)/(m-1).
       - Core [Lam_cert, Lam_s1]: covered by exact contiguous intervals [Lam_k, Lam_{k+1}]
         certified via our Zero-Discrepancy Shared-Multiplier Convex-Combination NC-SOS Theorem:
         using constant valid weights (X_cap >= x_+(Lam_1), L_box >= L_all on [Lam_0, Lam_1])
         and affine Holden ideal g(mu) = g_0 - mu g_1 (mu = Lam for p=6/5,5/4,3/2; mu = Lam^2
         for p=5/3), a SINGLE shared ideal multiplier vector lam paired with endpoint PSD Gram
         tuples (Z^{(0)}, Z^{(1)}) satisfies the exact convex-combination identity at EVERY
         mu(t) = (1-t)mu_0 + t*mu_1 with IDENTICALLY ZERO quadratic discrepancy!
         Certifying just TWO interval Cholesky checks (Z0^{(0)} > 0 and Z0^{(1)} > 0) plus
         max(Psi_0, Psi_1) < sig_+(Lam_0)/(m-1) proves NO finite-dimensional solution exists
         for ANY real Lam in [Lam_0, Lam_1]!
         (Valid over C^n since real symmetric PSD G_a + Hermitian PSD W_a is Hermitian PSD
         and Re<v, w v> = Re<v, w^* v>!)
================================================================================
"""

import heapq
import time
from itertools import product
import mpmath as mp
from mpmath import iv

# Untrusted oracle libraries (STRICTLY confined to `oracle_*` functions in Section A!)
import numpy as np
from scipy.optimize import brentq, least_squares, linprog


# ==============================================================================
# SECTION A: UNTRUSTED NUMERICAL ORACLES (ONLY GENERATE CANDIDATE WITNESSES!)
# ==============================================================================
def _oracle_sym_pow(M, power):
    M = 0.5 * (M + M.T)
    ev, q = np.linalg.eigh(M)
    if ev[0] <= 1e-18:
        return None
    return (q * (ev ** power)) @ q.T


def _oracle_roots_kappa(Lam, kappa):
    x_min = (kappa - 1.0) / kappa
    f = lambda x: (1.0 + x) ** (2.0 * kappa - 1.0) - Lam * (x ** (kappa - 1.0))
    if f(x_min) >= 0:
        return None
    xm = brentq(f, 1e-15, x_min, xtol=1e-15, rtol=1e-15)
    hi = max(2.0, x_min * 2.0)
    while f(hi) < 0:
        hi *= 2.0
    xp = brentq(f, x_min, hi, xtol=1e-15, rtol=1e-15)
    return xp, xm, (xp ** (kappa - 1.0)) * (xp - 1.0), (xm ** (kappa - 1.0)) * (xm - 1.0)


def _oracle_scalar_1x1_Lam(kappa, m):
    x_min = (kappa - 1.0) / kappa
    Lam_min = ((1.0 + x_min) ** (2.0 * kappa - 1.0)) / (x_min ** (kappa - 1.0))
    def eq(Lam):
        r = _oracle_roots_kappa(Lam, kappa)
        return -1e3 if r is None else r[2] + (m - 1.0) * r[3]
    lo = Lam_min * (1.0 + 1e-12)
    hi = Lam_min * 2.0
    while eq(hi) < 0:
        hi *= 2.0
    return brentq(eq, lo, hi, xtol=1e-15, rtol=1e-15)


def oracle_build_lower_bound_witness(p_num, p_den, a_int, b_int, m, r, L_dep):
    """Untrusted oracle: builds candidate SPD matrices T_0..T_{m-1} and R_0 as exact mp.mpf lists."""
    p = p_num / p_den
    kappa = p / (2.0 * (p - 1.0))
    q_root = kappa / a_int
    Lam1 = _oracle_scalar_1x1_Lam(kappa, m)
    xp1, xm1, _, _ = _oracle_roots_kappa(Lam1, kappa)

    def solve_r(cr, Lam0, d0, X0):
        triu = np.triu_indices(cr)
        def unpack(x):
            Lam = x[0]
            d = np.concatenate([[1.0], np.exp(x[1:cr])])
            X = np.zeros((cr, cr)); X[triu] = x[cr:]
            X = X + X.T - np.diag(np.diag(X))
            return Lam, d, X
        def res(x):
            Lam, d, X = unpack(x)
            rt = _oracle_roots_kappa(Lam, kappa)
            if rt is None:
                return np.full(cr * (cr + 1), 1e3)
            xp, xm, sigp, _ = rt
            sd = np.sqrt(d); H = (sd[:, None] * X) * sd[None, :]; D = np.diag(d)
            G = (sd[:, None] * H) * sd[None, :]
            Mp = _oracle_sym_pow(D + H, 2.0 * kappa - 1.0)
            Gkm1 = _oracle_sym_pow(G, kappa - 1.0)
            Gk = _oracle_sym_pow(G, kappa)
            if Mp is None or Gkm1 is None or Gk is None:
                return np.full(cr * (cr + 1), 1e3)
            R1 = Mp - Lam * ((sd[:, None] * Gkm1) * sd[None, :])
            targ = sigp * (d ** (2.0 * kappa)); targ[0] = -sigp / (m - 1.0)
            R2 = Gk - (d[:, None] * Gkm1) * d[None, :] - np.diag(targ)
            w1 = 1.0 / np.outer(d ** (kappa - 0.5), d ** (kappa - 0.5))
            w2 = 1.0 / np.outer(d ** kappa, d ** kappa)
            return np.concatenate([(R1 * w1)[triu], (R2 * w2)[triu]])
        sol = least_squares(res, np.concatenate([[Lam0], np.log(d0[1:]), X0[triu]]),
                            xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=4000)
        Lam, d, X = unpack(sol.x)
        C = (Lam / (2.0 ** (2.0 * kappa - 1.0))) ** (1.0 / (2.0 * kappa))
        return Lam, C, d, X, float(np.linalg.norm(sol.fun))

    best = None
    d_grid = [0.005, 0.02, 0.08, 0.2, 0.35] if kappa < 1.4 else [0.05, 0.15, 0.25, 0.4]
    b_grid = [-0.01, -0.02, -0.04] if kappa < 1.4 else [-0.1, -0.2, -0.3]
    for dt in d_grid:
        for bt in b_grid:
            X0 = np.array([[xm1 * 1.1, bt], [bt, 0.35 * xp1]])
            if np.linalg.eigvalsh(X0)[0] <= 1e-6:
                continue
            r2 = solve_r(2, Lam1 * 1.0001, np.array([1.0, dt]), X0)
            if r2[4] < 1e-10 and abs(r2[3][0, 1]) > 1e-6:
                if best is None or r2[1] > best[1]:
                    best = r2
    assert best is not None
    Lam_p, C_p, d_p, X_p, _ = best
    for cr in range(3, r + 1):
        ratio_last = d_p[-1] / d_p[-2] if cr > 3 else d_p[-1] * 1.3
        d0 = np.concatenate([d_p, [d_p[-1] * min(0.8, max(0.05, ratio_last))]])
        X0 = np.zeros((cr, cr))
        X0[:cr - 1, :cr - 1] = X_p
        X0[cr - 1, cr - 1] = X_p[cr - 2, cr - 2]
        for j in range(1, cr - 1):
            X0[j, cr - 1] = X0[cr - 1, j] = X_p[j - 1, cr - 2]
        X0[0, cr - 1] = X0[cr - 1, 0] = X_p[0, cr - 2] * 0.2
        Lam_c, C_c, d_c, X_c, err_c = solve_r(cr, Lam_p, d0, X0)
        if err_c < 1e-8 and C_c >= C_p - 1e-12:
            Lam_p, C_p, d_p, X_p = Lam_c, C_c, d_c, X_c
        else:
            break

    xp, xm, _, _ = _oracle_roots_kappa(Lam_p, kappa)
    G_rg = (d_p[:, None] * X_p) * d_p[None, :]
    T_rg = _oracle_sym_pow(G_rg, q_root)
    xp_T = xp ** q_root; xm_T = xm ** q_root; scale_exp = 2.0 * q_root

    nodes = [(1.0, 0, m - 1)]
    blocks = [[] for _ in range(m)]
    blocks[m - 1].append(([0], 1.0, "root+"))
    queue = [0]
    while queue:
        u = queue.pop(0)
        sc_u, dep_u, done_j = nodes[u]
        for j in range(m):
            if j == done_j:
                continue
            if dep_u < L_dep:
                blk = [u]
                for i in range(1, len(d_p)):
                    v = len(nodes)
                    nodes.append((sc_u * d_p[i], dep_u + 1, j))
                    blk.append(v)
                    queue.append(v)
                blocks[j].append((blk, sc_u, "block"))
            else:
                blocks[j].append(([u], sc_u, "leaf-"))
    N = len(nodes)
    Ts_mp = []
    for j in range(m):
        Tj = np.zeros((N, N))
        for blk, sc, kind in blocks[j]:
            sc_T = sc ** scale_exp
            if kind == "root+":
                Tj[blk[0], blk[0]] = sc_T * xp_T
            elif kind == "leaf-":
                Tj[blk[0], blk[0]] = sc_T * xm_T
            else:
                Tj[np.ix_(blk, blk)] = sc_T * T_rg
        Tj = 0.5 * (Tj + Tj.T)
        Tm = mp.matrix(N, N)
        for i1 in range(N):
            for i2 in range(i1, N):
                v = mp.mpf(f"{float(Tj[i1, i2]):.17g}")
                Tm[i1, i2] = Tm[i2, i1] = v
        Ts_mp.append(Tm)

    M_mp = mp.zeros(N, N); N_mp = mp.zeros(N, N)
    for Tm in Ts_mp:
        M_mp += Tm ** a_int
        N_mp += Tm ** b_int
    En, Qn = mp.eigh(N_mp)
    N_half = Qn * mp.diag([mp.sqrt(e) for e in En]) * Qn.T
    N_mhalf = Qn * mp.diag([1 / mp.sqrt(e) for e in En]) * Qn.T
    G_mp = N_half * M_mp * N_half
    G_mp = (G_mp + G_mp.T) / 2
    Eg, Qg = mp.eigh(G_mp)
    G_half = Qg * mp.diag([mp.sqrt(e) for e in Eg]) * Qg.T
    K_mp = N_mhalf * G_half * N_mhalf
    K_mp = (K_mp + K_mp.T) / 2
    Ek, Qk = mp.eigh(K_mp)
    R0_mp = Qk * mp.diag([mp.sqrt(e) for e in Ek]) * Qk.T
    R0_mp = (R0_mp + R0_mp.T) / 2

    Ts_exact = [[[Ts_mp[j][i1, i2] for i2 in range(N)] for i1 in range(N)] for j in range(m)]
    R0_exact = [[R0_mp[i1, i2] for i2 in range(N)] for i1 in range(N)]
    return Ts_exact, R0_exact, N


def oracle_stage1_lp_multipliers(Lam_lo_mp, Lam_hi_mp, k_num, k_den):
    """Untrusted oracle: finds candidate 5-scalar multipliers (a, b, c, lam1) for Lam in [Lam_lo, Lam_hi]."""
    Lam_mid = float(0.5 * (Lam_lo_mp + Lam_hi_mp))
    Lam_hi = float(Lam_hi_mp)
    kappa = k_num / k_den
    ts = np.unique(np.concatenate([
        np.geomspace(1e-2, 0.99, 250),
        np.linspace(1.0, 3.5, 500),
        np.geomspace(3.5, 20.0, 250),
    ]))
    gs = np.unique(np.concatenate([
        np.geomspace(1e-6, 2.5, 800),
        np.geomspace(2.5, 20.0, 250),
    ]))
    A1 = np.column_stack([ts, ts**(2*kappa - 1), ts**(2*kappa), -1.0/ts, -np.ones_like(ts), np.zeros_like(ts)])
    b1 = np.zeros(len(ts))
    gkm1 = gs**(kappa - 1); gk = gs**kappa
    # Enforce G-inequality at BOTH Lam_lo and Lam_hi so multipliers are safe across the whole box!
    Lam_lo = float(Lam_lo_mp)
    A2_lo = np.column_stack([-gs, -Lam_lo*gkm1, -Lam_lo*(gkm1 + gk), np.zeros_like(gs), np.zeros_like(gs), -np.ones_like(gs)])
    A2_hi = np.column_stack([-gs, -Lam_hi*gkm1, -Lam_hi*(gkm1 + gk), np.zeros_like(gs), np.zeros_like(gs), -np.ones_like(gs)])
    b2 = gk - gkm1
    A2 = np.vstack([A2_lo, A2_hi, np.array([0.0, 0.0, 0.0, 0.0, 0.0, -1.0])])
    b2_all = np.concatenate([b2, b2, [0.0]])
    c_obj = np.array([-1.0, 0.0, 0.0, 1.0, 1.0, 1.0])
    # Strictly ensure 1 + c*Lam_hi > 0!
    c_min = -1.0 / Lam_hi + max(1e-6, 1e-4 / Lam_hi)
    bounds = [(None, None), (None, None), (c_min, -1e-9), (1e-9, None), (None, None), (None, None)]
    res = linprog(c_obj, A_ub=np.vstack([A1, A2]), b_ub=np.concatenate([b1, b2_all]), bounds=bounds, method="highs")
    assert res.success, f"Stage-1 LP failed on [{Lam_lo}, {Lam_hi}]: {res.message}"
    a, b, c, lam1 = res.x[:4]
    return tuple(mp.mpf(f"{float(v):.17g}") for v in (a, b, c, lam1))


def _poly_iv_to_f64(p_iv):
    return {k: float(mp.mpf(v.mid)) for k, v in p_iv.items()}


def oracle_solve_interval_sos(struct, p_obj_iv, g0_iv, g1_iv, h_list_iv, weights_iv, mu0_iv, mu1_iv, eps_I_f, max_iter=80):
    """
    Untrusted oracle: solves the Joint Shared-Multiplier Interval SDP in float64 to obtain
    a SINGLE shared ideal multiplier vector `lam_shared` and TWO endpoint PSD Gram tuples
    (Z^{(0)}, Z^{(1)}) simultaneously valid at mu0 and mu1 (guaranteeing IDENTICALLY ZERO
    quadratic discrepancy Delta_quad == 0 across ALL mu in [mu0, mu1]!).
    Converts all candidate witness entries to exact mp.mpf before leaving Section A!
    """
    n_var = struct["n_var"]; w2i = struct["w2i"]
    blocks_wlists = struct["blocks_wlists"]; id_meta = struct["id_meta"]

    def p2v(pf):
        v = np.zeros(n_var)
        for w, c in pf.items():
            v[w2i[canon_w(w)]] += c
        return v

    p_obj_f = _poly_iv_to_f64(p_obj_iv)
    g0_f = _poly_iv_to_f64(g0_iv); g1_f = _poly_iv_to_f64(g1_iv)
    h_list_f = [_poly_iv_to_f64(ph) for ph in h_list_iv]
    weights_f = [_poly_iv_to_f64(pw) for pw in weights_iv]

    c_obj_orig = p2v(p_obj_f)
    a_norm = p2v({(): 1.0})

    # Precompute constant block tensors raw_blocks (identical at mu0 and mu1!)
    raw_blocks = []
    for idx_b, wlist in enumerate(blocks_wlists):
        pW = weights_f[idx_b]
        sz = len(wlist)
        F_t = np.zeros((n_var, sz, sz))
        for r_idx, wu in enumerate(wlist):
            wur = wu[::-1]
            for c_idx, wv in enumerate(wlist):
                p = {}
                for k, v in pW.items():
                    kk = wur + k + wv
                    p[kk] = p.get(kk, 0.0) + v
                F_t[:, r_idx, c_idx] = p2v(p)
        F_t = 0.5 * (F_t + np.swapaxes(F_t, 1, 2))
        raw_blocks.append((sz, F_t))

    sz0 = raw_blocks[0][0]
    nb1 = len(raw_blocks)
    trace_F0 = np.einsum("vii->v", raw_blocks[0][1])
    c_single = c_obj_orig - eps_I_f * trace_F0
    c_joint = np.concatenate([c_single, c_single])

    def build_A_split(mu_f):
        pg_f = dict(g0_f)
        for k, v in g1_f.items():
            pg_f[k] = pg_f.get(k, 0.0) - mu_f * v
        all_ideals_f = [pg_f] + h_list_f
        rows_g, rows_h = [], []
        for (g_idx, wl, wr) in id_meta:
            pg = all_ideals_f[g_idx]
            p = {}
            for k, v in pg.items():
                kk = wl + k + wr
                p[kk] = p.get(kk, 0.0) + v
            if g_idx == 0:
                rows_g.append(p2v(p))
            else:
                rows_h.append(p2v(p))
        return np.array(rows_g), (np.array(rows_h) if rows_h else np.zeros((0, n_var)))

    mu0_f = float(mp.mpf(mu0_iv.mid))
    mu1_f = float(mp.mpf(mu1_iv.mid))
    Ag0, Ah = build_A_split(mu0_f)
    Ag1, _ = build_A_split(mu1_f)
    n_g = Ag0.shape[0]; n_h = Ah.shape[0]
    # Shared g(mu) constraint: Ag0 y0 + Ag1 y1 = 0 (=> shared lam_g, ZERO quadratic error!)
    # Separate mu-independent h constraints: Ah y0 = 0 AND Ah y1 = 0 (=> tighter AND much smaller n_free!)
    Z_h = np.zeros((n_h, n_var))
    A_id_joint = np.vstack([
        np.hstack([Ag0, Ag1]),
        np.hstack([Ah, Z_h]),
        np.hstack([Z_h, Ah]),
    ])
    a_joint = np.concatenate([a_norm, a_norm])

    U_eq, s_eq, _ = np.linalg.svd(A_id_joint, full_matrices=False)
    rank_eq = int(np.sum(s_eq > 1e-10 * s_eq[0]))
    A_full = np.vstack([U_eq[:, :rank_eq].T @ A_id_joint, a_joint[None, :]])
    b_full = np.zeros(rank_eq + 1); b_full[-1] = 1.0

    Uf, sf, Vtf = np.linalg.svd(A_full, full_matrices=True)
    rk_f = int(np.sum(sf > 1e-10 * sf[0]))
    y0 = Vtf[:rk_f].T @ ((Uf[:, :rk_f].T @ b_full) / sf[:rk_f])
    N_null = Vtf[rk_f:].T
    n_free = N_null.shape[1]

    blocks = []
    for side in (0, 1):
        sl = slice(0, n_var) if side == 0 else slice(n_var, 2 * n_var)
        y0_s = y0[sl]
        Nn_s = N_null[sl, :]
        for sz, F_t in raw_blocks:
            F_flat = F_t.reshape(n_var, sz * sz)
            B0 = (y0_s @ F_flat).reshape(sz, sz)
            Bz_flat = Nn_s.T @ F_flat
            Bz = Bz_flat.reshape(n_free, sz, sz)
            sc = max(np.linalg.norm(B0), np.max(np.linalg.norm(Bz_flat, axis=1)), 1e-12)
            blocks.append((sz, B0 / sc, Bz / sc, Bz_flat / sc, sc))

    c0 = float(c_joint @ y0); g = N_null.T @ c_joint
    n_blocks = len(blocks); tot_n = sum(b[0] for b in blocks)
    z = np.zeros(n_free)
    S_list = [np.eye(b[0]) for b in blocks]
    X_list = [np.eye(b[0]) for b in blocks]

    def max_step_psd(M_list, dM_list):
        amax = 1.0
        for M, dM in zip(M_list, dM_list):
            ev, evec = np.linalg.eigh(M)
            Li = evec * (1.0 / np.sqrt(np.maximum(ev, 1e-30)))
            G = Li.T @ dM @ Li; G = 0.5 * (G + G.T)
            lm = float(np.linalg.eigvalsh(G)[0])
            if lm < -1e-16:
                amax = min(amax, -1.0 / lm)
        return amax

    best_snap = None; best_score = 1e9
    min_dres = 1e9; min_dres_snap = None
    target_mu = max(1e-10, 0.005 * eps_I_f)
    dres_tol = max(1e-9, 0.15 * eps_I_f)

    for _ in range(1, max_iter + 1):
        Rp_list = []; rd = g.copy(); mu = 0.0
        for a, (rk, B0, Bz, Bzf, _) in enumerate(blocks):
            Rp = S_list[a] - (B0 + (z @ Bzf).reshape(rk, rk))
            Rp = 0.5 * (Rp + Rp.T)
            Rp_list.append(Rp)
            rd -= Bzf @ X_list[a].ravel()
            mu += float(np.sum(S_list[a] * X_list[a]))
        mu /= tot_n; d_res = float(np.linalg.norm(rd))
        d_obj = float(c0 - sum(float(np.sum(b[1] * X_list[a])) for a, b in enumerate(blocks)))
        if d_res < min_dres:
            min_dres = d_res; min_dres_snap = ([X.copy() for X in X_list], -d_obj)
        if d_res < dres_tol and (-d_obj) < best_score:
            best_score = -d_obj; best_snap = ([X.copy() for X in X_list], -d_obj)
        if best_snap is not None and d_res < min(1e-8, 0.05 * eps_I_f) and mu < target_mu:
            break
        if best_snap is not None and mu < 1e-11 and d_res > 20.0 * dres_tol:
            break

        M_s = np.zeros((n_free, n_free)); Sinv_l = []
        for a, (rk, B0, Bz, Bzf, _) in enumerate(blocks):
            ev, V = np.linalg.eigh(S_list[a])
            Sinv = (V * (1.0 / np.maximum(ev, 1e-30))) @ V.T
            Sinv_l.append(Sinv)
            SB = (Sinv @ Bz).reshape(n_free, rk * rk)
            BX = (Bz @ X_list[a]).reshape(n_free, rk * rk)
            M_s += SB @ BX.T
        M_s = 0.5 * (M_s + M_s.T)
        d_diag = np.sqrt(np.maximum(np.diag(M_s), 1e-30))
        M_n = (M_s / d_diag[:, None]) / d_diag[None, :] + 1e-14 * np.eye(n_free)

        def solve_M(rhs):
            try:
                return np.linalg.solve(M_n, rhs / d_diag) / d_diag
            except np.linalg.LinAlgError:
                return np.linalg.lstsq(M_n, rhs / d_diag, rcond=1e-14)[0] / d_diag

        def solve_dir(sv, dSa=None, dXa=None):
            rhs = -rd.copy(); Rc_l = []
            for a, (rk, B0, Bz, Bzf, _) in enumerate(blocks):
                Rc = sv * mu * np.eye(rk) - S_list[a] @ X_list[a]
                if dSa is not None:
                    Rc = Rc - dSa[a] @ dXa[a]
                Rc_l.append(Rc)
                W = Sinv_l[a] @ (Rc + Rp_list[a] @ X_list[a]); W = 0.5 * (W + W.T)
                rhs += Bzf @ W.ravel()
            dz = solve_M(rhs); dS_l, dX_l = [], []
            for a, (rk, B0, Bz, Bzf, _) in enumerate(blocks):
                dS = (dz @ Bzf).reshape(rk, rk) - Rp_list[a]; dS = 0.5 * (dS + dS.T)
                dX = Sinv_l[a] @ (Rc_l[a] - dS @ X_list[a]); dX = 0.5 * (dX + dX.T)
                dS_l.append(dS); dX_l.append(dX)
            return dz, dS_l, dX_l

        _, dSa, dXa = solve_dir(0.0)
        apa = min(1.0, max_step_psd(S_list, dSa)); ada = min(1.0, max_step_psd(X_list, dXa))
        mua = sum(float(np.sum((S_list[a] + apa * dSa[a]) * (X_list[a] + ada * dXa[a]))) for a in range(n_blocks)) / tot_n
        sig = float(np.clip((mua / max(mu, 1e-30)) ** 3, 1e-4, 0.8))
        dz, dS, dX = solve_dir(sig, dSa, dXa)
        ap = min(1.0, 0.96 * max_step_psd(S_list, dS)); ad = min(1.0, 0.96 * max_step_psd(X_list, dX))
        z += ap * dz
        for a in range(n_blocks):
            S_list[a] = 0.5 * ((S_list[a] + ap * dS[a]) + (S_list[a] + ap * dS[a]).T)
            X_list[a] = 0.5 * ((X_list[a] + ad * dX[a]) + (X_list[a] + ad * dX[a]).T)

    X_use = (best_snap if best_snap is not None else min_dres_snap)[0]
    Z0_raw = [0.5 * (X_use[a] + X_use[a].T) / blocks[a][4] for a in range(nb1)]
    Z1_raw = [0.5 * (X_use[nb1 + a] + X_use[nb1 + a].T) / blocks[nb1 + a][4] for a in range(nb1)]
    Z0_raw[0] += eps_I_f * np.eye(sz0)
    Z1_raw[0] += eps_I_f * np.eye(sz0)
    psos0 = sum(raw_blocks[b][1].reshape(n_var, -1) @ Z0_raw[b].ravel() for b in range(nb1))
    psos1 = sum(raw_blocks[b][1].reshape(n_var, -1) @ Z1_raw[b].ravel() for b in range(nb1))

    M_ls = np.hstack([A_id_joint.T, -a_joint[:, None]])
    rhs_ls = np.concatenate([c_obj_orig - psos0, c_obj_orig - psos1])
    sol_ls, _, _, _ = np.linalg.lstsq(M_ls, rhs_ls, rcond=1e-12)
    lam_g = sol_ls[:n_g]
    lam_h0 = sol_ls[n_g:n_g + n_h]
    lam_h1 = sol_ls[n_g + n_h:n_g + 2 * n_h]
    # Reassemble full id_meta order (shared lam_g for g_idx==0; endpoint-specific lam_h for g_idx>=1!)
    lam_0_mp, lam_1_mp = [], []
    ig, ih = 0, 0
    for (g_idx, _, _) in id_meta:
        if g_idx == 0:
            v = mp.mpf(f"{float(lam_g[ig]):.17g}")
            lam_0_mp.append(v); lam_1_mp.append(v)
            ig += 1
        else:
            lam_0_mp.append(mp.mpf(f"{float(lam_h0[ih]):.17g}"))
            lam_1_mp.append(mp.mpf(f"{float(lam_h1[ih]):.17g}"))
            ih += 1

    def pack_Z(Z_raw):
        Z0_mp = [[mp.mpf(f"{float(0.5*(Z_raw[0][i,j]+Z_raw[0][j,i])):.17g}") for j in range(sz0)] for i in range(sz0)]
        factors_mp = [None]
        for a in range(1, nb1):
            ev, V = np.linalg.eigh(0.5 * (Z_raw[a] + Z_raw[a].T))
            facs = []
            for r_i in range(len(ev)):
                if ev[r_i] > 1e-15:
                    facs.append((
                        mp.mpf(f"{float(ev[r_i]):.17g}"),
                        [mp.mpf(f"{float(V[i, r_i]):.17g}") for i in range(len(ev))],
                    ))
            factors_mp.append(facs)
        return Z0_mp, factors_mp

    Z0_0, fac_0 = pack_Z(Z0_raw)
    Z0_1, fac_1 = pack_Z(Z1_raw)
    return (Z0_0, fac_0, lam_0_mp, Z0_1, fac_1, lam_1_mp)


# ==============================================================================
# SECTION B: 100% PURE ZERO-FLOAT mpmath.iv VERIFIERS (ZERO numpy, ZERO float!)
# ==============================================================================
def strip_outer_0(w):
    i, j = 0, len(w)
    while i < j and w[i] == 0:
        i += 1
    while j > i and w[j - 1] == 0:
        j -= 1
    return w[i:j]


def canon_w(w):
    s = strip_outer_0(w)
    return min(s, s[::-1])


def gen_words(n_gen, max_len):
    out = []
    for L in range(max_len + 1):
        out.extend(product(range(n_gen), repeat=L))
    return out


def reduced_words_k(n_gen, max_len):
    ws = [()]
    for L in range(1, max_len + 1):
        for w in product(range(n_gen), repeat=L):
            if w[-1] != 0:
                ws.append(w)
    return ws


def padd_iv(a, b, sc=1):
    out = dict(a)
    for k, v in b.items():
        out[k] = out[k] + sc * v if k in out else sc * v
    return out


def pmul_iv(a, b):
    out = {}
    for k1, v1 in a.items():
        for k2, v2 in b.items():
            k = k1 + k2
            out[k] = out[k] + v1 * v2 if k in out else v1 * v2
    return out


def ppow_iv(a, n):
    res = {(): iv.mpf(1)}
    for _ in range(n):
        res = pmul_iv(res, a)
    return res


def iv_matmul(A, B):
    n = len(A)
    C = [[iv.mpf(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        Ai = A[i]; Ci = C[i]
        for k in range(n):
            aik = Ai[k]
            if aik == 0:
                continue
            Bk = B[k]
            for j in range(n):
                Ci[j] += aik * Bk[j]
    return C


def iv_matpow(A, k):
    n = len(A)
    res = [[iv.mpf(1 if i == j else 0) for j in range(n)] for i in range(n)]
    base = A; e = k
    while e > 0:
        if e & 1:
            res = iv_matmul(res, base)
        e >>= 1
        if e > 0:
            base = iv_matmul(base, base)
    return res


def iv_symmetrize(A):
    """Exact enclosure of a mathematically symmetric matrix: (A + A^T)/2 encloses every real A = A^T."""
    n = len(A)
    half = iv.mpf(1) / iv.mpf(2)
    S = [[None] * n for _ in range(n)]
    for i in range(n):
        S[i][i] = A[i][i]
        for j in range(i + 1, n):
            v = half * (A[i][j] + A[j][i])
            S[i][j] = S[j][i] = v
    return S


def iv_cholesky_pd(M):
    """100% pure mpmath.iv Cholesky certification that every symmetric real matrix in M is PD."""
    n = len(M)
    L = [[iv.mpf(0) for _ in range(n)] for _ in range(n)]
    min_diag = None
    for i in range(n):
        for j in range(i):
            s = M[i][j]
            for k in range(j):
                s -= L[i][k] * L[j][k]
            L[i][j] = s / L[j][j]
        s = M[i][i]
        for k in range(i):
            s -= L[i][k] * L[i][k]
        if mp.mpf(s.a) <= 0:
            return False, mp.mpf(s.a)
        L[i][i] = iv.sqrt(s)
        da = mp.mpf(L[i][i].a)
        if min_diag is None or da < min_diag:
            min_diag = da
    return True, min_diag


# --- B1: Pure mpmath.iv Unified Kubo-Ando / Fourier Lower Bound Verifier ---
def _iv_certify_tr_pow(Y_iv, p_iv):
    """Zero-float Weyl + Ostrowski upper bound on Tr(Y^p) (valid for arbitrary multiplicities!)."""
    n = len(Y_iv)
    for i in range(n):
        for j in range(i + 1, n):
            assert Y_iv[i][j] == Y_iv[j][i], "Y_iv asymmetric!"
    Y_mp = mp.matrix([[mp.mpf(Y_iv[i][j].mid) for j in range(n)] for i in range(n)])
    _, Q_mp = mp.eigh(Y_mp)
    Q_iv = [[iv.mpf(Q_mp[i, j]) for j in range(n)] for i in range(n)]
    QT_iv = [[Q_iv[j][i] for j in range(n)] for i in range(n)]

    QTQ = iv_matmul(QT_iv, Q_iv)
    eps_q = mp.mpf(0)
    for i in range(n):
        row_s_iv = iv.mpf(0)
        for j in range(n):
            d = QTQ[i][j] - (1 if i == j else 0)
            row_s_iv += iv.mpf(max(abs(mp.mpf(d.a)), abs(mp.mpf(d.b))))
        row_ub = mp.mpf(row_s_iv.b)
        if row_ub > eps_q:
            eps_q = row_ub
    assert eps_q < mp.mpf("1e-15"), f"Orthogonality failed: {eps_q}"

    W = iv_matmul(QT_iv, iv_matmul(Y_iv, Q_iv))
    eta = mp.mpf(0)
    for i in range(n):
        row_off_iv = iv.mpf(0)
        for j in range(n):
            if i != j:
                row_off_iv += iv.mpf(max(abs(mp.mpf(W[i][j].a)), abs(mp.mpf(W[i][j].b))))
        row_off_ub = mp.mpf(row_off_iv.b)
        if row_off_ub > eta:
            eta = row_off_ub

    inv_orth = iv.mpf(1) / (iv.mpf(1) - iv.mpf(eps_q))
    eta_iv = iv.mpf(eta)
    tr_hi_iv = iv.mpf(0)
    for i in range(n):
        lam_hi_iv = (iv.mpf(mp.mpf(W[i][i].b)) + eta_iv) * inv_orth
        assert mp.mpf(lam_hi_iv.a) > 0
        tr_hi_iv += lam_hi_iv ** p_iv
    return mp.mpf(tr_hi_iv.b)


def certify_lower_bound_iv(p_num, p_den, a_int, b_int, Ts_exact, R0_exact):
    """100% pure zero-float mpmath.iv Kubo-Ando lower bound certifier."""
    assert p_num * (a_int + b_int) == 2 * a_int * p_den
    m = len(Ts_exact); N = len(R0_exact)
    p_iv = iv.mpf(p_num) / iv.mpf(p_den)
    inv_p_iv = iv.mpf(p_den) / iv.mpf(p_num)

    Ts_iv = []
    for j in range(m):
        for i1 in range(N):
            for i2 in range(i1 + 1, N):
                assert Ts_exact[j][i1][i2] == Ts_exact[j][i2][i1], "T_j asymmetric!"
        Tj = [[iv.mpf(Ts_exact[j][i1][i2]) for i2 in range(N)] for i1 in range(N)]
        ok_t, _ = iv_cholesky_pd(Tj)
        assert ok_t, f"T_{j} not certified PD!"
        Ts_iv.append(Tj)

    for i1 in range(N):
        for i2 in range(i1 + 1, N):
            assert R0_exact[i1][i2] == R0_exact[i2][i1], "R0 asymmetric!"
    R0_iv = [[iv.mpf(R0_exact[i1][i2]) for i2 in range(N)] for i1 in range(N)]
    ok_r, _ = iv_cholesky_pd(R0_iv)
    assert ok_r, "R0 not certified PD!"
    K0_iv = iv_matmul(R0_iv, R0_iv)

    M_iv = [[iv.mpf(0) for _ in range(N)] for _ in range(N)]
    N_iv = [[iv.mpf(0) for _ in range(N)] for _ in range(N)]
    Num_iv = iv.mpf(0)
    Tbs_iv = []
    for j in range(m):
        Ta = iv_matpow(Ts_iv[j], a_int)
        Tb = iv_matpow(Ts_iv[j], b_int)
        Tbs_iv.append(Tb)
        for i1 in range(N):
            Num_iv += Ta[i1][i1]
            for i2 in range(N):
                M_iv[i1][i2] += Ta[i1][i2]
                N_iv[i1][i2] += Tb[i1][i2]

    KNK = iv_symmetrize(iv_matmul(K0_iv, iv_matmul(N_iv, K0_iv)))
    M_iv = iv_symmetrize(M_iv)
    tau_cert = None
    for tau_s in ["1e-18", "1e-15", "1e-12", "1e-10", "1e-8", "1e-6"]:
        tau_iv = iv.mpf(tau_s)
        sc = (iv.mpf(1) + tau_iv) ** 2
        Diff = [[sc * KNK[i1][i2] - M_iv[i1][i2] for i2 in range(N)] for i1 in range(N)]
        ok_d, _ = iv_cholesky_pd(Diff)
        if ok_d:
            tau_cert = tau_iv
            break
    assert tau_cert is not None, "Kubo-Ando Cholesky certification failed!"

    sum_tr_iv = iv.mpf(0)
    for j in range(m):
        Yj = iv_symmetrize(iv_matmul(R0_iv, iv_matmul(Tbs_iv[j], R0_iv)))
        sum_tr_iv += iv.mpf(_iv_certify_tr_pow(Yj, p_iv))

    Den_ub = mp.mpf((((iv.mpf(1) + tau_cert) ** p_iv) * sum_tr_iv).b)
    Num_lo = mp.mpf(Num_iv.a)
    C_lb = mp.mpf(((iv.mpf(Num_lo) / iv.mpf(Den_ub)) ** inv_p_iv).a)
    return C_lb, tau_cert


# --- B2: Pure mpmath.iv Root & Universal 5-Scalar Stage-1 Verifier ---
def iv_certify_xplus(Lam_mp, k_num, k_den):
    """
    Pure zero-float mpmath.iv enclosure of the UNIQUE upper positive root x_+(Lam) > (k-1)/k
    of (1+x)^{2k-1} = Lam * x^{k-1}, plus sig_+(Lam) = x_+^{k-1} * (x_+ - 1).
    """
    assert k_num > k_den > 0, "Requires kappa = k_num / k_den > 1!"
    Lam_iv = iv.mpf(Lam_mp)
    k_iv = iv.mpf(k_num) / iv.mpf(k_den)
    twokm1 = 2 * k_iv - 1
    km1 = k_iv - 1
    k_m = mp.mpf(k_num) / mp.mpf(k_den)
    x_min_m = (k_m - 1) / k_m

    # Untrusted point Newton in mpmath to locate root center
    x_m = mp.mpf("1.2")
    for _ in range(80):
        fv = (1 + x_m) ** (2 * k_m - 1) - Lam_mp * (x_m ** (k_m - 1))
        dfv = (2 * k_m - 1) * ((1 + x_m) ** (2 * k_m - 2)) - Lam_mp * (k_m - 1) * (x_m ** (k_m - 2))
        x_m -= fv / dfv
        if x_m <= x_min_m:
            x_m = mp.mpf("1.5")

    rad = mp.mpf("1e-32")
    xl = x_m - rad; xh = x_m + rad
    assert xl > mp.mpf(1), "x_+ must exceed 1 (Lam > 2^{2k-1})!"
    fl = (1 + iv.mpf(xl)) ** twokm1 - Lam_iv * (iv.mpf(xl) ** km1)
    fh = (1 + iv.mpf(xh)) ** twokm1 - Lam_iv * (iv.mpf(xh) ** km1)
    assert mp.mpf(fl.b) < 0 and mp.mpf(fh.a) > 0, "IVT sign change failed for x_+(Lam)!"
    # Uniqueness on ((k-1)/k, inf) follows from d/dx[(1+x)^{2k-1}/x^{k-1}] = (1+x)^{2k-2}/x^k * (k*x - (k-1)) > 0!
    xp_iv = iv.mpf([xl, xh])
    sigp_iv = (xp_iv ** km1) * (xp_iv - 1)
    return xp_iv, sigp_iv


def _iv_sup_1d(f_and_df, lo, hi, tol_str="1e-10", max_splits=500):
    assert lo < hi
    tol = mp.mpf(tol_str)
    def eval_box(xl, xh):
        xb = iv.mpf([xl, xh])
        xm = (xl + xh) / 2
        assert xl <= xm <= xh
        xm_iv = iv.mpf(xm)
        fm, _ = f_and_df(xm_iv)
        fb, dfb = f_and_df(xb)
        mv = fm + dfb * (xb - xm_iv)
        return max(mp.mpf(fm.a), mp.mpf(fb.a)), min(mp.mpf(fb.b), mp.mpf(mv.b))

    n_init = 24
    log_lo = mp.log(lo); log_hi = mp.log(hi)
    edges = [mp.exp(log_lo + (log_hi - log_lo) * k / n_init) for k in range(n_init + 1)]
    edges[0] = lo; edges[-1] = hi
    best_lo = None; heap = []
    for k in range(n_init):
        assert edges[k] < edges[k + 1]
        lv, hv = eval_box(edges[k], edges[k + 1])
        if best_lo is None or lv > best_lo:
            best_lo = lv
        heapq.heappush(heap, (-hv, k, edges[k], edges[k + 1], lv, hv))
    uid = n_init
    for _ in range(max_splits):
        _, _, xl, xh, lv, hv = heap[0]
        if hv - best_lo <= tol or (xh - xl) <= mp.mpf("1e-22") * max(mp.mpf(1), xh):
            break
        heapq.heappop(heap)
        xm = (xl + xh) / 2
        lv1, hv1 = eval_box(xl, xm)
        lv2, hv2 = eval_box(xm, xh)
        if lv1 > best_lo: best_lo = lv1
        if lv2 > best_lo: best_lo = lv2
        uid += 1; heapq.heappush(heap, (-hv1, uid, xl, xm, lv1, hv1))
        uid += 1; heapq.heappush(heap, (-hv2, uid, xm, xh, lv2, hv2))
    return heap[0][5]


def iv_certify_stage1_5scalar(Lam_iv, k_num, k_den, mults_mp):
    """
    100% zero-float mpmath.iv certification of Stage-1 upper bound L_all(Lam) over ALL (0, inf)
    simultaneously for EVERY Lam in Lam_iv (ZERO D <= I assumed!).
    """
    a_iv, b_iv, c_iv, l1_iv = (iv.mpf(x) for x in mults_mp)
    k_iv = iv.mpf(k_num) / iv.mpf(k_den)
    km1_iv = k_iv - 1; twok_iv = 2 * k_iv; twokm1_iv = twok_iv - 1; twokm2_iv = twok_iv - 2

    assert mp.mpf(l1_iv.a) > 0 and mp.mpf(c_iv.b) < 0
    alpha_G = iv.mpf(1) - (b_iv + c_iv) * Lam_iv
    beta_G = iv.mpf(1) + c_iv * Lam_iv
    assert mp.mpf(beta_G.a) > 0, "1 + c*Lam_iv must stay > 0 across entire Lam_iv!"

    def fM_and_df(tb):
        f = a_iv * tb + b_iv * (tb ** twokm1_iv) + c_iv * (tb ** twok_iv) - l1_iv / tb
        df = a_iv + b_iv * twokm1_iv * (tb ** twokm2_iv) + c_iv * twok_iv * (tb ** twokm1_iv) + l1_iv / (tb * tb)
        return f, df

    t_lo = mp.mpf("0.2")
    for _ in range(45):
        tb = iv.mpf([mp.mpf(0), t_lo])
        t2df = l1_iv + a_iv * (tb ** 2) + b_iv * twokm1_iv * (tb ** twok_iv) + c_iv * twok_iv * (tb ** (twok_iv + 1))
        if mp.mpf(t2df.a) > 0:
            break
        t_lo /= 2
    else:
        raise AssertionError("f_M small-t monotonicity failed!")

    t_hi = mp.mpf("4.0")
    for _ in range(45):
        u_hi = mp.mpf((iv.mpf(1) / iv.mpf(t_hi)).b)
        ub = iv.mpf([mp.mpf(0), u_hi])
        sdf = c_iv * twok_iv + b_iv * twokm1_iv * ub + a_iv * (ub ** twokm1_iv) + l1_iv * (ub ** (twok_iv + 1))
        if mp.mpf(sdf.b) < 0:
            break
        t_hi *= 2
    else:
        raise AssertionError("f_M large-t monotonicity failed!")

    sup_M_ub = _iv_sup_1d(fM_and_df, t_lo, t_hi)

    def fG_and_df(gb):
        f = alpha_G * (gb ** km1_iv) - beta_G * (gb ** k_iv) - a_iv * gb
        df = alpha_G * km1_iv * (gb ** (k_iv - 2)) - beta_G * k_iv * (gb ** km1_iv) - a_iv
        return f, df

    g_hi = mp.mpf("4.0")
    for _ in range(45):
        u_hi = mp.mpf((iv.mpf(1) / iv.mpf(g_hi)).b)
        ub = iv.mpf([mp.mpf(0), u_hi])
        sdf = -beta_G * k_iv + alpha_G * km1_iv * ub - a_iv * (ub ** km1_iv)
        if mp.mpf(sdf.b) < 0:
            break
        g_hi *= 2
    else:
        raise AssertionError("f_G large-g monotonicity failed!")

    g_lo = mp.mpf("1e-4")
    small_g_ub = None
    if k_num < 2 * k_den and mp.mpf(alpha_G.a) > 0:
        for _ in range(55):
            gb = iv.mpf([mp.mpf(0), g_lo])
            s_df = alpha_G * km1_iv - beta_G * k_iv * gb - a_iv * (gb ** (iv.mpf(2) - k_iv))
            if mp.mpf(s_df.a) > 0:
                small_g_ub = mp.mpf(fG_and_df(iv.mpf(g_lo))[0].b)
                break
            g_lo /= 4
        assert small_g_ub is not None
    elif k_num > 2 * k_den and mp.mpf(a_iv.a) > 0:
        for _ in range(55):
            gb = iv.mpf([mp.mpf(0), g_lo])
            f_over_g = -a_iv + alpha_G * (gb ** (k_iv - 2)) - beta_G * (gb ** km1_iv)
            if mp.mpf(f_over_g.b) < 0:
                small_g_ub = mp.mpf(0)
                break
            g_lo /= 4
        assert small_g_ub is not None
    else:
        g_lo = mp.mpf("1e-24")
        gb = iv.mpf([mp.mpf(0), g_lo])
        small_g_ub = mp.mpf((alpha_G * (gb ** km1_iv) - beta_G * (gb ** k_iv) - a_iv * gb).b)

    core_G_ub = _iv_sup_1d(fG_and_df, g_lo, g_hi)
    sup_G_ub = max(mp.mpf(0), small_g_ub, core_G_ub)
    return mp.mpf((iv.mpf(sup_M_ub) + iv.mpf(sup_G_ub) + l1_iv - a_iv).b)


# --- B3: Pure mpmath.iv Problem Builder & Zero-Discrepancy Shared-Multiplier Verifier ---
def _build_closed_basis_struct(p_key, wlist0, max_id_len):
    """
    100% symbolic Newton-chip / closed-basis NC-SOS structure:
      V = { canon_w(u^* v) : u, v in wlist0 } => EVERY variable is covered by Block 0 by construction!
    """
    n_gen = 3 if p_key in ("5/4", "5/3") else 2
    # Get exact polynomial monomial supports (independent of numeric parameter values!)
    _, g0_s, g1_s, h_s, w_s = build_problem_polys_iv(p_key, iv.mpf(2), iv.mpf(1), iv.mpf(1))
    w_supp = [list(pw.keys()) for pw in w_s]
    id_supp = [list(set(g0_s.keys()) | set(g1_s.keys()))] + [list(ph.keys()) for ph in h_s]

    canon = sorted(set(canon_w(u[::-1] + v) for u in wlist0 for v in wlist0))
    w2i = {w: i for i, w in enumerate(canon)}
    n_var = len(canon)
    canon_set = set(canon)

    word_pairs = [[] for _ in range(n_var)]
    for r_i, wu in enumerate(wlist0):
        wur = wu[::-1]
        for c_i, wv in enumerate(wlist0):
            word_pairs[w2i[canon_w(wur + wv)]].append((r_i, c_i))
    for idx in range(n_var):
        assert len(word_pairs[idx]) > 0, f"Word {canon[idx]} uncovered by Block 0!"

    blocks_wlists = [wlist0]
    for a in range(1, len(w_supp)):
        supp = w_supp[a]
        cand = [u for u in wlist0 if all(canon_w(u[::-1] + k + u) in canon_set for k in supp)]
        kept = []
        for u in cand:
            if all(canon_w(u[::-1] + k + v) in canon_set for v in kept for k in supp):
                kept.append(u)
        blocks_wlists.append(kept)

    all_short = gen_words(n_gen, max_id_len)
    id_meta = []
    for gi, supp in enumerate(id_supp):
        for wl in all_short:
            for wr in all_short:
                if len(wl) + len(wr) > max_id_len:
                    continue
                if all(canon_w(wl + k + wr) in canon_set for k in supp):
                    id_meta.append((gi, wl, wr))

    return {
        "n_gen": n_gen, "max_deg": 0, "canon": canon, "w2i": w2i, "n_var": n_var,
        "blocks_wlists": blocks_wlists, "word_pairs": word_pairs, "id_meta": id_meta,
    }


def build_symbolic_struct(p_key, max_deg):
    if p_key == "5/4" and max_deg in ("8A", "8C"):
        base3 = reduced_words_k(3, 3)
        d4 = [w for w in reduced_words_k(3, 4) if len(w) == 4]
        if max_deg == "8A":
            wlist0 = sorted(set(base3 + [w for w in d4 if w.count(2) == 0]), key=lambda w: (len(w), w))
        else:
            wlist0 = sorted(set(base3 + [w for w in d4 if w.count(2) <= 1]), key=lambda w: (len(w), w))
        return _build_closed_basis_struct("5/4", wlist0, max_id_len=4)
    if p_key == "3/2" and max_deg == "12C":
        base5 = reduced_words_k(2, 5)
        d6 = [w for w in reduced_words_k(2, 6) if len(w) == 6 and (0, 0, 0) not in [w[i:i + 3] for i in range(4)]]
        wlist0 = sorted(set(base5 + d6), key=lambda w: (len(w), w))
        return _build_closed_basis_struct("3/2", wlist0, max_id_len=6)

    specs = {
        "6/5": (2, [5, 6], [0, 1, 1, 2, 1, 1, 2, 5, 5, 6, 6, 6, 6]),
        "5/4": (3, [5, 3, 6, 5], [0, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 5, 6, 6, 6, 6]),
        "3/2": (2, [6, 6], [0, 1, 1, 1, 2, 5, 5, 6, 6, 1, 2, 6, 6]),
        "5/3": (3, [6, 4, 6, 5], [0, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 5, 6, 6, 6, 6]),
    }
    n_gen, ideal_degs, weight_degs = specs[p_key]
    all_raw = gen_words(n_gen, max_deg)
    canon = sorted(set(canon_w(w) for w in all_raw))
    w2i = {w: i for i, w in enumerate(canon)}
    n_var = len(canon)

    blocks_wlists = []
    for dW in weight_degs:
        wlen = (max_deg - dW) // 2
        assert wlen >= 0, f"max_deg={max_deg} too small for weight deg {dW}!"
        blocks_wlists.append(reduced_words_k(n_gen, wlen))

    # Exact symmetric Block-0 coverage map for zero-residual absorption!
    wlist0 = blocks_wlists[0]
    word_pairs = [[] for _ in range(n_var)]
    for r_i, wu in enumerate(wlist0):
        wur = wu[::-1]
        for c_i, wv in enumerate(wlist0):
            word_pairs[w2i[canon_w(wur + wv)]].append((r_i, c_i))
    for idx in range(n_var):
        assert len(word_pairs[idx]) > 0, f"Word {canon[idx]} uncovered by Block 0!"

    id_meta = []
    for g_idx, dg in enumerate(ideal_degs):
        rem = max_deg - dg
        if rem < 0:
            continue
        for len_l in range(rem + 1):
            for len_r in range(rem - len_l + 1):
                for wl in product(range(n_gen), repeat=len_l):
                    for wr in product(range(n_gen), repeat=len_r):
                        id_meta.append((g_idx, wl, wr))

    return {
        "n_gen": n_gen, "max_deg": max_deg, "canon": canon, "w2i": w2i, "n_var": n_var,
        "blocks_wlists": blocks_wlists, "word_pairs": word_pairs, "id_meta": id_meta,
    }


def build_problem_polys_iv(p_key, X_cap_iv, U_iv, L_iv):
    """
    100% pure mpmath.iv builder of constant weights, objective, and affine Holden ideal
    g(mu) = g0 - mu * g1 (where mu = Lam for p=6/5, 5/4, 3/2; mu = Lam^2 for p=5/3).
    """
    one = iv.mpf(1)
    pI = {(): one}; p0 = {(0,): one}; p1 = {(1,): one}
    pIm0 = padd_iv(pI, p0, -1)

    if p_key == "6/5":
        # 0 = D in (0, 1], 1 = Ht = H / X_cap in (0, D]
        cM = one + X_cap_iv
        inv_cM = one / cM
        pMt = {(0,): inv_cM, (1,): X_cap_iv * inv_cM}
        X2 = X_cap_iv * X_cap_iv; X3 = X2 * X_cap_iv
        pObj = {(1, 0, 1, 0, 1): X3, (0, 1, 0, 1, 0): -X2}
        g0 = ppow_iv(pMt, 5)
        g1 = {(0, 1, 0, 1, 0): X2 / (cM ** 5)}
        h_list = [padd_iv(pmul_iv(pObj, p0), pmul_iv(p0, pObj), -1)]
        pUmE = padd_iv({(0,)*5: U_iv}, pObj, -1)
        pLpE = padd_iv({(0,)*5: L_iv}, pObj, +1)
        weights = [
            pI, p0, pIm0, pmul_iv(p0, pIm0),
            p1, padd_iv(p0, p1, -1), pmul_iv(p1, padd_iv(pI, p1, -1)),
            pUmE, pLpE,
            pmul_iv(p0, pUmE), pmul_iv(p0, pLpE),
            pmul_iv(pIm0, pUmE), pmul_iv(pIm0, pLpE),
        ]
        return pObj, g0, g1, h_list, weights

    if p_key == "5/4":
        # 0 = D in (0, 1], 1 = Ht = H / X_cap in (0, D], 2 = Qt = Q / sqrt(X_cap) in (0, 1]
        p2 = {(2,): one}
        sqX = iv.sqrt(X_cap_iv)
        cM = one + X_cap_iv; inv_cM = one / cM
        pMt = {(0,): inv_cM, (1,): X_cap_iv * inv_cM}
        half_XsqX = (X_cap_iv * sqX) / iv.mpf(2)
        pDHDQD = {(0, 1, 0, 2, 0): half_XsqX, (0, 2, 0, 1, 0): half_XsqX}
        pObj = padd_iv({(1, 0, 2, 0, 1): (X_cap_iv * X_cap_iv) * sqX}, pDHDQD, -1)
        g0 = ppow_iv(pMt, 4)
        inv_cM4 = one / (cM ** 4)
        g1 = {k: v * inv_cM4 for k, v in pDHDQD.items()}
        h1 = padd_iv(p1, {(2, 0, 2): -one})                           # Ht - Qt D Qt = 0
        h2 = padd_iv(pmul_iv(pObj, p0), pmul_iv(p0, pObj), -1)        # [E, D] = 0
        h3 = {(0, 1, 0, 2, 0): one, (0, 2, 0, 1, 0): -one}            # D Ht D Qt D - D Qt D Ht D = 0
        pUmE = padd_iv({(0,)*4: U_iv}, pObj, -1)
        pLpE = padd_iv({(0,)*4: L_iv}, pObj, +1)
        pIm2 = padd_iv(pI, p2, -1)
        weights = [
            pI, p0, pIm0, pmul_iv(p0, pIm0),
            p1, padd_iv(p0, p1, -1), pmul_iv(p1, padd_iv(pI, p1, -1)),
            p2, pIm2, pmul_iv(p2, pIm2),
            pUmE, pLpE,
            pmul_iv(p0, pUmE), pmul_iv(p0, pLpE),
            pmul_iv(pIm0, pUmE), pmul_iv(pIm0, pLpE),
        ]
        return pObj, g0, g1, [h1, h2, h3], weights

    if p_key == "3/2":
        # 0 = D in (0, 1], 1 = Qt = Q / sqrt(X_cap) in (0, 1]
        sqX = iv.sqrt(X_cap_iv); cM = one + X_cap_iv; inv_cM2 = one / (cM * cM)
        pDpH = {(0,): one, (1, 0, 1): X_cap_iv}
        pObj = {(1, 0, 1, 0, 1): X_cap_iv * sqX, (0, 1, 0): -sqX}
        g0 = {k: v * inv_cM2 for k, v in pmul_iv(pDpH, pDpH).items()}
        g1 = {(0, 1, 0): sqX * inv_cM2}
        h_list = [padd_iv(pmul_iv(pObj, p0), pmul_iv(p0, pObj), -1)]
        pIm1 = padd_iv(pI, p1, -1)
        pUmF = padd_iv({(0, 0): U_iv}, pObj, -1)
        pLpF = padd_iv({(0, 0): L_iv}, pObj, +1)
        weights = [
            pI, p0, p1, pIm1, pmul_iv(p1, pIm1),
            pUmF, pLpF,
            pmul_iv(p0, pUmF), pmul_iv(p0, pLpF),
            pIm0, pmul_iv(p0, pIm0),
            pmul_iv(pIm0, pUmF), pmul_iv(pIm0, pLpF),
        ]
        return pObj, g0, g1, h_list, weights

    if p_key == "5/3":
        # 0 = A = D^{1/2} in (0, 1], 1 = Bt = G^{1/4}/X^{1/4} in (0, A], 2 = Ht = H/X in (0, A^2]
        p2 = {(2,): one}; pA2 = {(0, 0): one}
        sqX = iv.sqrt(X_cap_iv)
        bX = X_cap_iv ** (iv.mpf(1) / iv.mpf(4))
        cM = one + X_cap_iv; inv_cM = one / cM
        pMt = {(0, 0): inv_cM, (2,): X_cap_iv * inv_cM}
        pABA = {(0, 1, 0): one}
        pObj = {(1, 1, 1, 1, 1): X_cap_iv * bX, (0, 0, 1, 0, 0): -bX}
        g0 = ppow_iv(pMt, 3)
        g1 = {(0, 1, 0, 0, 1, 0): sqX / (cM ** 3)}  # affine in mu = Lam^2!
        h1 = {(0, 2, 0): one, (1, 1, 1, 1): -one}                    # A Ht A - Bt^4 = 0
        h2 = padd_iv(pmul_iv(pObj, p0), pmul_iv(p0, pObj), -1)       # [E, A] = 0
        h3 = padd_iv(pmul_iv(pMt, pABA), pmul_iv(pABA, pMt), -1)     # [Mt, A Bt A] = 0
        pUmE = padd_iv({(0,)*5: U_iv}, pObj, -1)
        pLpE = padd_iv({(0,)*5: L_iv}, pObj, +1)
        weights = [
            pI, p0, pIm0, pmul_iv(p0, pIm0),
            p1, padd_iv(p0, p1, -1), pmul_iv(p1, padd_iv(pI, p1, -1)),
            p2, padd_iv(pA2, p2, -1), pmul_iv(p2, padd_iv(pI, p2, -1)),
            pUmE, pLpE,
            pmul_iv(p0, pUmE), pmul_iv(p0, pLpE),
            pmul_iv(pIm0, pUmE), pmul_iv(pIm0, pLpE),
        ]
        return pObj, g0, g1, [h1, h2, h3], weights

    raise ValueError(f"Unknown p_key {p_key}")


def iv_certify_nc_sos_interval(p_key, k_num, k_den, m, Lam0_mp, Lam1_mp, struct, mults_mp, witness_bundle):
    """
    100% PURE ZERO-FLOAT mpmath.iv CONVEX-COMBINATION NC-SOS INTERVAL VERIFIER!!
    Certifies that NO finite-dimensional SPD solution of Holden Theorem 3.1 exists
    for ANY real Lambda in the continuous closed interval [Lam0_mp, Lam1_mp]!

    Monotonicity on ((k-1)/k, inf):
      h(x) = (1+x)^{2k-1}/x^{k-1} has h'(x) = (1+x)^{2k-2}/x^k * (k*x - (k-1)) > 0,
      so x_+(Lam) = h^{-1}(Lam) is strictly increasing; and for x > 1,
      sig(x) = x^{k-1}(x-1) has sig'(x) = x^{k-2}(k*x - (k-1)) > 0,
      so sig_+(Lam) is strictly increasing. Thus for ALL Lam in [Lam0, Lam1]:
        1 < x_+(Lam0) <= x_+(Lam) <= x_+(Lam1) <= X_cap,
        sig_+(Lam) >= sig_+(Lam0) >= (m-1) * target_lo.
    """
    assert Lam0_mp < Lam1_mp
    Lam_box = iv.mpf([Lam0_mp, Lam1_mp])
    xp0_iv, sigp0_iv = iv_certify_xplus(Lam0_mp, k_num, k_den)
    xp1_iv, _ = iv_certify_xplus(Lam1_mp, k_num, k_den)
    assert mp.mpf(xp0_iv.a) > 1
    X_cap_iv = iv.mpf(mp.mpf(xp1_iv.b))
    target_lo = mp.mpf((sigp0_iv / iv.mpf(m - 1)).a)

    # Certify uniform Stage-1 L_box over ALL Lam in [Lam0_mp, Lam1_mp]
    L_box_mp = iv_certify_stage1_5scalar(Lam_box, k_num, k_den, mults_mp)
    L_box_iv = iv.mpf(L_box_mp)
    U_box_iv = iv.mpf(m - 1) * L_box_iv

    pObj_iv, g0_iv, g1_iv, h_list_iv, weights_iv = build_problem_polys_iv(p_key, X_cap_iv, U_box_iv, L_box_iv)

    mu0_iv = iv.mpf(Lam0_mp) ** 2 if p_key == "5/3" else iv.mpf(Lam0_mp)
    mu1_iv = iv.mpf(Lam1_mp) ** 2 if p_key == "5/3" else iv.mpf(Lam1_mp)

    n_var = struct["n_var"]; w2i = struct["w2i"]
    blocks_wlists = struct["blocks_wlists"]
    word_pairs = struct["word_pairs"]; id_meta = struct["id_meta"]
    sz0 = len(blocks_wlists[0]); idx_const = w2i[()]
    assert word_pairs[idx_const] == [(0, 0)], "Const word must map uniquely to (0, 0)!"

    Obj_vec = [iv.mpf(0) for _ in range(n_var)]
    for k, v in pObj_iv.items():
        Obj_vec[w2i[canon_w(k)]] += v

    Z0_0_mp, fac_0_mp, lam_0_mp, Z0_1_mp, fac_1_mp, lam_1_mp = witness_bundle
    # Strictly assert that EVERY mu-dependent ideal multiplier (g_idx == 0) is IDENTICAL at mu0 and mu1!
    # For g_idx >= 1 (h_list, independent of mu), convex combination (1-t)*lam_0 + t*lam_1 still has ZERO quadratic error!
    for idx_e, (g_idx, _, _) in enumerate(id_meta):
        if g_idx == 0:
            assert lam_0_mp[idx_e] == lam_1_mp[idx_e], "g-multiplier must be shared across [mu0, mu1]!"

    def assemble_endpoint(Z0_mp, fac_mp, lam_mp, mu_iv):
        pg_iv = padd_iv(g0_iv, g1_iv, -mu_iv)
        all_ideals = [pg_iv] + h_list_iv

        # Check symmetry of initial Z0_mp and convert to point intervals
        for i in range(sz0):
            for j in range(i + 1, sz0):
                assert Z0_mp[i][j] == Z0_mp[j][i], "Initial Z0 asymmetric!"
        Z0_iv = [[iv.mpf(Z0_mp[i][j]) for j in range(sz0)] for i in range(sz0)]
        lam_iv = [iv.mpf(x) for x in lam_mp]

        rhs_iv = [iv.mpf(0) for _ in range(n_var)]
        # Ideal multiplier contribution
        for idx_e, (g_idx, wl, wr) in enumerate(id_meta):
            c = lam_iv[idx_e]
            if c == 0:
                continue
            for k, v in all_ideals[g_idx].items():
                rhs_iv[w2i[canon_w(wl + k + wr)]] += c * v

        # Blocks a >= 1 (exact outer-product PSD factors!)
        for a in range(1, len(blocks_wlists)):
            wlist = blocks_wlists[a]; sz = len(wlist); pW = weights_iv[a]
            Ga = [[iv.mpf(0) for _ in range(sz)] for _ in range(sz)]
            for lam_r_mp, vec_r_mp in fac_mp[a]:
                assert lam_r_mp > 0, "Non-positive outer-product weight!"
                lr = iv.mpf(lam_r_mp)
                vr = [iv.mpf(x) for x in vec_r_mp]
                for i in range(sz):
                    lv = lr * vr[i]
                    for j in range(i, sz):
                        val = lv * vr[j]
                        Ga[i][j] += val
                        if i != j:
                            Ga[j][i] += val
            for r_i, wu in enumerate(wlist):
                wur = wu[::-1]
                for c_i, wv in enumerate(wlist):
                    g_rc = Ga[r_i][c_i]
                    if g_rc == 0:
                        continue
                    for k, v in pW.items():
                        rhs_iv[w2i[canon_w(wur + k + wv)]] += g_rc * v

        # Block 0 initial contribution
        wlist0 = blocks_wlists[0]
        for r_i, wu in enumerate(wlist0):
            wur = wu[::-1]
            for c_i, wv in enumerate(wlist0):
                rhs_iv[w2i[canon_w(wur + wv)]] += Z0_iv[r_i][c_i]

        # Exact minimum-Frobenius-norm residual absorption into Z0_iv!
        for idx in range(n_var):
            if idx == idx_const:
                continue
            diff = Obj_vec[idx] - rhs_iv[idx]
            pairs = word_pairs[idx]
            share = diff / len(pairs)
            for (r_i, c_i) in pairs:
                Z0_iv[r_i][c_i] += share

        for i in range(sz0):
            for j in range(i + 1, sz0):
                assert Z0_iv[i][j] == Z0_iv[j][i], "Asymmetry after residual absorption!"

        Psi_hi = mp.mpf((rhs_iv[idx_const] - Obj_vec[idx_const]).b)
        return Z0_iv, Psi_hi

    Z0_0_iv, Psi0_hi = assemble_endpoint(Z0_0_mp, fac_0_mp, lam_0_mp, mu0_iv)
    Z0_1_iv, Psi1_hi = assemble_endpoint(Z0_1_mp, fac_1_mp, lam_1_mp, mu1_iv)

    # Certify BOTH endpoint mpmath.iv Cholesky factorizations!
    # Because lam_shared is identical at mu0 and mu1 and g(mu) = g0 - mu*g1 is affine,
    # for ANY t in [0, 1], (1-t)*Eq(mu0) + t*Eq(mu1) has ZERO quadratic discrepancy!
    ok0, d0 = iv_cholesky_pd(Z0_0_iv)
    if not ok0:
        return False, f"Z0_0 Cholesky failed ({mp.nstr(d0, 3)})"
    ok1, d1 = iv_cholesky_pd(Z0_1_iv)
    if not ok1:
        return False, f"Z0_1 Cholesky failed ({mp.nstr(d1, 3)})"

    Psi_ub = max(Psi0_hi, Psi1_hi)
    min_d = min(d0, d1)
    margin = mp.mpf((iv.mpf(target_lo) - iv.mpf(Psi_ub)).a)
    if not (Psi_ub < target_lo and margin > 0):
        return False, f"Margin fail: Psi_ub={mp.nstr(Psi_ub, 10)} >= target_lo={mp.nstr(target_lo, 10)}"
    return True, (Psi_ub, target_lo, margin, min_d)


# ==============================================================================
# SECTION C: ORCHESTRATION DRIVERS (FEED SECTION A WITNESSES TO SECTION B!)
# ==============================================================================
def certify_stage1_tail(Lam_start_mp, Lam_end_mp, k_num, k_den, m):
    """
    Certifies via Section B's pure mpmath.iv verifier that NO solution exists on the ENTIRE
    interval [Lam_start_mp, Lam_end_mp] via Stage-1 L_all(Lam_box) < sig_+(Lam_lo)/(m-1)!
    """
    stack = [(Lam_start_mp, Lam_end_mp, 0)]
    covered = []
    while stack:
        lo, hi, depth = stack.pop()
        _, sig0_iv = iv_certify_xplus(lo, k_num, k_den)
        targ_lo = mp.mpf((sig0_iv / iv.mpf(m - 1)).a)
        mults = oracle_stage1_lp_multipliers(lo, hi, k_num, k_den)
        L_ub = iv_certify_stage1_5scalar(iv.mpf([lo, hi]), k_num, k_den, mults)
        if L_ub < targ_lo:
            covered.append((lo, hi))
        else:
            assert depth < 12, f"Stage-1 tail certification failed on [{lo}, {hi}]!"
            mid = (lo + hi) / 2
            assert lo < mid < hi
            stack.append((mid, hi, depth + 1))
            stack.append((lo, mid, depth + 1))
    covered.sort(key=lambda t: t[0])
    assert covered[0][0] == Lam_start_mp and covered[-1][1] == Lam_end_mp
    for i in range(len(covered) - 1):
        assert covered[i][1] == covered[i + 1][0]
    return covered


def certify_upper_bound_all_lambda(p_key, k_num, k_den, m, Lam_cert_str, tier_specs):
    """
    Certifies C_p(m) <= C_ub UNCONDITIONALLY for ALL n >= 1 by certifying ZERO solutions
    on the ENTIRE continuous interval [Lam_cert, Lam_interp(p, m)]!
    tier_specs: list of (Lam_hi_str, deg, eps_I_f) covering [Lam_cert, Lam_s1],
                followed automatically by Stage-1 tail covering [Lam_s1, Lam_interp_ub]!
    """
    t0 = time.time()
    mp.mp.dps = 45; iv.dps = 40

    # Outward-rounded left endpoint: Lam_cert_mp = iv(Lam_cert_str).a <= exact(Lam_cert_str)
    # guarantees zero decimal-to-binary rounding crack at [exact(Lam_cert_str), Lam_cert_mp]!
    Lam_cert_iv = iv.mpf(Lam_cert_str)
    Lam_cert_mp = mp.mpf(Lam_cert_iv.a)
    k_iv = iv.mpf(k_num) / iv.mpf(k_den)
    # Exact complex interpolation upper bound: Lam <= 2^{2k-2} * (1 + sqrt(m))
    Lam_interp_iv = (iv.mpf(2) ** (2 * k_iv - 2)) * (iv.mpf(1) + iv.sqrt(iv.mpf(m)))
    Lam_interp_ub = mp.mpf((Lam_interp_iv + iv.mpf("1e-6")).b)  # strictly covers Lam_interp!
    assert Lam_interp_ub > mp.mpf(Lam_interp_iv.b)
    # Outward-rounded upper bound on C_p(m) from exact Lam_cert_str (strictly >= C(Lam_cert_mp))!
    C_ub_iv = (Lam_cert_iv / (iv.mpf(2) ** (2 * k_iv - 1))) ** (iv.mpf(1) / (2 * k_iv))
    C_ub_mp = mp.mpf(C_ub_iv.b)

    structs = {}
    all_intervals = []
    cur_lo = Lam_cert_mp

    for (seg_hi_str, deg, eps_I_f) in tier_specs:
        seg_hi = mp.mpf(seg_hi_str)
        assert cur_lo < seg_hi, f"Non-increasing tier endpoint: cur_lo={cur_lo} >= seg_hi={seg_hi}"
        if deg not in structs:
            structs[deg] = build_symbolic_struct(p_key, deg)
        struct = structs[deg]

        stack = [(cur_lo, seg_hi, eps_I_f, 0)]
        while stack:
            lo, hi, eI, depth = stack.pop()
            # Quick Stage-1 check first (free!)
            _, sig0_iv = iv_certify_xplus(lo, k_num, k_den)
            targ_lo = mp.mpf((sig0_iv / iv.mpf(m - 1)).a)
            mults = oracle_stage1_lp_multipliers(lo, hi, k_num, k_den)
            L_box_mp = iv_certify_stage1_5scalar(iv.mpf([lo, hi]), k_num, k_den, mults)
            if L_box_mp < targ_lo:
                all_intervals.append((lo, hi, "Stage-1"))
                continue

            # Build problem polynomials for oracle at exact box bounds
            xp1_iv, _ = iv_certify_xplus(hi, k_num, k_den)
            X_cap_iv = iv.mpf(mp.mpf(xp1_iv.b))
            L_box_iv = iv.mpf(L_box_mp); U_box_iv = iv.mpf(m - 1) * L_box_iv
            pObj_iv, g0_iv, g1_iv, h_list_iv, weights_iv = build_problem_polys_iv(p_key, X_cap_iv, U_box_iv, L_box_iv)
            mu0_iv = iv.mpf(lo) ** 2 if p_key == "5/3" else iv.mpf(lo)
            mu1_iv = iv.mpf(hi) ** 2 if p_key == "5/3" else iv.mpf(hi)

            # Call untrusted oracle -> pure exact mp.mpf witness bundle
            bundle = oracle_solve_interval_sos(struct, pObj_iv, g0_iv, g1_iv, h_list_iv, weights_iv, mu0_iv, mu1_iv, eI)
            # Call 100% pure zero-float mpmath.iv verifier!
            ok, info = iv_certify_nc_sos_interval(p_key, k_num, k_den, m, lo, hi, struct, mults, bundle)
            if ok:
                all_intervals.append((lo, hi, f"SOS-d{deg}"))
            else:
                print(f"    [retry p={p_key} m={m} d={deg} depth={depth} eI={eI:.1e}] [{mp.nstr(lo,9)}, {mp.nstr(hi,9)}]: {info}")
                assert depth < 7, f"NC-SOS interval certification failed on [{lo}, {hi}] (deg={deg}): {info}"
                if isinstance(info, str) and info.startswith("Margin fail") and eI > 2e-7:
                    stack.append((lo, hi, max(1e-7, eI * 0.2), depth + 1))
                elif isinstance(info, str) and (info.startswith("Z0_0 Cholesky") or info.startswith("Z0_1 Cholesky")) and depth == 0:
                    stack.append((lo, hi, eI * 3.0, depth + 1))
                else:
                    mid = (lo + hi) / 2
                    assert lo < mid < hi
                    stack.append((mid, hi, eI, depth + 1))
                    stack.append((lo, mid, eI, depth + 1))
        cur_lo = seg_hi

    # Certify Stage-1 tail from cur_lo to Lam_interp_ub!
    tail_cov = certify_stage1_tail(cur_lo, Lam_interp_ub, k_num, k_den, m)
    for (lo, hi) in tail_cov:
        all_intervals.append((lo, hi, "Stage-1-tail"))

    # STRICT GAP-FREE CONTINUOUS COVERAGE ASSERTION!
    all_intervals.sort(key=lambda t: t[0])
    assert all_intervals[0][0] == Lam_cert_mp, "Left endpoint mismatch!"
    for i in range(len(all_intervals) - 1):
        assert all_intervals[i][1] == all_intervals[i + 1][0], f"GAP between {all_intervals[i]} and {all_intervals[i+1]}!"
    assert all_intervals[-1][1] >= Lam_interp_ub, "Right endpoint did not cover Lam_interp!"

    n_sos = sum(1 for x in all_intervals if x[2].startswith("SOS"))
    n_s1 = len(all_intervals) - n_sos
    print(f"  [UPPER PASS] p={p_key}, m={m}: ALL Lam in [{Lam_cert_str}, {mp.nstr(Lam_interp_ub, 8)}] "
          f"certified ({n_sos} SOS + {n_s1} Stage-1 boxes, 0 gaps) ==> "
          f"C_{{{p_key}}}({m}) <= {mp.nstr(C_ub_mp, 15)}  [{time.time()-t0:.1f}s]")
    return C_ub_mp, len(all_intervals)


if __name__ == "__main__":
    t_start = time.time()
    summary = {}

    # ------------------------------------------------------------------
    # PART 1: 100% ZERO-FLOAT LOWER BOUNDS (12 cases: 4 exponents x 3 m)
    # ------------------------------------------------------------------
    print("================================================================================")
    print("PART 1: 100% ZERO-FLOAT mpmath.iv LOWER BOUNDS (EXPLICIT FINITE-DIM MATRICES)")
    print("================================================================================")
    mp.mp.dps = 65; iv.dps = 60
    lb_cases = [
        ("6/5", 6, 5, 3, 2, [(2, 5, 2), (3, 4, 2), (4, 3, 2)]),
        ("5/4", 5, 4, 5, 3, [(2, 5, 2), (3, 4, 2), (4, 3, 2)]),
        ("3/2", 3, 2, 3, 1, [(2, 5, 2), (3, 4, 2), (4, 3, 2)]),
        ("5/3", 5, 3, 5, 1, [(2, 3, 2), (3, 3, 2), (4, 3, 2)]),
    ]
    for p_key, p_num, p_den, a_int, b_int, cfgs in lb_cases:
        for m, r, L_dep in cfgs:
            t0 = time.time()
            Ts, R0, N = oracle_build_lower_bound_witness(p_num, p_den, a_int, b_int, m, r, L_dep)
            C_lb, tau = certify_lower_bound_iv(p_num, p_den, a_int, b_int, Ts, R0)
            summary[(p_key, m)] = {"lb": C_lb, "dim": m * N}
            print(f"  [LOWER PASS] p={p_key}, m={m} ({m*N}x{m*N}, r={r}, L={L_dep}, tau={mp.nstr(mp.mpf(tau.b), 2)}): "
                  f"C_{{{p_key}}}({m}) > {mp.nstr(C_lb, 15)}  [{time.time()-t0:.1f}s]")

    # ------------------------------------------------------------------
    # PART 2: 100% ZERO-FLOAT ALL-DIMENSIONS, ALL-LAMBDA UPPER BOUNDS
    # ------------------------------------------------------------------
    print("\n================================================================================")
    print("PART 2: 100% ZERO-FLOAT ALL-DIMENSIONS, ALL-LAMBDA NC-SOS UPPER BOUNDS")
    print("================================================================================")
    ub_configs = [
        # (p_key, k_num, k_den, m, Lam_cert_str, tier_specs=[(seg_hi_str, deg, eps_I)])
        ("5/3", 5, 4, 2, "3.251598", [("3.251601", 6, 1e-7), ("3.25166", 6, 2e-6), ("3.25216", 6, 2e-5)]),
        ("5/3", 5, 4, 3, "3.580802", [("3.580807", 6, 1e-7), ("3.58085", 6, 2e-7), ("3.58146", 6, 2e-5)]),
        ("5/3", 5, 4, 4, "3.859845", [("3.859855", 6, 1e-7), ("3.85990", 6, 5e-7), ("3.86048", 6, 5e-6)]),

        ("3/2", 3, 2, 2, "4.453377", [("4.4533785", 10, 1e-7), ("4.453383", 10, 1e-7), ("4.45340", 10, 2e-7), ("4.45350", 10, 5e-7), ("4.4596", 10, 5e-6)]),
        ("3/2", 3, 2, 3, "4.806190", [("4.806192",  10, 1e-7), ("4.806198", 10, 1e-7), ("4.80622", 10, 2e-7), ("4.80635", 10, 1e-6), ("4.8151", 10, 1e-5)]),
        ("3/2", 3, 2, 4, "5.105198", [("5.105200",  10, 1e-7), ("5.105208", 10, 1e-7), ("5.10524", 10, 2e-7), ("5.10545", 10, 1e-6), ("5.1156", 10, 1e-5)]),

        ("6/5", 3, 1, 2, "33.4505",  [("33.4510", 10, 1e-7), ("33.455", 10, 5e-7), ("33.48", 10, 5e-6), ("33.77", 10, 1e-4)]),
        ("6/5", 3, 1, 3, "34.5515",  [("34.5522", 10, 1e-7), ("34.560", 10, 5e-7), ("34.62", 10, 5e-6), ("35.15", 10, 1e-4)]),
        ("6/5", 3, 1, 4, "35.4668",  [("35.4675", 10, 1e-7), ("35.475", 10, 5e-7), ("35.58", 10, 5e-6), ("36.31", 10, 1e-4)]),

        ("5/4", 5, 2, 2, "16.9073",  [("16.915", "8C", 2e-6), ("16.955", "8A", 5e-6), ("17.055", 6, 5e-5)]),
        ("5/4", 5, 2, 3, "17.5995",  [("17.615", "8C", 5e-6), ("17.675", "8A", 5e-6), ("17.865", 6, 5e-5)]),
        ("5/4", 5, 2, 4, "18.1790",  [("18.200", "8C", 5e-6), ("18.275", "8A", 5e-6), ("18.545", 6, 5e-5)]),
    ]
    for p_key, kn, kd, m, Lam_s, tiers in ub_configs:
        C_ub, n_box = certify_upper_bound_all_lambda(p_key, kn, kd, m, Lam_s, tiers)
        summary[(p_key, m)]["ub"] = C_ub
        summary[(p_key, m)]["boxes"] = n_box
        assert summary[(p_key, m)]["lb"] < C_ub, "Impossible: LB >= UB!"

    print("\n================================================================================")
    print("FINAL 100% ZERO-FLOAT CERTIFIED MULTI-p ENCLOSURE TABLE (ALL DIMENSIONS n >= 1)")
    print("================================================================================")
    for p_key in ["6/5", "5/4", "3/2", "5/3"]:
        for m in [2, 3, 4]:
            rec = summary[(p_key, m)]
            gap = mp.mpf((iv.mpf(rec["ub"]) - iv.mpf(rec["lb"])).b)
            print(f"  p = {p_key}, m = {m}:  {mp.nstr(rec['lb'], 13)}  <  C_{{{p_key}}}({m})  <=  {mp.nstr(rec['ub'], 13)}   "
                  f"(gap = {mp.nstr(gap, 3)}, {rec['boxes']} iv-boxes)")
    print(f"\nALL 24 RIGOROUS CERTIFICATIONS PASSED WITH ZERO GAPS AND ZERO FLOATS! ({time.time()-t_start:.1f}s total)")
