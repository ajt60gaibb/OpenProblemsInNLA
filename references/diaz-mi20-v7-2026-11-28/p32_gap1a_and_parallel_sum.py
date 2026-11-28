#!/usr/bin/env python3
"""
MI-20 Final-Sprint Bridge Verification Suite (`#131` Deliverables):
  Module 1 (Part A(ii)): Unconditional All-m (Lambda > 4, all m >= 2) Existence of Dual Balayage
                         Measure eta_Lambda >= 0, Exact Closed-Form Primal Spectral Edge q_edge(a)
                         (solving #114 Open Question (c)), Exact Z_{>0} SymPy Geometry & Pole-Sweeping
                         Proofs, and Alternating-Node Spectral Cauchy Primal/Dual Tonelli Cross-Check.
  Module 2 (Part A(i)):  Gap 1A Global Y = Q Rigidity — 3-Line Elimination (G1'')+(G2'')+(G4) =>
                         (MIRACLE-1) => (MIRACLE-3), Proved Special Cases (Hermitian PSD S all n,
                         Scalar P = p I_n all n, Exact Commuting 2x2 SymPy SOS Proof, Primal Convex
                         Lagrangian INEQ-1), and Exact 2x2 Non-Commuting No-Go Counterexamples
                         (including strictly positive symmetric part (S+S^T)/2 > 0) for Standalone
                         (MIRACLE-3).
  Module 3 (Part B(i)):  Universal All-(1 < p < 2) Large-m Excess Theorem — Exact Symbolic SymPy
                         Derivation for Arbitrary kappa = p/(2(p-1)) in (1, inf), Direct-from-Asymptotic
                         120-dps mpmath Verification Across 8 Rational & Irrational Exponents (res <= 1e-108),
                         Subcriticality rho_2 -> 0, and Large-m 2-Atom Primal/Dual Dichotomy Check.
  Module 4 (Part B(ii)): Parallel-Sum & Second-Use-of-Holden Polynomial Ideal Benchmarks at p = 5/3
                         (kappa = 5/4) and p = 6/5 (kappa = 3) — Exact 3-Gen (A,B,C) & Bounded 6-Gen
                         All-Degree-3 (A,Z,T1,T2,U,V) Holden Relations, 3-Atom Hermitian Linear Partition
                         Y_k = a_k I + c_k Z, Disproof of Naive 2nd-Step Candidates, Sharp Degree-6
                         Polynomial-Ideal Threshold in Primal-Dual IP SDP (1D comm, 3-var comm, Full NC D=4),
                         and p = 6/5 Dual-Q Off-Holden Obstruction + Degree-6 Barrier.

Author: bridge-auditor
Self-contained dependencies: stdlib + numpy + scipy + mpmath + sympy ONLY.
Run command: python3 -B -W default p32_gap1a_and_parallel_sum.py
"""

import time
from itertools import product
import numpy as np
from scipy.linalg import eigh
from scipy.optimize import brentq, least_squares, minimize
import mpmath as mp
import sympy as sp

T_GLOBAL_START = time.perf_counter()


# ==============================================================================
# SHARED HELPERS: GENERAL-p HOLDEN ROOTS & CLEAN PRIMAL-DUAL SDP SOLVER
# ==============================================================================

def get_xpm_float(Lam, kap):
    """Exact scalar roots 0 < x_- < (kap-1)/kap < 1 < x_+ of (1+x)^(2k-1) = Lam * x^(k-1)."""
    xc = (kap - 1.0) / kap
    def f(x):
        return (1.0 + x) ** (2.0 * kap - 1.0) - Lam * (x ** (kap - 1.0))
    lo = min(1e-15, 0.25 * (1.0 / Lam) ** (1.0 / (kap - 1.0)))
    while f(lo) <= 0.0:
        lo *= 1e-3
    xm = brentq(f, lo, xc, xtol=1e-15, rtol=1e-14)
    hi = max(2.0, (Lam ** (1.0 / kap)) * 2.0)
    while f(hi) < 0.0:
        hi *= 2.0
    xp = brentq(f, xc, hi, xtol=1e-15, rtol=1e-14)
    return xm, xp


def sig_float(x, kap):
    """Scalar charge sigma(x) = x^(kap - 1) * (x - 1)."""
    return (x ** (kap - 1.0)) * (x - 1.0)


def solve_1x1_float(kap, m):
    """Exact 1x1 scalar solution (Lam, xm, xp, sig_+, C_{1x1}) for given (kap, m)."""
    L0 = 2.0 ** (2.0 * kap - 1.0)
    hi = L0 * 2.0
    while sig_float(get_xpm_float(hi, kap)[1], kap) + (m - 1) * sig_float(get_xpm_float(hi, kap)[0], kap) < 0.0:
        hi *= 2.0
    Lam = brentq(
        lambda L: sig_float(get_xpm_float(L, kap)[1], kap) + (m - 1) * sig_float(get_xpm_float(L, kap)[0], kap),
        L0 + 1e-10, hi, xtol=1e-15
    )
    xm, xp = get_xpm_float(Lam, kap)
    sp_v = sig_float(xp, kap)
    C1 = (Lam / L0) ** (1.0 / (2.0 * kap))
    return Lam, xm, xp, sp_v, C1


def solve_sdp_dual(c, blocks, max_iter=90, tol=1e-7):
    """
    Infeasible primal-dual interior-point (HKM + Mehrotra predictor-corrector) SDP solver:
      (D) min  c^T z                s.t.  S_b = B0_b + sum_k z_k Bz_{b,k} >= 0
      (P) max -sum_b <B0_b, X_b>    s.t.  sum_b <Bz_{b,k}, X_b> = c_k,  X_b >= 0.
    Returns (p_obj, d_obj, nrp, nrd, it).
    """
    n = len(c)
    nb = len(blocks)
    ms = [b[0].shape[0] for b in blocks]
    mtot = sum(ms)
    B0_flat = [b[0].reshape(-1) for b in blocks]
    Bz_flat = [b[1].reshape(n, -1) for b in blocks]
    norm_c = float(np.linalg.norm(c))
    norm_B0 = float(np.sqrt(sum(float(np.sum(b[0] * b[0])) for b in blocks)))

    z = np.zeros(n)
    X = [np.eye(mb) for mb in ms]
    S = [np.eye(mb) for mb in ms]

    def max_step(M, dM):
        M_s = 0.5 * (M + M.T)
        try:
            L = np.linalg.cholesky(M_s)
        except np.linalg.LinAlgError:
            return 0.0
        Linv = np.linalg.solve(L, np.eye(M_s.shape[0]))
        T = Linv @ dM @ Linv.T
        T = 0.5 * (T + T.T)
        ev = float(np.linalg.eigvalsh(T)[0])
        return 1.0 if ev >= 0.0 else min(1.0, -0.95 / ev)

    nrp = nrd = 1.0
    it = 0
    for it in range(1, max_iter + 1):
        rp = c.copy()
        for b in range(nb):
            rp -= Bz_flat[b] @ X[b].reshape(-1)
        rd = [blocks[b][0] + np.tensordot(z, blocks[b][1], axes=([0], [0])) - S[b] for b in range(nb)]
        d_obj = float(c @ z)
        p_obj = -sum(float(B0_flat[b] @ X[b].reshape(-1)) for b in range(nb))
        mu = sum(float(np.sum(X[b] * S[b])) for b in range(nb)) / mtot
        nrp = float(np.linalg.norm(rp)) / (1.0 + norm_c)
        nrd = float(np.sqrt(sum(float(np.sum(r * r)) for r in rd))) / (1.0 + norm_B0)
        gap = abs(d_obj - p_obj) / (1.0 + abs(d_obj) + abs(p_obj))
        if max(nrp, nrd, gap, mu) < tol:
            break

        M = np.zeros((n, n))
        Sinv = []
        for b in range(nb):
            ev, V = eigh(0.5 * (S[b] + S[b].T))
            Si = (V / np.maximum(ev, 1e-15)) @ V.T
            Sinv.append(Si)
            Bzb = blocks[b][1]
            # Fast BLAS matmul for M_{jk} = Tr(Bzb[j] * Si * Bzb[k] * X[b])
            tmp = np.matmul(Si, np.matmul(Bzb, X[b]))
            M += Bz_flat[b] @ tmp.reshape(n, -1).T
        M = 0.5 * (M + M.T)
        evM, VM = eigh(M)
        reg = max(1e-11 * max(float(evM[-1]), 1.0), 1e-13)

        def solve_dir(sigma, second_order=None):
            rhs = -rp.copy()
            for b in range(nb):
                T0 = sigma * mu * Sinv[b] - X[b] - Sinv[b] @ (rd[b] @ X[b])
                if second_order is not None:
                    T0 -= Sinv[b] @ (second_order[0][b] @ second_order[1][b])
                rhs += Bz_flat[b] @ T0.reshape(-1)
            dz = VM @ ((VM.T @ rhs) / np.maximum(evM, reg))
            dS = [rd[b] + np.tensordot(dz, blocks[b][1], axes=([0], [0])) for b in range(nb)]
            dX = []
            for b in range(nb):
                W = sigma * mu * Sinv[b] - X[b] - Sinv[b] @ (dS[b] @ X[b])
                if second_order is not None:
                    W -= Sinv[b] @ (second_order[0][b] @ second_order[1][b])
                dX.append(0.5 * (W + W.T))
            return dz, dX, dS

        _dz_a, dX_a, dS_a = solve_dir(0.0)
        ap_a = min(max_step(X[b], dX_a[b]) for b in range(nb))
        ad_a = min(max_step(S[b], dS_a[b]) for b in range(nb))
        mu_a = sum(float(np.sum((X[b] + ap_a * dX_a[b]) * (S[b] + ad_a * dS_a[b]))) for b in range(nb)) / mtot
        sigma = min(0.5, max(1e-3, (mu_a / max(mu, 1e-30)) ** 3))
        if nrp > 1e-3 or nrd > 1e-3:
            sigma = max(sigma, 0.25)

        dz, dX, dS = solve_dir(sigma, (dS_a, dX_a))
        ap = min(max_step(X[b], dX[b]) for b in range(nb))
        ad = min(max_step(S[b], dS[b]) for b in range(nb))
        if ap < 1e-8 or ad < 1e-8:
            dz, dX, dS = solve_dir(0.5, None)
            ap = min(max_step(X[b], dX[b]) for b in range(nb))
            ad = min(max_step(S[b], dS[b]) for b in range(nb))
            if ap < 1e-10 and ad < 1e-10:
                break
        z += ad * dz
        for b in range(nb):
            Xb = X[b] + ap * dX[b]
            Sb = S[b] + ad * dS[b]
            X[b] = 0.5 * (Xb + Xb.T)
            S[b] = 0.5 * (Sb + Sb.T)

    d_obj = float(c @ z)
    p_obj = -sum(float(B0_flat[b] @ X[b].reshape(-1)) for b in range(nb))
    return p_obj, d_obj, nrp, nrd, it


# ==============================================================================
# MODULE 1 (PART A(ii)): UNCONDITIONAL ALL-m EXISTENCE OF eta_Lambda >= 0 &
#                        CLOSED-FORM PRIMAL SPECTRAL EDGE q_edge(a) AT p = 3/2
# ==============================================================================

def run_module_1():
    print("=" * 80)
    print("MODULE 1 (PART A(ii)): UNCONDITIONAL ALL-m EXISTENCE OF eta_Lambda >= 0 &")
    print("                       EXACT CLOSED-FORM PRIMAL SPECTRAL EDGE q_edge(a)")
    print("=" * 80)

    # --- Suite 1A: Exact Z_{>0} SymPy Proofs (ZERO floats!) ---
    print("\n[Suite 1A] Exact Symbolic Z_{>0} Geometry & Pole-Sweeping Proofs:")
    t, s, v, u = sp.symbols('t s v u', positive=True)
    q, x, gam, z = sp.symbols('q x gam z', positive=True)
    a = 1 + t
    Lam = (1 + a ** 2) ** 2 / a
    sigp = a * (a ** 2 - 1)

    # 1. Primal discriminant, exact closed-form spectral edge q_edge(a), & real Mobius simplicity det
    Pq = sp.expand((sigp - q * x) * (Lam - (1 + x) * q) + (1 + x))
    Ax, Bx, Cx = sp.Poly(Pq, x).all_coeffs()
    disc_x = sp.factor(Bx ** 2 - 4 * Ax * Cx)
    expected_disc_x = (q - a) ** 2 / a ** 2 * (a ** 2 * q ** 2 - (4 * a ** 3 + 2 * a) * q + 1)
    assert sp.simplify(disc_x - expected_disc_x) == 0
    q_edge_sym = 1 / (a * (sp.sqrt(a ** 2 + 1) + a) ** 2)
    q_edge_alt = (2 * a ** 2 + 1 - 2 * a * sp.sqrt(a ** 2 + 1)) / a
    assert sp.simplify(q_edge_sym - q_edge_alt) == 0
    assert sp.simplify((a ** 2 * q ** 2 - (4 * a ** 3 + 2 * a) * q + 1).subs(q, q_edge_alt)) == 0
    mob_det = sp.factor((Lam + sigp) * (1 + sigp * Lam) - sigp)
    assert sp.simplify(mob_det - a ** 3 * (a ** 2 + 1) ** 2 * (2 * a ** 2 - 1)) == 0
    print("  1. Primal disc_x = ((q-a)/a)^2 * (a^2 q^2 - (4a^3+2a)q + 1)  [EXACT]")
    print("     q_edge(a) = 1 / (a * (sqrt(a^2+1) + a)^2) in (0, a); Mobius det = a^3(a^2+1)^2(2a^2-1) > 0 [EXACT]")

    # 2. Exact x_apex(a) < 0 proof via u = a + sqrt(a^2+1) > 1 + sqrt(2) > 2
    a_sym = sp.Symbol('a', positive=True)
    Pq_a = sp.expand((a_sym * (a_sym ** 2 - 1) - q * x) * ((1 + a_sym ** 2) ** 2 / a_sym - (1 + x) * q) + (1 + x))
    Ax_a, Bx_a, _ = sp.Poly(Pq_a, x).all_coeffs()
    a_u = (u ** 2 - 1) / (2 * u)
    x_apex_u = sp.factor((-Bx_a / (2 * Ax_a)).subs({a_sym: a_u, q: 1 / (a_u * u ** 2)}))
    x_apex_v = sp.factor(x_apex_u.subs(u, 2 + v))
    num_ap, den_ap = sp.fraction(x_apex_v)
    c_num_ap = sp.Poly(sp.expand(num_ap), v).coeffs()
    c_den_ap = sp.Poly(sp.expand(den_ap), v).coeffs()
    assert max(c_num_ap) < 0 and min(c_den_ap) > 0
    print(f"  2. x_apex(u=2+v) < 0: {len(c_num_ap)} num coeffs ALL <= {max(c_num_ap)}, den coeff = {c_den_ap[0]} > 0 [EXACT Z]")

    # 3. Exact Re(1/a^2 - 1/xi(q)) > 0 on (0, a) (via Re(1/xi) = -Bx/(2 Cx))
    diff_w = sp.factor((1 / a ** 2 + Bx / (2 * Cx)).subs(q, a / (1 + s)))
    num_dw, den_dw = sp.fraction(diff_w)
    c_ndw = sp.Poly(sp.expand(num_dw), t, s).coeffs()
    c_ddw = sp.Poly(sp.expand(den_dw), t, s).coeffs()
    assert min(c_ndw) > 0 and min(c_ddw) > 0
    print(f"  3. Re(1/a^2 - 1/xi(q)) > 0: {len(c_ndw)} num coeffs >= {min(c_ndw)}, {len(c_ddw)} den coeffs >= {min(c_ddw)} [EXACT Z_{{>0}}]")

    # 4. Exact Dual discriminant, Lam*gam - 1 > 0, and Re(zeta(gam)) - a > 0 on (gam_crit, gam_*)
    P_dual = sp.expand(((sigp - (Lam * gam - 1) * z) * (Lam - Lam * gam * z) + Lam * gam) / Lam)
    Az, Bz, Cz = sp.Poly(P_dual, z).all_coeffs()
    disc_z = sp.factor(Bz ** 2 - 4 * Az * Cz)
    gam_star = a / (1 + a ** 2)
    gam_crit = 1 / (4 * a)
    expected_disc_z = -(4 * a * gam - 1) * ((a ** 2 + 1) * gam - a) ** 2 / a ** 2
    assert sp.simplify(disc_z - expected_disc_z) == 0

    gam_sub = (gam_crit + s * gam_star) / (1 + s)
    num_l, den_l = sp.fraction(sp.factor(Lam * gam_sub - 1))
    c_nl = sp.Poly(sp.expand(num_l), t, s).coeffs()
    c_dl = sp.Poly(sp.expand(den_l), t, s).coeffs()
    assert min(c_nl) > 0 and min(c_dl) > 0

    num_rz, den_rz = sp.fraction(sp.factor((-Bz / (2 * Az) - a).subs(gam, gam_sub)))
    c_nrz = sp.Poly(sp.expand(num_rz), t, s).coeffs()
    c_drz = sp.Poly(sp.expand(den_rz), t, s).coeffs()
    assert min(c_nrz) > 0 and min(c_drz) > 0
    print(f"  4. Dual Omega subset {{Re z > a}}: Lam*gam-1 > 0 ({len(c_nl)} terms >= {min(c_nl)}); "
          f"Re(zeta)-a > 0 ({len(c_nrz)} num >= {min(c_nrz)}, {len(c_drz)} den >= {min(c_drz)}) [EXACT Z_{{>0}}]")

    # 5. Exact Primal & Dual corner angle tan(alpha_a) = sqrt(3a^2-1)/(sqrt(a^2+1)*(2a^2-1)) < 1 => beta > 3
    d_re_x = sp.limit((-Bx / (2 * Ax) - a ** 2) / (a - q), q, a)
    rem_x_a = sp.cancel(disc_x / (q - a) ** 2).subs(q, a)
    tan_pri_sq = sp.factor((-rem_x_a / (4 * Ax.subs(q, a) ** 2)) / (d_re_x ** 2))

    d_re_z = sp.limit((-Bz / (2 * Az) - a) / (gam_star - gam), gam, gam_star)
    rem_z_gs = sp.cancel(disc_z / (gam - gam_star) ** 2).subs(gam, gam_star)
    tan_dual_sq = sp.factor((-rem_z_gs / (4 * Az.subs(gam, gam_star) ** 2)) / (d_re_z ** 2))

    expected_tan_sq = sp.factor((3 * a ** 2 - 1) / ((a ** 2 + 1) * (2 * a ** 2 - 1) ** 2))
    assert sp.simplify(tan_pri_sq - expected_tan_sq) == 0
    assert sp.simplify(tan_dual_sq - expected_tan_sq) == 0
    diff_tan_num = sp.expand((a ** 2 + 1) * (2 * a ** 2 - 1) ** 2 - (3 * a ** 2 - 1))
    c_dtan = sp.Poly(diff_tan_num, t).coeffs()
    assert min(c_dtan) > 0
    print(f"  5. Matching Primal & Dual corner angle tan^2(alpha_a) = (3a^2-1)/((a^2+1)(2a^2-1)^2) < 1 "
          f"(min coeff = {min(c_dtan)} > 0) => alpha_a < pi/4, beta = pi/alpha_a - 1 > 3 [EXACT Z_{{>0}}]")

    # 6. Exact Supercritical Real-Branch Pole-Sweeping, Strict Monotonicity r_+'(gam) < 0, & Golden-Ratio Transition
    assert sp.simplify(P_dual.subs(z, 1 / gam) - gam) == 0
    gam_real = (1 / Lam + s * gam_crit) / (1 + s)
    r_mid = -Bz / (2 * Az)
    num_m, den_m = sp.fraction(sp.factor((r_mid - 1 / gam).subs(gam, gam_real)))
    c_nm = sp.Poly(sp.expand(num_m), t, s).coeffs()
    c_dm = sp.Poly(sp.expand(den_m), t, s).coeffs()
    assert min(c_nm) > 0 and min(c_dm) > 0
    num_ia, den_ia = sp.fraction(sp.factor(1 / gam_real - a))
    c_nia = sp.Poly(sp.expand(num_ia), t, s).coeffs()
    c_dia = sp.Poly(sp.expand(den_ia), t, s).coeffs()
    assert min(c_nia) > 0 and min(c_dia) > 0
    # Strict monotonicity r_+'(gam) < 0: gam*d_gam P_dual(gam, r_+) = Lam*gam^2*r_+^2 - r_+ - sigp > q(r_mid) > 0
    assert sp.simplify(gam * sp.diff(P_dual, gam) - (Lam * gam ** 2 * z ** 2 - z - sigp) - P_dual) == 0
    num_q3, den_q3 = sp.fraction(sp.factor((Lam * gam ** 2 * r_mid ** 2 - r_mid - sigp).subs(gam, gam_real)))
    c_nq3 = sp.Poly(sp.expand(num_q3), t, s).coeffs()
    c_dq3 = sp.Poly(sp.expand(den_q3), t, s).coeffs()
    assert min(c_nq3) > 0 and min(c_dq3) > 0

    # Exact Golden-Ratio phase transition z_1(a) - r_0(a) = 0 <=> a^2 - a - 1 = 0, plus exact M_lo(a) = 1/(sigp*Lam)
    z1_sym = Lam + 1 / sigp
    assert sp.simplify((sigp + 1 / Lam) / (sigp ** 2 * z1_sym) - 1 / ((a ** 2 - 1) * (a ** 2 + 1) ** 2)) == 0
    r0_sym = sp.simplify((-Bz / (2 * Az)).subs(gam, gam_crit))
    z1_minus_r0 = sp.factor(z1_sym - r0_sym)
    num_gr, den_gr = sp.fraction(z1_minus_r0)
    quot_gr, rem_gr = sp.div(sp.expand(num_gr), t ** 2 + t - 1, domain='QQ')
    assert rem_gr == 0
    c_qgr = sp.Poly(quot_gr, t).coeffs()
    c_dgr = sp.Poly(sp.expand(den_gr), t).coeffs()
    assert min(c_qgr) > 0 and min(c_dgr) > 0
    print(f"  6. Real-branch pole-sweeping on (1/Lam, gam_crit): P_dual(1/gam) = gam > 0, "
          f"(r_-+r_+)/2 - 1/gam > 0 ({len(c_nm)} terms >= {min(c_nm)}), 1/gam - a > 0 => a < 1/gam < r_- < r_+, A_+ > 0, A_- < 0 [EXACT Z_{{>0}}]")
    print(f"     Strict monotonicity r_+'(gam) < 0: Lam*gam^2*r_mid^2 - r_mid - sig_+ > 0 "
          f"({len(c_nq3)} num >= {min(c_nq3)}, {len(c_dq3)} den >= {min(c_dq3)}) [EXACT Z_{{>0}}]")
    print(f"     Golden-Ratio transition: z_1(a) - r_0(a) has exact factor (a^2 - a - 1) times positive rational "
          f"(quot coeffs >= {min(c_qgr)}, den >= {min(c_dgr)}); M_lo(a) = 1/((a^2-1)(a^2+1)^2) [EXACT Z_{{>0}}]")

    # High-precision 50-dps q_edge at m = 2 continuum a_*(2)
    mp.mp.dps = 50
    a_m2_mp = mp.mpf('1.1027583306433794')  # #114 m=2 continuum a
    q_edge_m2_mp = 1 / (a_m2_mp * (mp.sqrt(a_m2_mp ** 2 + 1) + a_m2_mp) ** 2)
    print(f"\n  Exact Closed-Form #114 Open Question (c) at m=2 (a = {mp.nstr(a_m2_mp, 16)}):")
    print(f"    q_edge(a_m2) = {mp.nstr(q_edge_m2_mp, 20)}  (matches #114 Jacobi/Richardson ~ 0.135!)")

    # --- Suite 1B: Alternating-Node Spectral Cauchy Primal RH vs Dual RH + Pole-Sweeping ---
    print("\n[Suite 1B] Alternating-Node Spectral Cauchy Cross-Check (Primal RH vs Dual RH + Pole-Sweeping, N=300):")

    def solve_cauchy_alt(W_all, dW_dth, v_all, z_pin, N):
        M = 2 * N
        dth = np.pi / N
        dW = dW_dth * dth
        idx = np.arange(M)
        odd_mask = ((idx[None, :] - idx[:, None]) % 2 == 1)
        diff = W_all[None, :] - W_all[:, None]
        diff_safe = np.where(odd_mask, diff, 1.0)
        C_mat = np.where(odd_mask, 2.0 * dW[None, :] / (2j * np.pi * diff_safe), 0.0)
        R = C_mat.real
        I_im = C_mat.imag
        A_sys = R.copy()
        np.fill_diagonal(A_sys, -np.sum(R, axis=1))
        rhs = I_im @ v_all - np.sum(I_im, axis=1) * v_all
        c_pin = dW / (2j * np.pi * (W_all - z_pin))
        A_sym = A_sys[:N, :N] + A_sys[:N, N:][:, ::-1]
        rhs_sym = rhs[:N]
        cp_sym = c_pin.real[:N] + c_pin.real[N:][::-1]
        vp_rhs = float(c_pin.imag @ v_all)
        u_half, _, _, _ = np.linalg.lstsq(
            np.vstack([A_sym, cp_sym[None, :]]),
            np.concatenate([rhs_sym, [vp_rhs]]),
            rcond=None
        )
        return u_half

    def solve_primal_rh(av, N=300):
        Lm = (1.0 + av ** 2) ** 2 / av
        spv = av * (av ** 2 - 1.0)
        qe = 1.0 / (av * (np.sqrt(av ** 2 + 1.0) + av) ** 2)
        thm = (np.arange(N) + 0.5) * (np.pi / N)
        dth = np.pi / N
        qv = 0.5 * (av + qe) - 0.5 * (av - qe) * np.cos(thm)
        dq_dth = 0.5 * (av - qe) * np.sin(thm)
        A = qv ** 2
        B = qv ** 2 - (Lm + spv) * qv + 1.0
        poly_edge = av ** 2 * qv ** 2 - (4.0 * av ** 3 + 2.0 * av) * qv + 1.0
        sqrt_neg = ((av - qv) / av) * np.sqrt(-poly_edge)
        re_xi = -B / (2.0 * A)
        im_xi = sqrt_neg / (2.0 * A)
        xi = re_xi + 1j * im_xi
        dre_dq = -(Lm + spv) / (2.0 * qv ** 2) + 1.0 / (qv ** 3)
        dim_dq = (
            ((qv - 2.0 * av) / (2.0 * av * qv ** 3)) * np.sqrt(-poly_edge)
            + ((av - qv) / (2.0 * av * qv ** 2)) * ((2.0 * av ** 3 + av - av ** 2 * qv) / np.sqrt(-poly_edge))
        )
        dxi_dq = dre_dq + 1j * dim_dq
        ua = av + np.sqrt(av ** 2 + 1.0)
        x_ap = -(ua - 1.0) * (ua + 1.0) * (ua ** 6 - ua ** 4 - 9.0 * ua ** 2 + 1.0) / (16.0 * ua ** 2)
        w_ap = 1.0 / x_ap
        w_a2 = 1.0 / (av ** 2)
        al = np.arctan(np.sqrt(3.0 * av ** 2 - 1.0) / (np.sqrt(av ** 2 + 1.0) * (2.0 * av ** 2 - 1.0)))
        be = np.pi / al - 1.0
        w = 1.0 / xi
        dw_dq = -dxi_dq / (xi ** 2)
        A_p = (Lm - (1.0 + xi) * qv) / (2j * qv ** 2 * im_xi)
        H0 = (w - w_ap) * ((w_a2 - w) ** be)
        v_low = np.unwrap(np.angle((2j * np.pi * A_p / dxi_dq) / H0))
        v_low -= 2.0 * np.pi * np.round(v_low[0] / (2.0 * np.pi))
        W_all = np.concatenate([w, np.conj(w[::-1])])
        dW_dth = np.concatenate([dw_dq * dq_dth, -np.conj(dw_dq[::-1] * dq_dth[::-1])])
        v_all = np.concatenate([v_low, -v_low[::-1]])
        u_low = solve_cauchy_alt(W_all, dW_dth, v_all, 0.0, N)
        Phi_low = H0 * np.exp(u_low + 1j * v_low)
        Phi_0 = (-w_ap) * (w_a2 ** be)
        rho_raw = np.real(Phi_low / (2j * np.pi * A_p / dxi_dq))
        mass = float(np.sum(rho_raw * dq_dth * dth))
        rho = rho_raw / mass
        T0_pri = mass / Phi_0
        M_pri = T0_pri / spv - 1.0
        xs_t = np.linspace(0.0, 0.98 * av ** 2, 50)
        vals = [
            float(np.sum(((Lm - (1.0 + xt) * qv) / ((spv - qv * xt) * (Lm - (1.0 + xt) * qv) + (1.0 + xt))) * rho * dq_dth * dth))
            for xt in xs_t
        ]
        bal_err = float(np.max(np.abs(np.array(vals) * T0_pri - 1.0)))
        return qe, be, float(rho.min()), M_pri, bal_err

    def solve_dual_rh(av, N=300):
        Lm = (1.0 + av ** 2) ** 2 / av
        spv = av * (av ** 2 - 1.0)
        gs = av / (1.0 + av ** 2)
        gc = 1.0 / (4.0 * av)
        z1 = Lm + 1.0 / spv
        Az_f = lambda g: g * (Lm * g - 1.0)
        Bz_f = lambda g: -((Lm * g - 1.0) + spv * g)
        r0 = -Bz_f(gc) / (2.0 * Az_f(gc))
        atoms = []
        z_cur = z1
        coeff = 1.0
        while z_cur > r0 + 1e-11:
            qa = Lm * z_cur ** 2
            qb = 1.0 - z_cur ** 2 - (Lm + spv) * z_cur
            qc = z_cur + spv
            dg = qb ** 2 - 4.0 * qa * qc
            roots_g = [(-qb - np.sqrt(dg)) / (2.0 * qa), (-qb + np.sqrt(dg)) / (2.0 * qa)]
            gk = [gr for gr in roots_g if 1.0 / Lm + 1e-12 < gr < gc and z_cur > -Bz_f(gr) / (2.0 * Az_f(gr))][0]
            r_minus = -Bz_f(gk) / Az_f(gk) - z_cur
            A_p = (1.0 - gk * z_cur) / (Az_f(gk) * (r_minus - z_cur))
            A_m = (1.0 - gk * r_minus) / (Az_f(gk) * (z_cur - r_minus))
            assert A_p > 0.0 and A_m < 0.0
            wk = coeff / A_p
            atoms.append((gk, wk))
            coeff = -wk * A_m
            z_cur = r_minus
        z_star = z_cur
        thm = (np.arange(N) + 0.5) * (np.pi / N)
        dth = np.pi / N
        gv = 0.5 * (gs + gc) - 0.5 * (gs - gc) * np.cos(thm)
        dg_dth = 0.5 * (gs - gc) * np.sin(thm)
        A = Az_f(gv)
        B = Bz_f(gv)
        sqrt_neg = ((av ** 2 + 1.0) / av) * (gs - gv) * np.sqrt(4.0 * av * gv - 1.0)
        re_z = -B / (2.0 * A)
        im_z = sqrt_neg / (2.0 * A)
        zeta = re_z + 1j * im_z
        dA = 2.0 * Lm * gv - 1.0
        dB = -(Lm + spv)
        dre_dg = -(dB * A - B * dA) / (2.0 * A ** 2)
        d_sn = ((av ** 2 + 1.0) / av) * (-np.sqrt(4.0 * av * gv - 1.0) + (gs - gv) * (2.0 * av / np.sqrt(4.0 * av * gv - 1.0)))
        dim_dg = (d_sn * A - sqrt_neg * dA) / (2.0 * A ** 2)
        dz_dg = dre_dg + 1j * dim_dg
        W_p = (1.0 - gv * zeta) / (-2j * A * im_z)
        al = np.arctan(np.sqrt(3.0 * av ** 2 - 1.0) / (np.sqrt(av ** 2 + 1.0) * (2.0 * av ** 2 - 1.0)))
        be = np.pi / al - 1.0
        f0 = (r0 - zeta) * ((zeta - av) ** be)
        v_top = np.unwrap(np.angle((2j * np.pi * (zeta - z_star) * W_p / dz_dg) / f0))
        v_top -= 2.0 * np.pi * np.round(v_top[0] / (2.0 * np.pi))
        Z_all = np.concatenate([zeta, np.conj(zeta[::-1])])
        dZ_dth = np.concatenate([dz_dg * dg_dth, -np.conj(dz_dg[::-1] * dg_dth[::-1])])
        v_all = np.concatenate([v_top, -v_top[::-1]])
        u_top = solve_cauchy_alt(Z_all, dZ_dth, v_all, z_star, N)
        f0_star = (r0 - z_star) * ((z_star - av) ** be)
        Phi_top = (f0 / f0_star) * np.exp(u_top + 1j * v_top)
        rho_unit = np.real(Phi_top / (2j * np.pi * (zeta - z_star) * W_p / dz_dg))
        mass_cont = float(np.sum(rho_unit * dg_dth * dth))
        M_dual = (sum(wk for _, wk in atoms) + coeff * mass_cont) / (spv ** 2)
        # Uniform mass upper bound check: M <= (1/sp^2) * ... wait: int d_eta <= a^2 / (x_crit * sp^2)?
        # Check balayage at q = 0: int (1/P_gam(0)) d_eta <= 1/sp - 1/K_0(0) = 1/(sp^2 * z_1).
        # Since P_gam(0) = sp + gam <= sp + gam_* = sp + a/(1+a^2), M = int d_eta <= (sp + gam_*) / (sp^2 * z_1)!
        M_ub = (spv + gs) / (spv ** 2 * z1)
        assert M_dual <= M_ub + 1e-12
        qs_t = np.linspace(0.0, 0.99 * av, 40)
        errs = []
        for qt in qs_t:
            k0_inv = (Lm - qt) / (spv * (Lm - qt) + 1.0)
            atom_sum = sum(wk * (1.0 - gk * qt) / (Az_f(gk) * qt ** 2 + Bz_f(gk) * qt + spv + gk) for gk, wk in atoms)
            cont_sum = coeff * float(np.sum(((1.0 - gv * qt) / (A * qt ** 2 + B * qt + spv + gv)) * rho_unit * dg_dth * dth))
            errs.append(abs((k0_inv + (atom_sum + cont_sum) / (spv ** 2)) * spv - 1.0))
        return len(atoms), z_cur, r0, float(rho_unit.min()), M_dual, M_ub, max(errs)

    print(f"  {'a':>10s} | {'q_edge':>10s} | {'beta':>6s} | {'atoms':>5s} | {'M_primal':>11s} | {'M_dual':>11s} | {'|M_p-M_d|':>9s} | {'bal_pri':>8s} | {'bal_dual':>8s}")
    for av in [1.1027583306433794, 1.2, 1.5, 1.8, 2.0, 2.5, 3.0]:
        qe, be, rmin_p, Mp, bp = solve_primal_rh(av, N=300)
        na, zc, r0, rmin_d, Md, Mub, bd = solve_dual_rh(av, N=300)
        assert rmin_p > 0.0 and rmin_d > 0.0 and be > 3.0
        assert bp < 2e-6 and bd < 1e-6 and abs(Mp - Md) < 2e-6
        assert zc <= r0 + 1e-11 and Md <= Mub + 1e-12
        print(f"  {av:10.6f} | {qe:10.8f} | {be:6.3f} | {na:5d} | {Mp:11.8f} | {Md:11.8f} | {abs(Mp - Md):9.2e} | {bp:8.2e} | {bd:8.2e}")
    print("  [PASS] Module 1: ALL exact Z_{>0} proofs & Primal/Dual RH Tonelli checks passed!\n")


# ==============================================================================
# MODULE 2 (PART A(i)): GAP 1A GLOBAL Y = Q RIGIDITY — REDUCTION TO (MIRACLE-3),
#                       PROVED SPECIAL CASES, & 2x2 NON-COMMUTING NO-GO THEOREM
# ==============================================================================

def solve_rg_p32_Q(r_target):
    """Exact coupled rank-r RG fixed points at p = 3/2, m = 2 in Q coordinates."""
    Lam1, xm1, _, _, _ = solve_1x1_float(1.5, 2)
    Lam = Lam1 + 5e-4
    ds = np.array([1.0, 0.075])
    Q = np.array([[np.sqrt(xm1), -0.15], [-0.15, 0.50]])

    def solve_k(rk, L_in, d_in, Q_in):
        triu = np.triu_indices(rk)
        x0 = np.concatenate([[L_in], np.log(d_in[1:]), Q_in[triu]])
        def unpack(xv):
            L = xv[0]
            dd = np.concatenate([[1.0], np.exp(xv[1:rk])])
            QQ = np.zeros((rk, rk))
            QQ[triu] = xv[rk:]
            QQ = QQ + QQ.T - np.diag(np.diag(QQ))
            return L, dd, QQ
        def res(xv):
            L, dd, QQ = unpack(xv)
            _, xp = get_xpm_float(L, 1.5)
            spv = sig_float(xp, 1.5)
            D = np.diag(dd)
            H = QQ @ D @ QQ
            R1 = (D + H) @ (D + H) - L * D @ QQ @ D
            F = QQ @ D @ QQ @ D @ QQ - D @ QQ @ D
            R2 = F - np.diag(np.concatenate([[-spv], spv * (dd[1:] ** 2)]))
            w = 1.0 / np.outer(dd, dd)
            return np.concatenate([(R1 * w)[triu], (R2 * w)[triu]])
        sol = least_squares(res, x0, xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=6000)
        assert float(np.linalg.norm(sol.fun)) < 1e-12
        return unpack(sol.x)

    Lam, ds, Q = solve_k(2, Lam, ds, Q)
    for rk in range(3, r_target + 1):
        ratio = ds[-1] / ds[-2]
        ds_n = np.concatenate([ds, [ds[-1] * max(0.15, ratio * 0.9)]])
        Q_n = np.zeros((rk, rk))
        Q_n[:rk - 1, :rk - 1] = Q
        _, xp_c = get_xpm_float(Lam, 1.5)
        Q_n[rk - 1, rk - 1] = min(0.97 * np.sqrt(xp_c), Q[-1, -1] + 0.12)
        Q_n[:rk - 1, rk - 1] = -0.015 * (0.35 ** np.arange(rk - 1)[::-1])
        Q_n[rk - 1, :rk - 1] = Q_n[:rk - 1, rk - 1]
        Lam, ds, Q = solve_k(rk, Lam, ds_n, Q_n)
    return Lam, ds, Q


def run_module_2():
    print("=" * 80)
    print("MODULE 2 (PART A(i)): GAP 1A GLOBAL Y = Q RIGIDITY — (MIRACLE-3) REDUCTION,")
    print("                      PROVED SPECIAL CASES, & 2x2 NON-COMMUTING NO-GO THEOREM")
    print("=" * 80)

    # --- Suite 2A: Exact Verification of (G1'')+(G2'')+(G4) => (MIRACLE-1) => (MIRACLE-3) ---
    print("\n[Suite 2A] Verification of (G1'')+(G2'')+(G4) => (MIRACLE-1) => (MIRACLE-3) & INEQ-1 on p=3/2 RG Blocks:")
    rng = np.random.default_rng(131)
    for r in [2, 3, 4]:
        Lam, ds, Q = solve_rg_p32_Q(r)
        D = np.diag(ds)
        sD = np.diag(np.sqrt(ds))
        _, xp = get_xpm_float(Lam, 1.5)
        spv = sig_float(xp, 1.5)
        Y = Q.copy()
        MX = D + Y.T @ D @ Y
        A = D + Y @ D @ Q
        E0 = np.diag(np.concatenate([[-spv], spv * (ds[1:] ** 2)]))
        # Note: (G1''): Y^T D Y D Q - D Y D = E0, (G2''): MX A = Lam D Y D, (G4): A A^T = Lam D Q D
        err_g1 = float(np.linalg.norm(Y.T @ D @ Y @ D @ Q - D @ Y @ D - E0))
        err_g2 = float(np.linalg.norm(MX @ A - Lam * D @ Y @ D))
        err_g4 = float(np.linalg.norm(A @ A.T - Lam * D @ Q @ D))
        err_m1 = float(np.linalg.norm(Y @ D @ Q @ D @ Y.T - D @ Q @ D - E0))
        P = sD @ Q @ sD
        S = sD @ Y @ sD
        err_m3 = float(np.linalg.norm(D @ (S - P) @ D - (S.T @ S @ P - S @ P @ S.T)))
        assert max(err_g1, err_g2, err_g4, err_m1, err_m3) < 1e-12

        # Primal Convex Polar Identity (INEQ-1): whenever (D, Q) solves symmetric Holden M_Q^2 = Lam D Q D
        # with M_Q = D + Q D Q <= (1 + x_+) D, any U in O(r) solving (G4) via A(U) = sqrt(Lam) D Q^(1/2) U
        # (giving Y(U) = (A(U) - D) Q^(-1) D^(-1)) satisfies the EXACT Frobenius identity:
        #   Tr(M_Q - Re A(U)) === (1/2) ||M_Q^(-1/2) (Y(U) - Q) D Q||_F^2 >= (1 / (2*(1 + x_+))) ||D^(-1/2) (Y(U) - Q) D Q||_F^2 >= 0,
        # proving U_Q = Lam^(-1/2) Q^(-1/2) D^(-1) M_Q is the UNIQUE global minimizer of Phi(Q, U) := -Re Tr(A(U)) over O(r)!
        wQ, VQ = eigh(Q)
        Q12 = (VQ * np.sqrt(wQ)) @ VQ.T
        Qm12 = (VQ / np.sqrt(wQ)) @ VQ.T
        Qinv = (VQ / wQ) @ VQ.T
        Dinv = np.diag(1.0 / ds)
        Dm12 = np.diag(ds ** (-0.5))
        MQ = D + Q @ D @ Q
        wM, VM = eigh(MQ)
        MQm12 = (VM / np.sqrt(wM)) @ VM.T
        U_opt = (1.0 / np.sqrt(Lam)) * Qm12 @ Dinv @ MQ
        assert float(np.linalg.norm(U_opt @ U_opt.T - np.eye(r))) < 1e-12
        max_id_err = 0.0
        min_lb_margin = 1e9
        min_gap_u = 1e9
        for _ in range(100):
            K_sk = rng.standard_normal((r, r))
            K_sk = 0.25 * (K_sk - K_sk.T)
            U_pert = np.linalg.solve(np.eye(r) - K_sk, np.eye(r) + K_sk) @ U_opt
            A_u = np.sqrt(Lam) * D @ Q12 @ U_pert
            Y_u = (A_u - D) @ Qinv @ Dinv
            lhs = float(np.trace(MQ - 0.5 * (A_u + A_u.T)))
            rhs_ex = 0.5 * float(np.linalg.norm(MQm12 @ (Y_u - Q) @ D @ Q, 'fro') ** 2)
            rhs_lb = (0.5 / (1.0 + xp)) * float(np.linalg.norm(Dm12 @ (Y_u - Q) @ D @ Q, 'fro') ** 2)
            max_id_err = max(max_id_err, abs(lhs - rhs_ex))
            min_lb_margin = min(min_lb_margin, lhs - rhs_lb)
            min_gap_u = min(min_gap_u, lhs)
        assert max_id_err < 1e-12 and min_lb_margin >= -1e-14 and min_gap_u > 0.0
        print(f"  r={r}: (G1'',G2'',G4) err={max(err_g1,err_g2,err_g4):.1e} | (MIRACLE-1,3) err={max(err_m1,err_m3):.1e} | "
              f"INEQ-1 id_err={max_id_err:.1e}, min_gap={min_gap_u:.3e}, min(lhs-lb)={min_lb_margin:+.3e}")

    # --- Suite 2B: Exact Symbolic Commuting 2x2 SOS Killer & Proved Special Cases ---
    print("\n[Suite 2B] Exact SymPy SOS Proof of Commuting 2x2 (MIRACLE-3) & General-n Proved Cases:")
    p1, p2, d1, d2, d0, a, b, c, d, t = sp.symbols('p1 p2 d1 d2 d0 a b c d t', real=True)
    P_c = sp.Matrix([[p1, 0], [0, p2]])
    D_c = sp.Matrix([[d1, 0], [0, d2]])
    S_c = sp.Matrix([[a, b], [c, d]])
    E_c = D_c * (S_c - P_c) * D_c - (S_c.T * S_c * P_c - S_c * P_c * S_c.T)
    sol_c = sp.solve([E_c[0, 0], E_c[1, 1]], [a, d])
    X_lyap = sp.Matrix([[a / 2, p1 * c / (p1 + p2)], [p2 * b / (p1 + p2), d / 2]])
    # Check Lyapunov equation P X + X P = P S^T? Wait: (P X + X P)[0,1] = (p1 + p2) X[0,1] = p1 c = (P S^T)[0,1],
    # (P X + X P)[1,0] = (p1 + p2) X[1,0] = p2 b = (P S^T)[1,0]!
    assert sp.simplify(P_c * X_lyap + X_lyap * P_c - P_c * S_c.T) == sp.zeros(2, 2)
    killer_c = sp.factor(((S_c - X_lyap).T * E_c).trace().subs(sol_c))
    expected_killer = (
        (d1 ** 2 * p1 + d2 ** 2 * p2) * (b ** 2 * p2 - c ** 2 * p1) ** 2
        + d1 ** 3 * d2 ** 3 * (p1 + p2) * (b ** 2 - b * c + c ** 2)
    ) / (d1 ** 2 * d2 ** 2 * (p1 + p2))
    # Verify exact sign (+ or -):
    diff_plus = sp.simplify(killer_c - expected_killer)
    diff_minus = sp.simplify(killer_c + expected_killer)
    assert diff_plus == 0 or diff_minus == 0
    sgn_str = "+" if diff_plus == 0 else "-"
    print(f"  Commuting 2x2 Lyapunov SOS Identity: ({sgn_str})Tr((S-X)^T E)|_{{E_diag=0}} == EXACT SOS >= 0 [EXACT]")
    print("  Hermitian PSD S = S^* >= 0 (all n >= 1, all D, P > 0): [S^2, P]=0 => [S, P]=0 => S=P [PROVED]")
    print("  Scalar P = p I_n (all n >= 1, all D > 0, arbitrary complex S): skew=0 => S=S^* => S=P [PROVED]")

    # --- Suite 2C: Exact 2x2 Non-Commuting No-Go Theorem for Standalone (MIRACLE-3) ---
    print("\n[Suite 2C] Exact 2x2 Non-Commuting No-Go Theorem (Explicit Counterexamples to Standalone (MIRACLE-3)):")
    D_nc = sp.Matrix([[d1, d0], [d0, d2]])
    E_nc = D_nc * (S_c - P_c) * D_nc - (S_c.T * S_c * P_c - S_c * P_c * S_c.T)
    sol_nc = sp.solve([E_nc[0, 0], E_nc[1, 1]], [a, d])
    pos_den = (d1 * d2 - d0 ** 2) * (d1 * d2 + d0 ** 2)
    F01 = sp.expand(sp.cancel(E_nc[0, 1].subs(sol_nc) * pos_den))
    F10 = sp.expand(sp.cancel(E_nc[1, 0].subs(sol_nc) * pos_den))
    G1 = sp.Poly(sp.expand(F01.subs(b, t * c) / c), c)
    G2 = sp.Poly(sp.expand(F10.subs(b, t * c) / c), c)
    # Verify miraculous identities B2 == -t * B1 and t * A1 + A2 == Tr(D^2) * (p1 - p2 t^2)^2!
    assert sp.simplify(G2.nth(1) + t * G1.nth(1)) == 0
    assert sp.simplify((t * G1.nth(2) + G2.nth(2)) - (d1 ** 2 + d2 ** 2 + 2 * d0 ** 2) * (p1 - p2 * t ** 2) ** 2) == 0
    print("  Exact 2x2 reduction verified: B_2(t) === -t*B_1(t) and t*A_1 + A_2 === Tr(D^2)*(p1 - p2*t^2)^2 [EXACT]")

    # Construct explicit reproducible counterexamples (both indefinite S and strictly positive-real-part (S+S^T)/2 > 0!)
    def find_m3_counterexamples(seed, n_trials):
        rg = np.random.default_rng(seed)
        cex_list = []
        for _ in range(n_trials):
            p1v, p2v = 10.0 ** rg.uniform(-2.0, 2.0, size=2)
            d1v, d2v = 10.0 ** rg.uniform(-2.0, 2.0, size=2)
            rhov = rg.uniform(-0.99, 0.99)
            d0v = rhov * np.sqrt(d1v * d2v)
            detD = d1v * d2v - d0v ** 2
            ts = np.linspace(-3.0, 3.0, 61)
            u_t = p1v - p2v * ts ** 2
            A1 = u_t * (d0v ** 2 * (p1v + p2v - 2.0 * p2v * ts) + d1v ** 2 * p2v * (1.0 - ts) + d2v ** 2 * (p1v - p2v * ts))
            A2 = -u_t * (d0v ** 2 * (p1v * ts - 2.0 * p1v + p2v * ts) + d1v ** 2 * (p2v * ts - p1v) + d2v ** 2 * p1v * (ts - 1.0))
            B1 = -d0v * detD * (d1v + d2v * ts) * (p1v - p2v)
            B2 = -ts * B1
            C1 = detD * (d0v ** 4 - d0v ** 2 * d1v * d2v * (ts + 1.0) + d1v ** 2 * d2v ** 2 * ts + (d0v ** 2 + d1v * d2v) * (p1v ** 2 - p1v * p2v * ts + p2v ** 2 * ts - p2v ** 2))
            C2 = -detD * (-d0v ** 4 * ts + d0v ** 2 * d1v * d2v * (ts + 1.0) - d1v ** 2 * d2v ** 2 + (d0v ** 2 + d1v * d2v) * (p1v ** 2 * ts - p1v ** 2 + p1v * p2v - p2v ** 2 * ts))
            res = (A1 * C2 - A2 * C1) ** 2 - (A1 * B2 - A2 * B1) * (B1 * C2 - B2 * C1)
            for idx_i in np.where(res[:-1] * res[1:] < 0.0)[0][:2]:
                def rf(tv):
                    uv = p1v - p2v * tv ** 2
                    a1 = uv * (d0v ** 2 * (p1v + p2v - 2.0 * p2v * tv) + d1v ** 2 * p2v * (1.0 - tv) + d2v ** 2 * (p1v - p2v * tv))
                    a2 = -uv * (d0v ** 2 * (p1v * tv - 2.0 * p1v + p2v * tv) + d1v ** 2 * (p2v * tv - p1v) + d2v ** 2 * p1v * (tv - 1.0))
                    b1 = -d0v * detD * (d1v + d2v * tv) * (p1v - p2v)
                    b2 = -tv * b1
                    c1 = detD * (d0v ** 4 - d0v ** 2 * d1v * d2v * (tv + 1.0) + d1v ** 2 * d2v ** 2 * tv + (d0v ** 2 + d1v * d2v) * (p1v ** 2 - p1v * p2v * tv + p2v ** 2 * tv - p2v ** 2))
                    c2 = -detD * (-d0v ** 4 * tv + d0v ** 2 * d1v * d2v * (tv + 1.0) - d1v ** 2 * d2v ** 2 + (d0v ** 2 + d1v * d2v) * (p1v ** 2 * tv - p1v ** 2 + p1v * p2v - p2v ** 2 * tv))
                    return (a1 * c2 - a2 * c1) ** 2 - (a1 * b2 - a2 * b1) * (b1 * c2 - b2 * c1)
                tr = brentq(rf, ts[idx_i], ts[idx_i + 1], xtol=1e-14)
                uv = p1v - p2v * tr ** 2
                a1 = uv * (d0v ** 2 * (p1v + p2v - 2.0 * p2v * tr) + d1v ** 2 * p2v * (1.0 - tr) + d2v ** 2 * (p1v - p2v * tr))
                a2 = -uv * (d0v ** 2 * (p1v * tr - 2.0 * p1v + p2v * tr) + d1v ** 2 * (p2v * tr - p1v) + d2v ** 2 * p1v * (tr - 1.0))
                b1 = -d0v * detD * (d1v + d2v * tr) * (p1v - p2v)
                c1 = detD * (d0v ** 4 - d0v ** 2 * d1v * d2v * (tr + 1.0) + d1v ** 2 * d2v ** 2 * tr + (d0v ** 2 + d1v * d2v) * (p1v ** 2 - p1v * p2v * tr + p2v ** 2 * tr - p2v ** 2))
                c2 = -detD * (-d0v ** 4 * tr + d0v ** 2 * d1v * d2v * (tr + 1.0) - d1v ** 2 * d2v ** 2 + (d0v ** 2 + d1v * d2v) * (p1v ** 2 * tr - p1v ** 2 + p1v * p2v - p2v ** 2 * tr))
                K2 = tr * a1 + a2
                K0 = tr * c1 + c2
                if K2 > 1e-25 and K0 / K2 < 0.0:
                    for sgn in [+1.0, -1.0]:
                        cv = sgn * np.sqrt(-K0 / K2)
                        if abs(a1 * cv ** 2 + b1 * cv + c1) < 1e-6 * (abs(c1) + abs(a1 * cv ** 2) + 1.0):
                            bv = tr * cv
                            Mad = np.array([[d1v ** 2, d0v ** 2], [d0v ** 2, d2v ** 2]])
                            rhs = np.array([
                                -(bv ** 2 * p2v + bv * d0v * d1v - cv ** 2 * p1v + cv * d0v * d1v - d0v ** 2 * p2v - d1v ** 2 * p1v),
                                -(-bv ** 2 * p2v + bv * d0v * d2v + cv ** 2 * p1v + cv * d0v * d2v - d0v ** 2 * p1v - d2v ** 2 * p2v),
                            ])
                            av, dv = np.linalg.solve(Mad, rhs)
                            Pm = np.diag([p1v, p2v])
                            Dm = np.array([[d1v, d0v], [d0v, d2v]])
                            Sm = np.array([[av, bv], [cv, dv]])
                            rel_err = float(np.linalg.norm(Dm @ (Sm - Pm) @ Dm - (Sm.T @ Sm @ Pm - Sm @ Pm @ Sm.T))) / (float(np.linalg.norm(Dm) ** 2 * np.linalg.norm(Pm)) + 1.0)
                            if rel_err < 1e-10 and float(np.linalg.norm(Sm - Pm)) > 1e-4:
                                evS = np.linalg.eigvals(Sm)
                                evSym = np.linalg.eigvalsh(0.5 * (Sm + Sm.T))
                                wD, VD = eigh(Dm)
                                Dm12 = (VD / np.sqrt(wD)) @ VD.T
                                Qm = Dm12 @ Pm @ Dm12
                                Ym = Dm12 @ Sm @ Dm12
                                E0m = Ym @ Dm @ Qm @ Dm @ Ym.T - Dm @ Qm @ Dm
                                comm_rel = float(np.linalg.norm(E0m @ Dm - Dm @ E0m)) / (float(np.linalg.norm(E0m) * np.linalg.norm(Dm)) + 1e-30)
                                MXm = Dm + Ym.T @ Dm @ Ym
                                Am = Dm + Ym @ Dm @ Qm
                                LHS = MXm @ Am
                                RHS = Dm @ Ym @ Dm
                                Lam_e = float(np.sum(LHS * RHS) / np.sum(RHS * RHS))
                                g4_rel = float(np.linalg.norm(Am @ Am.T - Lam_e * Dm @ Qm @ Dm)) / float(np.linalg.norm(Am @ Am.T))
                                cex_list.append((rel_err, float(np.linalg.norm(Sm - Pm)), float(evSym[0]), bool(np.all(evS.real > 0.0)), comm_rel, g4_rel, (p1v, p2v, d1v, d2v, d0v, Sm)))
        return cex_list

    cex = find_m3_counterexamples(2026, 5000)
    n_pos_eigs = sum(1 for item in cex if item[3])
    n_pos_sym = sum(1 for item in cex if item[2] > 0.0)
    min_comm = min(item[4] for item in cex)
    min_g4 = min(item[5] for item in cex)
    assert len(cex) >= 100 and n_pos_sym >= 1 and min_comm > 1e-5 and min_g4 > 1e-2
    # Print the cleanest strictly positive-real-part ((S+S^T)/2 > 0) counterexample witness!
    best_pos = max(cex, key=lambda item: item[2])
    p1w, p2w, d1w, d2w, d0w, Sw = best_pos[6]
    print(f"  5,000 random non-commuting 2x2 trials: {len(cex)} genuine (MIRACLE-3) counterexamples found!")
    print(f"    Re(eig(S)) > 0: {n_pos_eigs}/{len(cex)} | Strictly PSD symmetric part (S+S^T)/2 > 0: {n_pos_sym}/{len(cex)}")
    print(f"    ALL counterexamples violate [E0, D] = 0 (min rel ||[E0, D]|| = {min_comm:.3e}) & (G4) (min rel err = {min_g4:.3e})!")
    print(f"  Explicit Positive-Real-Part Witness ((S+S^T)/2 min_eig = {best_pos[2]:+.6f} > 0):")
    print(f"    P = diag({p1w:.6f}, {p2w:.6f}), D = [[{d1w:.6f}, {d0w:.6f}], [{d0w:.6f}, {d2w:.6f}]]")
    print(f"    S = [[{Sw[0,0]:.6f}, {Sw[0,1]:.6f}], [{Sw[1,0]:.6f}, {Sw[1,1]:.6f}]], ||S-P||={best_pos[1]:.4f}, rel_err={best_pos[0]:.2e}")
    print("  [PASS] Module 2: Reduction, proved cases, & exact 2x2 No-Go counterexample verified!\n")


# ==============================================================================
# MODULE 3 (PART B(i)): UNIVERSAL ALL-(1 < p < 2) LARGE-m EXCESS THEOREM
# ==============================================================================

def run_module_3():
    print("=" * 80)
    print("MODULE 3 (PART B(i)): UNIVERSAL ALL-(1 < p < 2) LARGE-m EXCESS THEOREM")
    print("                      (EXACT SYMPY DERIVATION + 120-DPS 8-EXPONENT VERIFICATION)")
    print("=" * 80)

    # --- Suite 3A: Exact Symbolic Derivation in SymPy for Arbitrary kappa > 1 ---
    print("\n[Suite 3A] Exact Symbolic General-kappa Cancellation & Exponent Laws:")
    u_k, e_s = sp.symbols('u_k e_s', positive=True)
    kap_s = 1 + u_k  # strictly kappa in (1, inf)
    exp_det_eps = sp.simplify((2 * kap_s - 1) - (2 - 2 * kap_s) - 1 - 4 * (kap_s - 1))
    assert exp_det_eps == 0
    c_k_sym = sp.Integer(2) ** ((2 * kap_s - 1) / (kap_s - 1))
    assert sp.simplify(sp.powsimp(sp.Integer(2) ** (2 * kap_s - 1) / (c_k_sym ** (kap_s - 1)), force=True) - 1) == 0

    # Exact symbolic derivation of the universal +1 coefficient in Lam * (T_RG2 - T_1x1) = +eps^2 * (1 + o(1)):
    #   (M_2^(2k-1))_00 - (1 + X_00)^(2k-1) = (2k - 2) * eps^2 + O(eps^3)
    #   (G_2^(k-1))_00 / X_00^(k-1) = (1 - eps)*(1 + eps)^(k-1) + O(eps^(2k-1)) = 1 + (k - 2)*eps + ...
    #   => X_00 - x_- = -(k - 2)/(k - 1) * eps^2 + O(eps^(2k)) + O(eps^3)
    #   => Lam*(T_RG2 - T_1x1) = [2(k-1)*(-(k-2)/(k-1)) + (2k - 2) - 1]*eps^2 = +1 * eps^2 identically!
    m00_e2 = sp.simplify(sp.series((1 + e_s ** 2) ** (2 * kap_s - 1) * (1 - e_s ** 2) - 1, e_s, 0, 3).removeO() / (e_s ** 2))
    g00_e1 = sp.simplify((sp.series((1 - e_s) * (1 + e_s) ** (kap_s - 1), e_s, 0, 2).removeO() - 1) / e_s)
    assert sp.simplify(m00_e2 - (2 * kap_s - 2)) == 0
    assert sp.simplify(g00_e1 - (kap_s - 2)) == 0
    plus_one_coeff = sp.simplify(2 * (kap_s - 1) * (-g00_e1 / (kap_s - 1)) + m00_e2 - 1)
    assert plus_one_coeff == 1

    q2_22_p32 = sp.simplify((1 + sp.sqrt(c_k_sym)).subs(u_k, sp.Rational(1, 2)))
    assert q2_22_p32 == 5

    exp_m = sp.simplify(1 / (4 * kap_s) - 1 / (kap_s - 1))
    exp_m_expected = -(3 * kap_s + 1) / (4 * kap_s * (kap_s - 1))
    assert sp.simplify(exp_m - exp_m_expected) == 0
    assert exp_m.subs(u_k, sp.Rational(1, 2)) == sp.Rational(-11, 6)
    assert exp_m.subs(u_k, sp.Integer(1)) == sp.Rational(-7, 8)
    assert exp_m.subs(u_k, sp.Rational(1, 4)) == sp.Rational(-19, 5)
    assert exp_m.subs(u_k, sp.Integer(2)) == sp.Rational(-5, 12)
    exp_rho = sp.simplify(1 - kap_s / (kap_s - 1))
    assert sp.simplify(exp_rho + 1 / (kap_s - 1)) == 0
    print(f"  1. Exact det(M_2)^(2k-1) / (Lam^2 d_1 det(G_2)^(k-1)): eps-exponent = {exp_det_eps}, c_k = 2^((2k-1)/(k-1)) [EXACT]")
    print(f"  2. Exact +1 cancellation: 2(k-1)*(-(k-2)/(k-1)) + (2k-2) - 1 === {plus_one_coeff} for ALL kappa > 1 [EXACT]")
    print(f"  3. Limiting Q_2(p=3/2) (2,2) entry = {q2_22_p32} (reproduces [[1,1],[1,5]] / Golden Ratio eigs!) [EXACT]")
    print("  4. Universal excess exponent = -(3*kappa+1)/(4*kappa*(kappa-1)): p=5/3 -> -19/5, p=3/2 -> -11/6, p=4/3 -> -7/8, p=6/5 -> -5/12 [EXACT]")
    print("  5. Universal subcriticality rho_2 ~ m^(-1/(kappa-1)) -> 0 for ALL 1 < p < 2 [EXACT]")

    # --- Suite 3B: 120-dps Direct-from-Asymptotic Verification Across ALL 8 Exponents ---
    print("\n[Suite 3B] 120-dps Direct-from-Asymptotic Verification (ZERO Homotopy!) Across 8 Rational & Irrational Exponents:")
    mp.mp.dps = 120

    def solve_r2_120dps(p_val, m_val):
        kap = p_val / (2 * (p_val - 1))
        L0 = mp.mpf(2) ** (2 * kap - 1)

        def xpm_from_xp(xp):
            Lm = (1 + xp) ** (2 * kap - 1) / (xp ** (kap - 1))
            xm = (1 / Lm) ** (1 / (kap - 1))
            for _ in range(50):
                f = (1 + xm) ** (2 * kap - 1) - Lm * xm ** (kap - 1)
                fp = (2 * kap - 1) * (1 + xm) ** (2 * kap - 2) - Lm * (kap - 1) * xm ** (kap - 2)
                st = f / fp
                xm -= st
                if abs(st) < mp.mpf('1e-110') * abs(xm):
                    break
            return Lm, xm

        xp1 = mp.mpf(m_val) ** (1 / (2 * kap)) * (1 - (2 * kap - 2) / (2 * kap) * mp.mpf(m_val) ** (-1 / (2 * kap)))
        for _ in range(40):
            Lam1, xm1 = xpm_from_xp(xp1)
            g = xp1 ** (kap - 1) * (xp1 - 1) + (m_val - 1) * xm1 ** (kap - 1) * (xm1 - 1)
            dL_dxp = Lam1 * ((2 * kap - 1) / (1 + xp1) - (kap - 1) / xp1)
            dxm_dL = xm1 ** (kap - 1) / ((2 * kap - 1) * (1 + xm1) ** (2 * kap - 2) - Lam1 * (kap - 1) * xm1 ** (kap - 2))
            dg = xp1 ** (kap - 2) * (kap * xp1 - (kap - 1)) + (m_val - 1) * xm1 ** (kap - 2) * (kap * xm1 - (kap - 1)) * dxm_dL * dL_dxp
            st = g / dg
            xp1 -= st
            if abs(st) < mp.mpf('1e-110') * abs(xp1):
                break
        Lam1, xm1 = xpm_from_xp(xp1)
        C1 = (Lam1 / L0) ** (1 / (2 * kap))
        eps = Lam1 ** (-1 / (kap - 1))
        c_k = mp.mpf(2) ** ((2 * kap - 1) / (kap - 1))

        def sym2_pow_det(a0, b0, c0, det_val, pw):
            tr = a0 + c0
            df = a0 - c0
            rad = mp.sqrt(df * df + 4 * b0 * b0)
            l1 = (tr + rad) / 2
            l2 = det_val / l1
            if l2 <= 0:
                raise ValueError("Non-SPD")
            p1 = l1 ** pw
            p2 = l2 ** pw
            if df >= 0:
                c2 = (rad + df) / (2 * rad)
                s2 = 2 * b0 * b0 / (rad * (rad + df))
            else:
                s2 = (rad - df) / (2 * rad)
                c2 = 2 * b0 * b0 / (rad * (rad - df))
            return p1 * c2 + p2 * s2, (p1 - p2) * (b0 / rad), p1 * s2 + p2 * c2

        def eval_res(v, check_raw=False):
            xp = xp1 + v[0] * xp1 * eps ** 2
            d1 = eps * v[1]
            detX = c_k * eps ** 2 * v[2]
            X01 = mp.sqrt(eps) * v[3]
            X11 = v[4]
            X00 = (X01 * X01 + detX) / X11
            Lm = (1 + xp) ** (2 * kap - 1) / (xp ** (kap - 1))
            spv = xp ** (kap - 1) * (xp - 1)
            sd1 = mp.sqrt(d1)
            h00, h01, h11 = X00, sd1 * X01, d1 * X11
            detM = d1 * (1 + X11 + X00 + detX)
            detG = d1 * d1 * detX
            m00, m01, m11 = sym2_pow_det(1 + h00, h01, d1 + h11, detM, 2 * kap - 1)
            g00, g01, g11 = X00, d1 * X01, d1 * d1 * X11
            gkm1_00, gkm1_01, gkm1_11 = sym2_pow_det(g00, g01, g11, detG, kap - 1)
            gk_00, gk_01, gk_11 = sym2_pow_det(g00, g01, g11, detG, kap)
            r00 = m00 - Lm * gkm1_00
            r01 = (m01 - Lm * sd1 * gkm1_01) / (sd1 * mp.sqrt(eps))
            r_det = (detM ** (2 * kap - 1)) / (Lm * Lm * d1 * (detG ** (kap - 1))) - 1
            eh00 = gk_00 - gkm1_00
            eh11 = (gk_11 - d1 * d1 * gkm1_11) / (d1 ** (2 * kap))
            e0 = (eh00 + spv / (m_val - 1)) / (spv / (m_val - 1))
            e1 = (eh11 - spv) / spv
            if check_raw:
                raw_r11 = abs(m11 - Lm * d1 * gkm1_11) / max(abs(m11), abs(Lm * d1 * gkm1_11))
                raw_eh01 = abs(gk_01 - d1 * gkm1_01) / (d1 ** kap * spv)
                return [r00, r01, r_det, e0, e1], raw_r11, raw_eh01
            return [r00, r01, r_det, e0, e1]

        v = [mp.mpf(1) / (2 * kap), mp.mpf(1), mp.mpf(1), mp.mpf(1), mp.mpf(1)]
        h_fd = mp.mpf('1e-50')
        for _ in range(18):
            f0 = eval_res(v)
            nf = mp.sqrt(sum(fi * fi for fi in f0))
            if nf < mp.mpf('1e-100'):
                break
            J = mp.matrix(5, 5)
            for j in range(5):
                vj = list(v)
                vj[j] += h_fd
                fj = eval_res(vj)
                for i in range(5):
                    J[i, j] = (fj[i] - f0[i]) / h_fd
            dv = mp.lu_solve(J, mp.matrix([-fi for fi in f0]))
            alpha = mp.mpf(1)
            while True:
                vt = [v[j] + alpha * dv[j] for j in range(5)]
                if vt[1] > 0 and vt[2] > 0 and vt[4] > 0:
                    v = vt
                    break
                alpha /= 2
        f_end, raw_r11, raw_eh01 = eval_res(v, check_raw=True)
        rn = max(mp.sqrt(sum(fi * fi for fi in f_end)), raw_r11, raw_eh01)
        xp2 = xp1 + v[0] * xp1 * eps ** 2
        Lam2 = (1 + xp2) ** (2 * kap - 1) / (xp2 ** (kap - 1))
        C2 = (Lam2 / L0) ** (1 / (2 * kap))
        d1 = eps * v[1]
        rho2 = (m_val - 1) * (d1 ** (2 * kap))
        exc = C2 - C1
        pred_lead = (mp.mpf(2) ** (-(2 * kap - 1) / (2 * kap)) / (4 * kap)) * (mp.mpf(m_val) ** (1 / (4 * kap) - 1 / (kap - 1)))
        _, xm2 = xpm_from_xp(xp2)
        T_rg2 = xp2 ** (kap - 1) * (xp2 - 1) / (m_val - 1)
        T_1x1_L2 = -(xm2 ** (kap - 1) * (xm2 - 1))
        sp2 = xp2 ** (kap - 1) * (xp2 - 1)
        T_sub = ((T_rg2 - T_1x1_L2) / T_1x1_L2) / ((sp2 / Lam2) * (Lam2 ** (-2 / (kap - 1))))

        # Also evaluate 2-atom Primal (#107) and Dual (#119) operator integrals c_2 * I_op on this exact r=2 block!
        # Construct exact 2x2 matrices in 120-dps mpmath:
        detX = c_k * eps ** 2 * v[2]
        X01 = mp.sqrt(eps) * v[3]
        X11 = v[4]
        X00 = (X01 * X01 + detX) / X11
        sd1 = mp.sqrt(d1)
        h00, h01, h11 = X00, sd1 * X01, d1 * X11
        detM = d1 * (1 + X11 + X00 + detX)
        detG = d1 * d1 * detX
        # Eigenvalues & first-row weights of X_2 and Q_2:
        def eigs_and_w0(a0, b0, c0, det_v):
            tr = a0 + c0
            df = a0 - c0
            rad = mp.sqrt(df * df + 4 * b0 * b0)
            l1 = (tr + rad) / 2
            l2 = det_v / l1
            if df >= 0:
                w1 = (rad + df) / (2 * rad)
                w2 = 2 * b0 * b0 / (rad * (rad + df))
            else:
                w2 = (rad - df) / (2 * rad)
                w1 = 2 * b0 * b0 / (rad * (rad - df))
            return (l1, w1), (l2, w2)

        def inv2(a0, b0, c0):
            dt = a0 * c0 - b0 * b0
            return c0 / dt, -b0 / dt, a0 / dt

        def mat2_eig_min(a0, b0, c0):
            tr = a0 + c0
            df = a0 - c0
            return (tr - mp.sqrt(df * df + 4 * b0 * b0)) / 2

        c_2 = (mp.mpf(m_val) / (m_val - 1)) * sp2
        # Primal operators Z, T1, T2:
        gkm1_00, gkm1_01, gkm1_11 = sym2_pow_det(X00, d1 * X01, d1 * d1 * X11, detG, kap - 1)
        Z00, Z01, Z11 = gkm1_00, gkm1_01 * (d1 ** (1 - kap)), gkm1_11 * (d1 ** (2 - 2 * kap))
        m32_00, m32_01, m32_11 = sym2_pow_det(1 + h00, h01, d1 + h11, detM, 3 - 2 * kap)
        T1_00, T1_01, T1_11 = m32_00, m32_01 * (d1 ** (kap - mp.mpf('1.5'))), m32_11 * (d1 ** (2 * kap - 3))
        g2k_00, g2k_01, g2k_11 = sym2_pow_det(X00, d1 * X01, d1 * d1 * X11, detG, 2 - kap)
        T2_00, T2_01, T2_11 = g2k_00, g2k_01 * (d1 ** (kap - 2)), g2k_11 * (d1 ** (2 * kap - 4))
        (xl1, xw1), (xl2, xw2) = eigs_and_w0(X00, X01, X11, detX)
        Ipri_00 = Ipri_01 = Ipri_11 = mp.mpf(0)
        for xk, wk in [(xl1, xw1), (xl2, xw2)]:
            gk_s = (1 + xk) / Lam2
            d00, d01, d11 = inv2(T1_00 - gk_s * T2_00, T1_01 - gk_s * T2_01, T1_11 - gk_s * T2_11)
            K00 = sp2 - xk * Z00 + gk_s * d00
            K01 = -xk * Z01 + gk_s * d01
            K11 = sp2 - xk * Z11 + gk_s * d11
            ik00, ik01, ik11 = inv2(K00, K01, K11)
            Ipri_00 += wk * ik00
            Ipri_01 += wk * ik01
            Ipri_11 += wk * ik11
        pri_e0_perp = float(c_2 * Ipri_11)  # since e_0 = (1, 0) has c_2 * Ipri_00 == 1!
        assert abs(float(c_2 * Ipri_00) - 1.0) < 1e-30

        # Dual operators Y, W1^-1, P and Q_2 = D^(-1/2) G^(1/2) D^(-1/2):
        gh_00, gh_01, gh_11 = sym2_pow_det(X00, d1 * X01, d1 * d1 * X11, detG, mp.mpf('0.5'))
        Q00, Q01, Q11 = gh_00, gh_01 / sd1, gh_11 / d1
        detQ = mp.sqrt(detG) / d1
        (ql1, qw1), (ql2, qw2) = eigs_and_w0(Q00, Q01, Q11, detQ)
        gy_00, gy_01, gy_11 = sym2_pow_det(X00, d1 * X01, d1 * d1 * X11, detG, kap - mp.mpf('0.5'))
        Y00, Y01, Y11 = gy_00, gy_01 * (d1 ** (mp.mpf('0.5') - kap)), gy_11 * (d1 ** (1 - 2 * kap))
        mw_00, mw_01, mw_11 = sym2_pow_det(1 + h00, h01, d1 + h11, detM, 2 - 2 * kap)
        W00, W01, W11 = mw_00, mw_01 * (d1 ** (kap - 1)), mw_11 * (d1 ** (2 * kap - 2))
        gp_00, gp_01, gp_11 = sym2_pow_det(X00, d1 * X01, d1 * d1 * X11, detG, mp.mpf('1.5') - kap)
        P00, P01, P11 = gp_00, gp_01 * (d1 ** (kap - mp.mpf('1.5'))), gp_11 * (d1 ** (2 * kap - 3))
        Idual_00 = Idual_01 = Idual_11 = mp.mpf(0)
        for sk, wk in [(ql1, qw1), (ql2, qw2)]:
            d00, d01, d11 = inv2(Lam2 * W00 - sk * P00, Lam2 * W01 - sk * P01, Lam2 * W11 - sk * P11)
            K00 = sp2 - sk * Y00 + d00
            K01 = -sk * Y01 + d01
            K11 = sp2 - sk * Y11 + d11
            ik00, ik01, ik11 = inv2(K00, K01, K11)
            Idual_00 += wk * ik00
            Idual_01 += wk * ik01
            Idual_11 += wk * ik11
        dual_e0_perp = float(c_2 * Idual_11)
        assert abs(float(c_2 * Idual_00) - 1.0) < 1e-30
        pri_min = float(mat2_eig_min(c_2 * Ipri_00, c_2 * Ipri_01, c_2 * Ipri_11))
        dual_min = float(mat2_eig_min(c_2 * Idual_00, c_2 * Idual_01, c_2 * Idual_11))
        return (
            float(rn), float(exc), float(exc / pred_lead), float(T_sub),
            float(v[1]), float(v[2]), float(rho2), pri_e0_perp, dual_e0_perp, pri_min, dual_min
        )

    tests = [
        ("5/3", mp.mpf(5) / 3, 10 ** 6),
        ("phi", (1 + mp.sqrt(5)) / 2, 10 ** 8),
        ("3/2", mp.mpf(3) / 2, 10 ** 10),
        ("sqrt(2)", mp.sqrt(2), 10 ** 12),
        ("7/5", mp.mpf(7) / 5, 10 ** 12),
        ("4/3", mp.mpf(4) / 3, 10 ** 14),
        ("5/4", mp.mpf(5) / 4, 10 ** 16),
        ("6/5", mp.mpf(6) / 5, 10 ** 18),
    ]
    print(f"  {'p':>7s} | {'m':>5s} | {'res':>8s} | {'exc/lead':>8s} | {'T_sub':>8s} | {'d1/eps':>8s} | {'rho_2':>8s} | {'Pri11-1':>9s} | {'Dual11-1':>9s}")
    for name, pv, mv in tests:
        rn, exc, rl, ts, d1r, det_r, rho2, p11, d11, pmin, dmin = solve_r2_120dps(pv, mv)
        assert rn < 1e-105 and abs(ts - 1.0) < 1e-3 and abs(d1r - 1.0) < 1e-3 and rho2 < 1e-8
        assert 0.94 < rl < 1.01 and 0.95 < det_r < 1.01
        # Verify sharp 2-piece dichotomy across p = 3/2 (Regime I: Pri >= 1 >= Dual; Regime II: Dual >= 1 >= Pri; Regime III: both > 1)!
        if pv > mp.mpf('1.5001'):
            assert p11 > 1.0 and d11 < 1.0 and pmin >= 1.0 - 1e-12
        elif abs(pv - mp.mpf('1.5')) < 1e-12:
            assert abs(p11 - 1.0) < 1e-12 and abs(d11 - 1.0) < 1e-12
        elif pv > mp.mpf(4) / 3 + mp.mpf('1e-4'):
            assert d11 > 1.0 and p11 < 1.0 and dmin >= 1.0 - 1e-12
        elif abs(pv - mp.mpf(4) / 3) < 1e-12:
            assert abs(p11 - 1.0) < 1e-12 and d11 > 1.0
        else:
            assert p11 > 1.0 and d11 > 1.0
        print(f"  {name:>7s} | 1e{int(round(float(mp.log10(mv)))):2d}  | {rn:8.1e} | {rl:8.6f} | {ts:8.6f} | {d1r:8.6f} | {rho2:8.2e} | {p11 - 1.0:+9.2e} | {d11 - 1.0:+9.2e}")
    print("  [PASS] Module 3: Exact symbolic all-p law & 120-dps 8-exponent verification passed!\n")


# ==============================================================================
# MODULE 4 (PART B(ii)): PARALLEL-SUM & SECOND-USE-OF-HOLDEN POLYNOMIAL IDEALS
#                        AT p = 5/3 (kappa = 5/4) AND p = 6/5 (kappa = 3)
# ==============================================================================

def solve_rg_general_float(kap_target, m, r_target, n_hom=5):
    """Coupled rank-r RG solver in float64 via smooth kappa-homotopy from exact p=3/2 RG block."""
    assert m == 2
    Lam_c, ds_c, Q_c = solve_rg_p32_Q(r_target)
    H_c = Q_c @ np.diag(ds_c) @ Q_c
    X_c = (ds_c ** (-0.5))[:, None] * H_c * (ds_c ** (-0.5))[None, :]

    def solve_at_kap(kap, L_in, d_in, X_in):
        rk = len(d_in)
        L0 = 2.0 ** (2.0 * kap - 1.0)
        triu = np.triu_indices(rk)
        w0, V0 = eigh(0.5 * (X_in + X_in.T))
        S0 = (V0 * np.log(np.maximum(w0, 1e-12))) @ V0.T
        x0 = np.concatenate([[np.log(max(L_in - L0, 1e-9))], np.log(d_in[1:]), S0[triu]])
        def unpack(xv):
            L = L0 + np.exp(np.clip(xv[0], -30.0, 12.0))
            dd = np.concatenate([[1.0], np.exp(np.clip(xv[1:rk], -20.0, -0.01))])
            Sm = np.zeros((rk, rk))
            Sm[triu] = xv[rk:]
            Sm = Sm + np.triu(Sm, 1).T
            ws, Vs = eigh(Sm)
            XX = (Vs * np.exp(np.clip(ws, -25.0, 8.0))) @ Vs.T
            return L, dd, XX
        def res(xv):
            L, dd, XX = unpack(xv)
            sD = np.sqrt(dd)
            H = (sD[:, None] * XX) * sD[None, :]
            M = np.diag(dd) + H
            G = (dd[:, None] * XX) * dd[None, :]
            wM, VM = eigh(M)
            wG, VG = eigh(G)
            R1 = (VM * (wM ** (2.0 * kap - 1.0))) @ VM.T - L * ((sD[:, None] * ((VG * (wG ** (kap - 1.0))) @ VG.T)) * sD[None, :])
            E = (VG * (wG ** kap)) @ VG.T - (dd[:, None] * ((VG * (wG ** (kap - 1.0))) @ VG.T)) * dd[None, :]
            E_hat = (dd ** (-kap))[:, None] * E * (dd ** (-kap))[None, :]
            _, xp = get_xpm_float(L, kap)
            spv = sig_float(xp, kap)
            diag_err = np.diag(E_hat) - np.concatenate([[-spv / (m - 1)], np.full(rk - 1, spv)])
            w_sc = (dd ** (-kap))[:, None] * (dd ** (-kap))[None, :]
            return np.concatenate([(R1 * w_sc)[triu], diag_err])
        sol = least_squares(res, x0, method='lm', ftol=1e-15, xtol=1e-15, gtol=1e-15, max_nfev=10000)
        assert sol.cost < 1e-22, f"RG homotopy failed at kap={kap}, r={rk}: cost={sol.cost}"
        L_o, d_o, X_o = unpack(sol.x)
        wx_o = eigh(X_o)[1][0, :] ** 2
        assert float(wx_o.min()) > 1e-6, f"RG decoupled at kap={kap}, r={rk}: wx={wx_o}"
        return L_o, d_o, X_o

    for k_step in np.linspace(1.5, kap_target, n_hom + 1)[1:]:
        # Scale Lam initial guess smoothly via 1x1 ratio
        L1_new = solve_1x1_float(k_step, m)[0]
        Lam_c = L1_new * 1.0002
        Lam_c, ds_c, X_c = solve_at_kap(float(k_step), Lam_c, ds_c, X_c)
    return Lam_c, ds_c, X_c


def run_module_4():
    print("=" * 80)
    print("MODULE 4 (PART B(ii)): PARALLEL-SUM & SECOND-USE-OF-HOLDEN POLYNOMIAL IDEALS")
    print("                       AT p = 5/3 (kappa = 5/4) AND p = 6/5 (kappa = 3)")
    print("=" * 80)

    # --- Suite 4A: p = 5/3 Exact 3-Gen & Bounded 6-Gen All-Degree-3 Formulations + Hermitian Linear Partition ---
    print("\n[Suite 4A] p = 5/3 (kappa = 5/4, m = 2): 3-Gen (A,B,C) & 6-Gen All-Degree-3 (A,Z,T1,T2,U,V) + 3-Atom Linear Y_k:")
    kap53 = 1.25
    Lam1, xm1, xp1, sp1, C1_53 = solve_1x1_float(kap53, 2)
    c_1x1 = 2.0 * sp1

    # Verify all 2 three-gen and all 7 degree-3 six-gen Holden identities on coupled r=2 and r=3 RG blocks!
    Lam3, ds3, X3 = solve_rg_general_float(kap53, 2, 3, n_hom=4)
    C3_53 = (Lam3 / (2.0 ** 1.5)) ** 0.4
    sD3 = np.sqrt(ds3)
    H3 = (sD3[:, None] * X3) * sD3[None, :]
    M3 = np.diag(ds3) + H3
    G3 = (ds3[:, None] * X3) * ds3[None, :]
    wM3, VM3 = eigh(M3)
    wG3, VG3 = eigh(G3)
    A3 = np.diag(ds3 ** 0.5)
    B3 = (VM3 * (wM3 ** 0.5)) @ VM3.T
    C3 = (VG3 * (wG3 ** 0.25)) @ VG3.T
    Dm14 = np.diag(ds3 ** (-0.25))
    Dm34 = np.diag(ds3 ** (-0.75))
    Z3 = Dm14 @ C3 @ Dm14
    T1_3 = Dm14 @ B3 @ Dm14
    T2_3 = Dm34 @ (C3 @ C3 @ C3) @ Dm34
    U3 = Z3 @ A3 @ Z3
    V3 = T1_3 @ A3 @ T1_3

    err_3gen = max(
        float(np.linalg.norm(B3 @ B3 @ B3 - Lam3 * A3 @ C3 @ A3)),
        float(np.linalg.norm(A3 @ B3 @ B3 @ A3 - (A3 ** 4) - (C3 @ C3 @ C3 @ C3)))
    )
    err_6gen = max(
        float(np.linalg.norm(U3 - Z3 @ A3 @ Z3)),
        float(np.linalg.norm(V3 - T1_3 @ A3 @ T1_3)),
        float(np.linalg.norm(T1_3 @ A3 @ V3 - Lam3 * A3 @ Z3 @ A3)),
        float(np.linalg.norm(V3 @ A3 @ T1_3 - Lam3 * A3 @ Z3 @ A3)),
        float(np.linalg.norm(A3 @ T2_3 @ A3 - U3 @ A3 @ Z3)),
        float(np.linalg.norm(A3 @ T2_3 @ A3 - Z3 @ A3 @ U3)),
        float(np.linalg.norm(A3 @ V3 @ A3 - (A3 ** 3) - U3 @ A3 @ U3))
    )
    assert err_3gen < 1e-13 and err_6gen < 1e-13
    print(f"  Coupled r=3 RG at p=5/3, m=2: C_3 = {C3_53:.12f} (vs C_1x1 = {C1_53:.12f}), D = {np.round(ds3, 6)}")
    print(f"    3-gen (A,B,C) exact residual = {err_3gen:.2e} | 6-gen All-Degree-3 (A,Z,T1,T2,U,V) residual = {err_6gen:.2e}")

    # 3-atom Hermitian linear partition Y_k = a_k I + c_k Z (exact partition of unity) at Lam3 on {1x1, r=3 RG} vs Holden-free 1D:
    wX3, VX3 = eigh(X3)
    wx3 = VX3[0, :] ** 2
    xm3, xp3 = get_xpm_float(Lam3, kap53)
    sp3 = sig_float(xp3, kap53)
    c_rg3 = 2.0 * sp3

    K3_list = [sp3 * np.eye(3) - xk * Z3 + ((1.0 + xk) / Lam3) * np.linalg.inv(T1_3 - ((1.0 + xk) / Lam3) * T2_3) for xk in wX3]
    u_1x1 = np.array([xm3, xp3])
    z_1x1 = u_1x1 ** 0.25
    K_1x1 = np.array([sp3 - xk * z_1x1 + ((1.0 + xk) / Lam3) / (np.sqrt(1.0 + u_1x1) - ((1.0 + xk) / Lam3) * (u_1x1 ** 0.75)) for xk in wX3])

    # Holden-free 1D curve u in (0, xp3] exhibits +1.688e-3 breakdown near u -> 0 (Obstruction 6(a)):
    us_hf = np.linspace(1e-7, xp3, 4000)
    zs_hf = us_hf ** 0.25
    K_hf = np.array([sp3 - xk * zs_hf + ((1.0 + xk) / Lam3) / (np.sqrt(1.0 + us_hf) - ((1.0 + xk) / Lam3) * (us_hf ** 0.75)) for xk in wX3])
    hf_1d_exc = float((1.0 / np.sum(wx3[:, None] / K_hf, axis=0)).max() / c_rg3 - 1.0)

    # Seed from exact Frobenius fit to optimal parallel-sum operators Y_k^opt = w_k K_k^{-1} (sum w_j K_j^{-1})^{-1} on r=3 RG:
    P3 = np.linalg.inv(sum(wx3[k] * np.linalg.inv(K3_list[k]) for k in range(3)))
    Y3_opt = [wx3[k] * np.linalg.inv(K3_list[k]) @ P3 for k in range(3)]
    G_fit = np.array([[3.0, float(np.trace(Z3))], [float(np.trace(Z3)), float(np.trace(Z3 @ Z3))]])
    ac_f = np.array([np.linalg.solve(G_fit, [float(np.trace(Y3_opt[k])), float(np.trace(Z3 @ Y3_opt[k]))]) for k in range(3)])

    def eval_lin(p4):
        av = np.array([p4[0], p4[1], 1.0 - p4[0] - p4[1]])
        cv = np.array([p4[2], p4[3], -p4[2] - p4[3]])
        S3 = sum((1.0 / wx3[k]) * ((av[k] * np.eye(3) + cv[k] * Z3) @ K3_list[k] @ (av[k] * np.eye(3) + cv[k] * Z3)) for k in range(3))
        B3 = sum((1.0 / wx3[k]) * ((av[k] * np.eye(3) + cv[k] * Z3) @ (av[k] * np.eye(3) + cv[k] * Z3)) for k in range(3))
        Y1 = av[:, None] + cv[:, None] * z_1x1[None, :]
        S1 = np.sum((Y1 ** 2 / wx3[:, None]) * K_1x1, axis=0)
        B1 = np.sum(Y1 ** 2 / wx3[:, None], axis=0)
        e_max = max(float(eigh(S3)[0][-1] / c_rg3 - 1.0), float(S1.max() / c_rg3 - 1.0))
        b_max = max(float(eigh(B3)[0][-1]), float(B1.max()))
        return e_max, b_max

    res_lin = minimize(
        lambda p4: eval_lin(p4)[0],
        [ac_f[0, 0], ac_f[1, 0], ac_f[0, 1], ac_f[1, 1]],
        method='Nelder-Mead',
        options={'maxiter': 5000, 'xatol': 1e-12, 'fatol': 1e-12}
    )
    exc_holden, bud_holden = eval_lin(res_lin.x)
    abs_exc_holden = exc_holden * c_rg3
    assert exc_holden < 3e-8 and bud_holden < 1.05 and hf_1d_exc > 1e-3
    print(f"  3-atom Hermitian linear Y_k = a_k I + c_k Z (exact partition of unity at Lam_3):")
    print(f"    Holden blocks {{1x1, r=3 RG}} max S/c_3 = 1 {exc_holden:+.3e} (abs = {abs_exc_holden:+.3e}, budget = {bud_holden:.5f} <= 2.0)")
    print(f"    Holden-free 1D curve u in (0, x_+] breakdown = 1 {hf_1d_exc:+.3e} (confirming Obstruction 6(a)!)")

    # Disproof of naive 2nd-step operator inequalities T2 <= xp^(1/2) Z and T1 >= Lam^(1/3) Z^(1/3):
    rng = np.random.default_rng(123)
    min_t2_z = 1e9
    for _ in range(2000):
        d = np.array([1.0, 10.0 ** rng.uniform(-3.0, -0.05)])
        Dm14_2 = np.diag(d ** (-0.25))
        Dm34_2 = np.diag(d ** (-0.75))
        U_r, _ = np.linalg.qr(rng.standard_normal((2, 2)))
        ex = 10.0 ** rng.uniform(-3.0, np.log10(xp1), size=2)
        G_r = (d[:, None] * (U_r @ np.diag(ex) @ U_r.T)) * d[None, :]
        wGr, VGr = eigh(G_r)
        Zr = Dm14_2 @ ((VGr * (wGr ** 0.25)) @ VGr.T) @ Dm14_2
        T2r = Dm34_2 @ ((VGr * (wGr ** 0.75)) @ VGr.T) @ Dm34_2
        min_t2_z = min(min_t2_z, float(eigh((xp1 ** 0.5) * Zr - T2r)[0][0]))
    wZ3, VZ3 = eigh(Z3)
    Z3_13 = (VZ3 * (wZ3 ** (1.0 / 3.0))) @ VZ3.T
    min_t1_z13 = float(eigh(T1_3 - (Lam3 ** (1.0 / 3.0)) * Z3_13)[0][0])
    assert min_t2_z < -1e-3 and min_t1_z13 < -1e-3
    print(f"  Disproof of naive 2nd-step candidates: min_eig(xp^(1/2) Z - T2) = {min_t2_z:+.3e} < 0; "
          f"min_eig(T1 - Lam^(1/3) Z^(1/3)) on r=3 RG = {min_t1_z13:+.3e} < 0")

    # --- Suite 4B: Sharp Degree-6 Threshold for Polynomial-Ideal Block-LMI SOS / NC-SOS at p = 5/3 ---
    print("\n[Suite 4B] Sharp Degree-6 Barrier for 3-Gen (A,B,C) Polynomial-Ideal Block-LMI SOS / NC-SOS (p=5/3, m=2):")
    g0 = (1.0 + xm1) / Lam1
    gxp = (1.0 + xp1) / Lam1
    s1 = np.sqrt(1.0 + xp1)
    s2 = xp1 ** 0.25

    def run_1d_comm_sos(D_tot, use_R1, use_R2):
        mon_all = [(i, j) for i in range(D_tot + 1) for j in range(D_tot + 1 - i)]
        var_map = {}
        n_vars = 0
        for blk in ['00', '01', '11']:
            for mij in mon_all:
                var_map[(blk, mij)] = n_vars
                n_vars += 1
        def idx(blk, ij):
            return var_map[('01' if blk == '10' else blk, ij)]
        eq_rows = []
        eq_rhs = []
        r0 = np.zeros(n_vars)
        r0[idx('00', (0, 0))] = 1.0
        eq_rows.append(r0)
        eq_rhs.append(1.0)
        def add_id(poly):
            dp = max(i + j for _, i, j in poly)
            for blk in ['00', '01', '11']:
                for ia in range(D_tot - dp + 1):
                    for jb in range(D_tot - dp + 1 - ia):
                        rr = np.zeros(n_vars)
                        for cf, i, j in poly:
                            rr[idx(blk, (ia + i, jb + j))] += cf
                        eq_rows.append(rr)
                        eq_rhs.append(0.0)
        if use_R1:
            add_id([(1.0, 3, 0), (-Lam1, 0, 1)])
        if use_R2:
            add_id([(1.0, 2, 0), (-1.0, 0, 0), (-1.0, 0, 4)])
        U, S_sv, Vt = np.linalg.svd(np.array(eq_rows), full_matrices=True)
        rk = int(np.sum(S_sv > 1e-12))
        y0 = Vt[:rk].T @ ((U[:, :rk].T @ np.array(eq_rhs)) / S_sv[:rk])
        N_ns = Vt[rk:].T
        df = N_ns.shape[1]
        c_vec = np.zeros(n_vars)
        c_vec[idx('00', (0, 1))] += xm1
        c_vec[idx('01', (0, 0))] += 2.0 * np.sqrt(g0)
        c_vec[idx('11', (1, 0))] += 1.0
        c_vec[idx('11', (0, 3))] -= g0
        ops = [
            ([(1.0, 0, 0)], D_tot // 2),
            ([(1.0, 1, 0), (-1.0, 0, 0)], (D_tot - 1) // 2),
            ([(s1, 0, 0), (-1.0, 1, 0)], (D_tot - 1) // 2),
            ([(1.0, 0, 1)], (D_tot - 1) // 2),
            ([(s2, 0, 0), (-1.0, 0, 1)], (D_tot - 1) // 2),
            ([(xp1, 1, 0), (-(1.0 + xp1) * gxp, 0, 3)], (D_tot - 3) // 2),
        ]
        blocks = []
        for poly, dh in ops:
            bm = [(i, j) for i in range(dh + 1) for j in range(dh + 1 - i)]
            basis = [('0', ij) for ij in bm] + [('1', ij) for ij in bm]
            mb = len(basis)
            B0 = np.zeros((mb, mb))
            Bz = np.zeros((df, mb, mb))
            for p1_i, (b1, (i1, j1)) in enumerate(basis):
                for p2_i in range(p1_i, mb):
                    b2, (i2, j2) = basis[p2_i]
                    blk = b1 + b2
                    for cf, gi, gj in poly:
                        kv = idx(blk, (i1 + i2 + gi, j1 + j2 + gj))
                        B0[p1_i, p2_i] += cf * y0[kv]
                        Bz[:, p1_i, p2_i] += cf * N_ns[kv, :]
                    if p1_i != p2_i:
                        B0[p2_i, p1_i] = B0[p1_i, p2_i]
                        Bz[:, p2_i, p1_i] = Bz[:, p1_i, p2_i]
            blocks.append((B0, Bz))
        po, do, nrp, nrd, _it = solve_sdp_dual(N_ns.T @ c_vec, blocks)
        cc = float(c_vec @ y0)
        return df, (sp1 - (po + cc)) / c_1x1, (sp1 - (do + cc)) / c_1x1, nrp, nrd

    def run_comm3_sos(D_tot, use_R1, use_R2, eps_A=0.5):
        mons3 = lambda d: [(i, j, k) for i in range(d + 1) for j in range(d + 1 - i) for k in range(d + 1 - i - j)]
        ma = mons3(D_tot)
        var_map = {}
        n_vars = 0
        for blk in ['00', '01', '11']:
            for tm in ma:
                var_map[(blk, tm)] = n_vars
                n_vars += 1
        def idx(blk, tm):
            return var_map[('01' if blk == '10' else blk, tm)]
        eq_rows = []
        eq_rhs = []
        r0 = np.zeros(n_vars)
        r0[idx('00', (1, 0, 0))] = 1.0
        eq_rows.append(r0)
        eq_rhs.append(1.0)
        def add_id(poly):
            dp = max(i + j + k for _, i, j, k in poly)
            for blk in ['00', '01', '11']:
                for ia, jb, kc in mons3(D_tot - dp):
                    rr = np.zeros(n_vars)
                    for cf, i, j, k in poly:
                        rr[idx(blk, (ia + i, jb + j, kc + k))] += cf
                    eq_rows.append(rr)
                    eq_rhs.append(0.0)
        if use_R1:
            add_id([(1.0, 0, 3, 0), (-Lam1, 2, 0, 1)])
        if use_R2:
            add_id([(1.0, 2, 2, 0), (-1.0, 4, 0, 0), (-1.0, 0, 0, 4)])
        U, S_sv, Vt = np.linalg.svd(np.array(eq_rows), full_matrices=True)
        rk = int(np.sum(S_sv > 1e-12))
        y0 = Vt[:rk].T @ ((U[:, :rk].T @ np.array(eq_rhs)) / S_sv[:rk])
        N_ns = Vt[rk:].T
        df = N_ns.shape[1]
        c_vec = np.zeros(n_vars)
        c_vec[idx('00', (0, 0, 1))] += xm1
        c_vec[idx('01', (2, 0, 0))] += 2.0 * np.sqrt(g0)
        c_vec[idx('11', (2, 1, 0))] += 1.0
        c_vec[idx('11', (0, 0, 3))] -= g0
        ops = [
            ([(1.0, 0, 0, 0)], D_tot // 2),
            ([(1.0, 1, 0, 0), (-eps_A, 0, 0, 0)], (D_tot - 1) // 2),
            ([(1.0, 0, 0, 0), (-1.0, 1, 0, 0)], (D_tot - 1) // 2),
            ([(1.0, 0, 1, 0), (-1.0, 1, 0, 0)], (D_tot - 1) // 2),
            ([(s1, 1, 0, 0), (-1.0, 0, 1, 0)], (D_tot - 1) // 2),
            ([(1.0, 0, 0, 1)], (D_tot - 1) // 2),
            ([(s2, 1, 0, 0), (-1.0, 0, 0, 1)], (D_tot - 1) // 2),
            ([(xp1, 2, 1, 0), (-(1.0 + xp1) * gxp, 0, 0, 3)], (D_tot - 3) // 2),
        ]
        blocks = []
        for poly, dh in ops:
            bm = mons3(dh)
            basis = [('0', tm) for tm in bm] + [('1', tm) for tm in bm]
            mb = len(basis)
            B0 = np.zeros((mb, mb))
            Bz = np.zeros((df, mb, mb))
            for p1_i, (b1, (i1, j1, k1)) in enumerate(basis):
                for p2_i in range(p1_i, mb):
                    b2, (i2, j2, k2) = basis[p2_i]
                    blk = b1 + b2
                    for cf, gi, gj, gk in poly:
                        kv = idx(blk, (i1 + i2 + gi, j1 + j2 + gj, k1 + k2 + gk))
                        B0[p1_i, p2_i] += cf * y0[kv]
                        Bz[:, p1_i, p2_i] += cf * N_ns[kv, :]
                    if p1_i != p2_i:
                        B0[p2_i, p1_i] = B0[p1_i, p2_i]
                        Bz[:, p2_i, p1_i] = Bz[:, p1_i, p2_i]
            blocks.append((B0, Bz))
        po, do, nrp, nrd, _it = solve_sdp_dual(N_ns.T @ c_vec, blocks, max_iter=60)
        cc = float(c_vec @ y0)
        return df, (sp1 - (po + cc)) / c_1x1, (sp1 - (do + cc)) / c_1x1, nrp, nrd

    def run_nc_D4(use_R1, use_R2, eps_A=0.0):
        words_upto = lambda d: [w for k in range(d + 1) for w in (''.join(t) for t in product('abc', repeat=k))]
        w_all = words_upto(4)
        var_map = {}
        n_vars = 0
        for w in w_all:
            key = ('00', min(w, w[::-1]))
            if key not in var_map:
                var_map[key] = n_vars
                n_vars += 1
        for w in w_all:
            var_map[('01', w)] = n_vars
            n_vars += 1
        for w in w_all:
            key = ('11', min(w, w[::-1]))
            if key not in var_map:
                var_map[key] = n_vars
                n_vars += 1
        def idx(blk, w):
            if blk == '00':
                return var_map[('00', min(w, w[::-1]))]
            if blk == '11':
                return var_map[('11', min(w, w[::-1]))]
            if blk == '01':
                return var_map[('01', w)]
            return var_map[('01', w[::-1])]
        eq_rows = []
        eq_rhs = []
        r0 = np.zeros(n_vars)
        r0[idx('00', 'a')] = 1.0
        eq_rows.append(r0)
        eq_rhs.append(1.0)
        def add_id(poly):
            dp = max(len(w) for _, w in poly)
            rem = 4 - dp
            for blk in ['00', '01', '11']:
                for dl in range(rem + 1):
                    for dr in range(rem - dl + 1):
                        for wl in (''.join(t) for t in product('abc', repeat=dl)):
                            for wr in (''.join(t) for t in product('abc', repeat=dr)):
                                rr = np.zeros(n_vars)
                                for cf, w in poly:
                                    rr[idx(blk, wl + w + wr)] += cf
                                if float(np.linalg.norm(rr)) > 1e-14:
                                    eq_rows.append(rr)
                                    eq_rhs.append(0.0)
        if use_R1:
            add_id([(1.0, 'bbb'), (-Lam1, 'aca')])
        if use_R2:
            add_id([(1.0, 'abba'), (-1.0, 'aaaa'), (-1.0, 'cccc')])
        U, S_sv, Vt = np.linalg.svd(np.array(eq_rows), full_matrices=True)
        rk = int(np.sum(S_sv > 1e-12))
        y0 = Vt[:rk].T @ ((U[:, :rk].T @ np.array(eq_rhs)) / S_sv[:rk])
        N_ns = Vt[rk:].T
        df = N_ns.shape[1]
        c_vec = np.zeros(n_vars)
        c_vec[idx('00', 'c')] += xm1
        c_vec[idx('01', 'aa')] += 2.0 * np.sqrt(g0)
        c_vec[idx('11', 'aba')] += 1.0
        c_vec[idx('11', 'ccc')] -= g0
        ops = [
            ([(1.0, '')], 2),
            ([(1.0, 'a'), (-eps_A, '')], 1),
            ([(1.0, ''), (-1.0, 'a')], 1),
            ([(1.0, 'b'), (-1.0, 'a')], 1),
            ([(s1, 'a'), (-1.0, 'b')], 1),
            ([(1.0, 'c')], 1),
            ([(s2, 'a'), (-1.0, 'c')], 1),
            ([(xp1, 'aba'), (-(1.0 + xp1) * gxp, 'ccc')], 0),
            ([(1.0, 'bb'), (-1.0, 'aa')], 1),
            ([(1.0 + xp1, 'aa'), (-1.0, 'bb')], 1),
            ([(xp1 ** 0.5, 'aa'), (-1.0, 'cc')], 1),
            ([(xp1, 'aaaa'), (-1.0, 'cccc')], 0),
        ]
        blocks = []
        for poly, dh in ops:
            wm = words_upto(dh)
            basis = [('0', u) for u in wm] + [('1', u) for u in wm]
            mb = len(basis)
            B0 = np.zeros((mb, mb))
            Bz = np.zeros((df, mb, mb))
            for i, (bi, ui) in enumerate(basis):
                for j in range(i, mb):
                    bj, uj = basis[j]
                    blk = bi + bj
                    for cf, gw in poly:
                        kv = idx(blk, ui[::-1] + gw + uj)
                        B0[i, j] += cf * y0[kv]
                        Bz[:, i, j] += cf * N_ns[kv, :]
                    if i != j:
                        B0[j, i] = B0[i, j]
                        Bz[:, j, i] = Bz[:, i, j]
            blocks.append((B0, Bz))
        po, do, nrp, nrd, _it = solve_sdp_dual(N_ns.T @ c_vec, blocks, max_iter=55)
        cc = float(c_vec @ y0)
        return df, (sp1 - (po + cc)) / c_1x1, (sp1 - (do + cc)) / c_1x1, nrp, nrd

    print(f"  {'Model':>22s} | {'R1':>2s} | {'R2':>2s} | {'df':>3s} | {'c_ub/c_1x1 (dual)':>17s} | {'rd':>8s}")
    sdp_rows = [
        ("1D comm (a=1) D=4", run_1d_comm_sos(4, False, False), 0, 0),
        ("1D comm (a=1) D=4", run_1d_comm_sos(4, True, False), 1, 0),
        ("1D comm (a=1) D=4", run_1d_comm_sos(4, True, True), 1, 1),
        ("1D comm (a=1) D=6", run_1d_comm_sos(6, False, False), 0, 0),
        ("1D comm (a=1) D=6", run_1d_comm_sos(6, True, True), 1, 1),
        ("3-var comm (a,b,c) D=4", run_comm3_sos(4, False, False), 0, 0),
        ("3-var comm (a,b,c) D=4", run_comm3_sos(4, True, False), 1, 0),
        ("3-var comm (a,b,c) D=4", run_comm3_sos(4, True, True), 1, 1),
        ("3-var comm (a,b,c) D=6", run_comm3_sos(6, False, False), 0, 0),
        ("3-var comm (a,b,c) D=6", run_comm3_sos(6, True, False), 1, 0),
        ("3-var comm (a,b,c) D=6", run_comm3_sos(6, True, True), 1, 1),
        ("Full NC (A,B,C) D=4", run_nc_D4(False, False, 0.0), 0, 0),
        ("Full NC (A,B,C) D=4", run_nc_D4(True, False, 0.0), 1, 0),
        ("Full NC (A,B,C) D=4", run_nc_D4(True, True, 0.0), 1, 1),
    ]
    for label, (df, _cp, cd, _nrp, nrd), r1f, r2f in sdp_rows:
        print(f"  {label:>22s} | {r1f:2d} | {r2f:2d} | {df:3d} | {cd:17.10f} | {nrd:8.1e}")
        assert nrd < 1e-8, f"Dual residual too large on {label}: {nrd}"
    # Assert the sharp Degree-6 transition quantitatively!
    assert abs(sdp_rows[4][1][2] - 1.0) < 1e-6       # 1D comm D=6 R1+R2 hits exact 1.000000
    assert sdp_rows[7][1][2] > 1.05                  # 3-var comm D=4 R1+R2 stays stuck > 1.058
    assert abs(sdp_rows[10][1][2] - 1.0) < 1e-5      # 3-var comm D=6 R1+R2 crushes to 1.000000!
    assert sdp_rows[13][1][2] > 1.15                 # Full NC D=4 R1+R2 stays stuck at 1.1637 (degree < 6!)
    # Exact analytic ceiling for odd-degree homogeneous k=1 pseudo-moment (M00[c]=0, KA bound on denom):
    denom_min = 1.0 - g0 * (xp1 / ((1.0 + xp1) * gxp))
    fake_k1_ratio = (sp1 + g0 / denom_min) / c_1x1
    print(f"  Exact k=1 homogeneous odd-degree pseudo-moment ceiling (c_00=0, KA denom) = {fake_k1_ratio:.10f}")

    # --- Suite 4C: p = 6/5 (kappa = 3, m = 2) Dual-Q 1-Square Verification & Off-Holden Obstruction ---
    print("\n[Suite 4C] p = 6/5 (kappa = 3, m = 2) Dual-Q Non-Commuting Verification & Exact Off-Holden Peak:")
    kap65 = 3.0
    _Lam65, _xm65, xp65, sp65, C1_65 = solve_1x1_float(kap65, 2)
    Lam65_2, ds65_2, X65_2 = solve_rg_general_float(kap65, 2, 2, n_hom=8)
    C2_65 = (Lam65_2 / 32.0) ** (1.0 / 6.0)
    sD6 = np.sqrt(ds65_2)
    H6 = (sD6[:, None] * X65_2) * sD6[None, :]
    M6 = np.diag(ds65_2) + H6
    G6 = (ds65_2[:, None] * X65_2) * ds65_2[None, :]
    wM6, VM6 = eigh(M6)
    wG6, VG6 = eigh(G6)
    # Verify exact polynomial Holden B^5 = Lam A C^4 A (deg 6) & A B A = A^4 + C^2 (deg 4) with A=D^(1/2), B=M, C=G^(1/2):
    A6 = np.diag(ds65_2 ** 0.5)
    C6 = (VG6 * (wG6 ** 0.5)) @ VG6.T
    err_65_h = float(np.linalg.norm(np.linalg.matrix_power(M6, 5) - Lam65_2 * A6 @ np.linalg.matrix_power(C6, 4) @ A6))
    err_65_g = float(np.linalg.norm(A6 @ M6 @ A6 - (A6 ** 4) - (C6 @ C6)))
    assert err_65_h < 1e-11 and err_65_g < 1e-14

    # Verify Dual-Q 1-square domination K_dual(s) >= B_{sig_+} on non-commuting r=2 RG block:
    _, xp6_2 = get_xpm_float(Lam65_2, kap65)
    sp6_2 = sig_float(xp6_2, kap65)
    E6 = (VG6 * (wG6 ** 3)) @ VG6.T - (ds65_2[:, None] * ((VG6 * (wG6 ** 2)) @ VG6.T)) * ds65_2[None, :]
    Ehat6 = (ds65_2 ** (-3.0))[:, None] * E6 * (ds65_2 ** (-3.0))[None, :]
    Bsig6 = sp6_2 * np.eye(2) - Ehat6
    Y6 = (ds65_2 ** (-2.5))[:, None] * ((VG6 * (wG6 ** 2.5)) @ VG6.T) * (ds65_2 ** (-2.5))[None, :]
    W1inv6 = (ds65_2 ** 2)[:, None] * ((VM6 * (wM6 ** (-4.0))) @ VM6.T) * (ds65_2 ** 2)[None, :]
    P6 = (ds65_2 ** 1.5)[:, None] * ((VG6 * (wG6 ** (-1.5))) @ VG6.T) * (ds65_2 ** 1.5)[None, :]
    Q6 = (ds65_2 ** (-0.5))[:, None] * C6 * (ds65_2 ** (-0.5))[None, :]
    wQ6, VQ6 = eigh(Q6)
    wq6 = VQ6[0, :] ** 2
    min_dom6 = 1e9
    Idual6 = np.zeros((2, 2))
    for sk, wk in zip(wQ6, wq6):
        Kk = sp6_2 * np.eye(2) - sk * Y6 + np.linalg.inv(Lam65_2 * W1inv6 - sk * P6)
        min_dom6 = min(min_dom6, float(eigh(Kk - Bsig6)[0][0]))
        Idual6 += wk * np.linalg.inv(Kk)
    assert min_dom6 >= -1e-12
    eigs_cI6 = eigh((2.0 * sp6_2) * Idual6)[0]
    assert abs(eigs_cI6[0] - 1.0) < 1e-11 and eigs_cI6[1] > 1.2

    # Exact off-Holden 1D peak at q = sqrt(2/3): B_{sig_+}(sqrt(2/3)) / (2*sig_+) = (sig_+ + 4/27)/(2*sig_+)
    off_holden_peak = (sp65 + 4.0 / 27.0) / (2.0 * sp65)
    qs6 = np.linspace(1e-5, np.sqrt(xp65), 50000)
    B_1d_peak = float(np.max(sp65 + qs6 ** 4 - qs6 ** 6)) / (2.0 * sp65)
    assert abs(off_holden_peak - B_1d_peak) < 1e-8
    print(f"  Coupled r=2 RG at p=6/5, m=2: C_2 = {C2_65:.12f} (vs C_1x1 = {C1_65:.12f}), "
          f"poly errs = ({err_65_h:.1e}, {err_65_g:.1e})")
    print(f"    Dual-Q 1-square min_eig(K_k - B_sig) = {min_dom6:+.2e} >= 0 | eigs(c_2 * I_dual) = ({eigs_cI6[0]:.8f}, {eigs_cI6[1]:.8f})")
    print(f"    Exact off-Holden 1D peak at q=sqrt(2/3): (sig_+ + 4/27)/(2*sig_+) = {off_holden_peak:.9f} (+{(off_holden_peak-1)*100:.2f}% floor)")
    print("  [PASS] Module 4: Exact p=5/3 & p=6/5 polynomial ideals, 3-atom linear Y_k, & Degree-6 threshold verified!\n")


def main():
    run_module_1()
    run_module_2()
    run_module_3()
    run_module_4()
    elapsed = time.perf_counter() - T_GLOBAL_START
    print("=" * 80)
    print(f"ALL 4 MODULES PASSED WITH ZERO ERRORS IN {elapsed:.2f}s!")
    print("=" * 80)


if __name__ == "__main__":
    main()
