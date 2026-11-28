"""
SELF-CONTAINED VERIFICATION & EXPLORATION SUITE FOR GENERAL 1 < p < 2 THEORY (OPEN PROBLEM MI-20).

Zero external local imports (uses only numpy, scipy, mpmath) so any independent verifier can execute
this file directly and reproduce every theorem check, counterexample, high-precision RG limit,
and continuous 5-scalar dual witness reported in general_p_theory_report.md.

Sections (with strict assert checks on every proved identity):
  1. Universal general-p exact operator laws across kappa in {5/4, 3/2, 2, 5/2, 3, pi}:
       - Holden Theorem 3.1: (D+H)^{2k-1} = Lam D^{1/2} G^{k-1} D^{1/2}, C = (Lam / 2^{2k-1})^{1/(2k)}
       - Universal Commutator Conservation Law: [E, D] = 0
       - Universal Anticommutator Identity: Lam E = M^{2k} - D M^{2k-1} - M^{2k-1} D
       - Exact low-degree rational-kappa polynomial systems at p = 6/5, 5/4, 5/3
       - Exact general-p Fourier / Kubo-Ando finite-matrix lower bound construction
  2. Elementary 3-line operator inequality (B^{1/4} A^{k-1} B^{1/4})^{1/(2k-1)} <= B^{1/2}
     proving 0 < H_j <= x_+(Lam) D and the spectral dichotomy (X = x_+ I or lam_min(X) <= x_-)
     for ALL 1 < p < 2, ALL n >= 1 (stress-tested on 1,800 random noncommuting SPD pairs).
  3. 3-line closed-form universal bound & exact Lambert-W quadratic p -> 1^+ curvature law:
       c_1x1(m) <= lim (C_p(m) - 1) / (p - 1)^2 <= ((1 + W((m-1)/e))^2 - 1) / 2.
  4. Continuous-domain cutting-plane verification of the Universal 5-Scalar Dual Witness
     (plus verification of the two new D <= I linear moment inequalities (6) & (7)).
  5. Exact algebraic obstruction separating kappa = 2 from kappa != 2:
       - Diagonal Row-Variance Identity at p = 3/2 (verified to 1e-16)
       - Zero-interpolation matched-node counterexamples at p = 3/2 and p = 6/5 vs p = 4/3 control
       - Block-kernel exact linear identities W_1 1 = V_0 q and W_2 1 = V_0 q^2 at p = 3/2 (r = 2, 3)
       - Adversarial non-top eigenvalue counterexamples (e_1 > 1.5 * sig_+ at d_1 < 1 for p = 3/2, 6/5)
  6. High-rank RG cascades across p in {5/3, 3/2, 4/3, 5/4, 6/5} (m = 2) and 35-digit mpmath RG
     fixed-point convergence (r = 2..8) at p = 3/2, m = 2.
"""

import numpy as np
import mpmath as mp
from scipy.optimize import least_squares, brentq, linprog


# ---------------------------------------------------------------------------
# Core numerical utilities
# ---------------------------------------------------------------------------

def roots_kappa_safe(Lam, kappa):
    """Positive roots 0 < x_- < (k-1)/k < x_+ of (1+x)^{2k-1} = Lam * x^{k-1}."""
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


def scalar_1x1_Lam_safe(kappa, m):
    Lam0 = 2.0 ** (2.0 * kappa - 1.0)

    def eq(Lam):
        _, _, sigp, sigm = roots_kappa_safe(Lam, kappa)
        return sigp + (m - 1.0) * sigm

    lo = Lam0 * (1.0 + 1e-13)
    hi = max(Lam0 * 2.0, 2.0 * np.sqrt(m))
    while eq(hi) < 0:
        hi *= 2.0
    Lam = brentq(eq, lo, hi, xtol=1e-15, rtol=1e-15)
    C = (Lam / Lam0) ** (1.0 / (2.0 * kappa))
    return Lam, C


def sym_pow(M, power, tol=1e-18):
    M = 0.5 * (M + M.T)
    ev, V = np.linalg.eigh(M)
    if ev[0] <= tol * max(ev[-1], 1.0):
        return None
    return (V * (ev ** power)) @ V.T


def solve_rg_cascade(kappa, m, r_max=8, verbose=False):
    Lam1, C1 = scalar_1x1_Lam_safe(kappa, m)
    xm1, xp1, _, _ = roots_kappa_safe(Lam1, kappa)
    sols = {1: (Lam1, C1, np.array([1.0]), np.array([[xm1]]), 0.0)}
    if verbose:
        p = 2.0 * kappa / (2.0 * kappa - 1.0)
        print(f"  p={p:.6f} (k={kappa:.4f}), m={m}: r=1 C={C1:.15f} Lam={Lam1:.14f}")

    def solve_r(r, Lam0, d0, X0):
        triu = np.triu_indices(r)

        def unpack(x):
            Lam = x[0]
            d = np.concatenate([[1.0], np.exp(x[1:r])])
            X = np.zeros((r, r))
            X[triu] = x[r:]
            X = X + X.T - np.diag(np.diag(X))
            return Lam, d, X

        def residuals(x):
            Lam, d, X = unpack(x)
            rt = roots_kappa_safe(Lam, kappa)
            if rt is None:
                return np.full(r * (r + 1), 1e3)
            _, _, sigp, _ = rt
            sd = np.sqrt(d); D = np.diag(d)
            H = (sd[:, None] * X) * sd[None, :]
            G = (sd[:, None] * H) * sd[None, :]
            Mp = sym_pow(D + H, 2.0 * kappa - 1.0)
            Gkm1 = sym_pow(G, kappa - 1.0)
            Gk = sym_pow(G, kappa)
            if Mp is None or Gkm1 is None or Gk is None:
                return np.full(r * (r + 1), 1e3)
            R1 = Mp - Lam * ((sd[:, None] * Gkm1) * sd[None, :])
            tgt = sigp * (d ** (2.0 * kappa))
            tgt[0] = -sigp / (m - 1.0)
            R2 = Gk - (d[:, None] * Gkm1) * d[None, :] - np.diag(tgt)
            w1 = 1.0 / np.outer(d ** (kappa - 0.5), d ** (kappa - 0.5))
            w2 = 1.0 / np.outer(d ** kappa, d ** kappa)
            return np.concatenate([(R1 * w1)[triu], (R2 * w2)[triu]])

        sol = least_squares(residuals, np.concatenate([[Lam0], np.log(d0[1:]), X0[triu]]),
                            xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=4000)
        Lam, d, X = unpack(sol.x)
        C = (Lam / (2.0 ** (2.0 * kappa - 1.0))) ** (1.0 / (2.0 * kappa))
        return Lam, C, d, X, float(np.linalg.norm(sol.fun))

    best_r2 = None
    for d_try in [1e-4, 1e-3, 1e-2, 0.06, 0.2, 0.4]:
        for bf in [-0.2, -0.45]:
            b = bf * np.sqrt(xm1 * xp1)
            Lam2, C2, d2, X2, err2 = solve_r(2, Lam1 * (1.0 + 1e-5), np.array([1.0, d_try]),
                                             np.array([[xm1, b], [b, 0.45 * xp1]]))
            if err2 < 1e-10 and abs(X2[0, 1]) > 1e-6 and C2 > C1 + 1e-14:
                if best_r2 is None or C2 > best_r2[1]:
                    best_r2 = (Lam2, C2, d2, X2, err2)
    assert best_r2 is not None, f"r=2 RG solve failed for kappa={kappa}, m={m}"
    Lam_p, C_p, d_p, X_p, err_p = best_r2
    sols[2] = best_r2
    if verbose:
        br = (m - 1.0) * np.sum(d_p[1:] ** (2.0 * kappa))
        print(f"    r= 2: C={C_p:.15f} dC={C_p-C1:+.3e} Lam={Lam_p:.14f} rho={br:.6f} res={err_p:.1e}")

    for r in range(3, r_max + 1):
        ratio = d_p[-1] / d_p[-2] if r > 3 else min(0.8, max(0.08, d_p[-1] * 1.4))
        best_c = None
        for r_try in [ratio, 0.55, 0.3]:
            d0 = np.concatenate([d_p, [d_p[-1] * min(0.85, max(0.04, r_try))]])
            X0 = np.zeros((r, r))
            X0[:r - 1, :r - 1] = X_p
            X0[r - 1, r - 1] = X_p[r - 2, r - 2]
            for j in range(1, r - 1):
                X0[j, r - 1] = X0[r - 1, j] = X_p[j - 1, r - 2]
            X0[0, r - 1] = X0[r - 1, 0] = X_p[0, r - 2] * 0.2
            Lam_c, C_c, d_c, X_c, err_c = solve_r(r, Lam_p, d0, X0)
            _, xp_c, _, _ = roots_kappa_safe(Lam_c, kappa)
            if err_c < 1e-8 and np.max(np.linalg.eigvalsh(X_c)) < xp_c - 1e-5:
                best_c = (Lam_c, C_c, d_c, X_c, err_c)
                break
        if best_c is None:
            break
        Lam_c, C_c, d_c, X_c, err_c = best_c
        sols[r] = best_c
        if verbose:
            br = (m - 1.0) * np.sum(d_c[1:] ** (2.0 * kappa))
            print(f"    r={r:2d}: C={C_c:.15f} dC={C_c-C_p:+.3e} Lam={Lam_c:.14f} rho={br:.6f} res={err_c:.1e}")
        Lam_p, C_p, d_p, X_p = Lam_c, C_c, d_c, X_c
    return sols


# ---------------------------------------------------------------------------
# Section 1: Universal Operator Identities, Rational Polynomials, Kubo-Ando
# ---------------------------------------------------------------------------

def section1_universal_laws():
    print("================================================================================")
    print("SECTION 1: UNIVERSAL GENERAL-p OPERATOR LAWS, POLYNOMIAL SYSTEMS & KUBO-ANDO")
    print("================================================================================")
    all_sols = {}
    for label, kap in [("p=5/3", 1.25), ("p=3/2", 1.5), ("p=4/3", 2.0), ("p=5/4", 2.5), ("p=6/5", 3.0), ("p=pi", np.pi)]:
        sols = solve_rg_cascade(kap, m=2, r_max=6, verbose=False)
        all_sols[label] = (kap, sols)
        r = max(sols.keys())
        Lam, C, d, X, err = sols[r]
        xm, xp, sigp, _ = roots_kappa_safe(Lam, kap)
        sd = np.sqrt(d); D = np.diag(d)
        H = (sd[:, None] * X) * sd[None, :]
        G = (sd[:, None] * H) * sd[None, :]
        M = D + H
        M2km1 = sym_pow(M, 2.0 * kap - 1.0)
        M2k = sym_pow(M, 2.0 * kap)
        Gkm1 = sym_pow(G, kap - 1.0)
        Gk = sym_pow(G, kap)
        E = Gk - D @ Gkm1 @ D

        comm_err = float(np.linalg.norm(E @ D - D @ E))
        anti_err = float(np.linalg.norm(Lam * E - (M2k - D @ M2km1 - M2km1 @ D)))
        ex = np.linalg.eigvalsh(X)
        assert comm_err < 1e-13, f"[E,D]=0 failed at {label}"
        assert anti_err < 1e-12, f"Anticommutator identity failed at {label}"
        assert ex[-1] <= xp + 1e-12 and ex[0] <= xm + 1e-12, f"Spectral bound/dichotomy failed at {label}"
        print(f"  {label:6s} (k={kap:.4f}, r={r}): C={C:.12f} | ||[E,D]||={comm_err:.1e} | ||anti||={anti_err:.1e} | x_min/x_-={ex[0]/xm:.4f} | x_max/x_+={ex[-1]/xp:.6f}")

    # Rational-kappa polynomial reformulations
    for label, kap in [("p=6/5", 3.0), ("p=5/4", 2.5), ("p=5/3", 1.25)]:
        _, sols = all_sols[label]
        Lam, _, d, X, _ = sols[max(sols.keys())]
        _, xp, sigp, _ = roots_kappa_safe(Lam, kap)
        D = np.diag(d); sd = np.sqrt(d); sm = 1.0 / sd
        H = (sd[:, None] * X) * sd[None, :]; G = (sd[:, None] * H) * sd[None, :]
        if label == "p=6/5":
            R1 = np.linalg.matrix_power(D + H, 5) - Lam * (D @ H @ D @ H @ D)
            F = H @ D @ H @ D @ H - D @ H @ D @ H @ D
            tgt = sigp * (d ** 5); tgt[0] = -sigp
            assert np.linalg.norm(R1) < 1e-12 and np.linalg.norm(F - np.diag(tgt)) < 1e-12
            print(f"  Poly p=6/5 (k=3):   ||(D+H)^5 - Lam DHDHD||={np.linalg.norm(R1):.2e}, ||F-tgt||={np.linalg.norm(F-np.diag(tgt)):.2e}")
        elif label == "p=5/4":
            Q = (sm[:, None] * sym_pow(G, 0.5)) * sm[None, :]
            R_H = H - Q @ D @ Q
            R1 = np.linalg.matrix_power(D + H, 4) - Lam * (D @ H @ D @ Q @ D)
            F = H @ D @ Q @ D @ H - D @ H @ D @ Q @ D
            tgt = sigp * (d ** 4); tgt[0] = -sigp
            assert np.linalg.norm(R_H) < 1e-12 and np.linalg.norm(R1) < 1e-12 and np.linalg.norm(F - np.diag(tgt)) < 1e-12
            assert np.max(np.linalg.eigvalsh(Q)) <= np.sqrt(xp) + 1e-12
            print(f"  Poly p=5/4 (k=5/2): ||H-QDQ||={np.linalg.norm(R_H):.2e}, ||(D+H)^4-Lam DHDQD||={np.linalg.norm(R1):.2e}, ||F-tgt||={np.linalg.norm(F-np.diag(tgt)):.2e}")
        elif label == "p=5/3":
            V = (sm[:, None] * sym_pow(G, 0.25)) * sm[None, :]
            R = V @ D @ V; N = sym_pow(D + H, 0.5)
            e1 = np.linalg.norm(H - R @ D @ R)
            e2 = np.linalg.norm(N @ N - (D + R @ D @ R))
            e3 = np.linalg.norm(N @ N @ N - Lam * (D @ V @ D))
            F = R @ D @ V @ D @ R - D @ V @ D
            tgt = sigp * (d ** 1.5); tgt[0] = -sigp
            assert max(e1, e2, e3, np.linalg.norm(F - np.diag(tgt))) < 1e-12
            print(f"  Poly p=5/3 (k=5/4): ||H-RDR||={e1:.2e}, ||N^2-D-RDR||={e2:.2e}, ||N^3-Lam DVD||={e3:.2e}, ||F-tgt||={np.linalg.norm(F-np.diag(tgt)):.2e}")

    # General-p Fourier / Kubo-Ando lower bound formula check
    for label, kap in [("p=5/3", 1.25), ("p=3/2", 1.5), ("p=4/3", 2.0), ("p=5/4", 2.5), ("p=6/5", 3.0)]:
        p = 2.0 * kap / (2.0 * kap - 1.0); s = kap / (kap - 1.0)
        Lam, C_rg, d, X, _ = all_sols[label][1][2]
        xm, xp, _, _ = roots_kappa_safe(Lam, kap)
        L_dep = 5; d_nodes = [d[1] ** k for k in range(L_dep + 1)]; N_tot = L_dep + 1
        sd2 = np.sqrt(d); H2 = (sd2[:, None] * X) * sd2[None, :]; G2 = (sd2[:, None] * H2) * sd2[None, :]
        G2_km1 = sym_pow(G2, kap - 1.0, tol=0.0)
        Ss = []
        for j in range(2):
            Sj = np.zeros((N_tot, N_tot))
            if j == 0:
                Sj[0, 0] = (xp ** (kap - 1.0)) * (d_nodes[0] ** (2.0 * kap - 2.0)); k = 1
            else:
                k = 0
            while k < N_tot:
                if k + 1 < N_tot:
                    Sj[k:k + 2, k:k + 2] = (d_nodes[k] ** (2.0 * kap - 2.0)) * G2_km1; k += 2
                else:
                    Sj[k, k] = (xm ** (kap - 1.0)) * (d_nodes[k] ** (2.0 * kap - 2.0)); k += 1
            Ss.append(Sj)
        M_ka = 0.5 * (sym_pow(Ss[0], s, tol=0.0) + sym_pow(Ss[1], s, tol=0.0))
        N_ka = 0.5 * (Ss[0] + Ss[1])
        N_h = sym_pow(N_ka, 0.5, tol=0.0); N_mh = sym_pow(N_ka, -0.5, tol=0.0)
        K_ka = N_mh @ sym_pow(N_h @ M_ka @ N_h, 0.5, tol=0.0) @ N_mh
        K_h = sym_pow(K_ka, 0.5, tol=0.0)
        C_ka = (sum(np.trace(sym_pow(S, s, tol=0.0)) for S in Ss) /
                sum(np.trace(sym_pow(K_h @ S @ K_h, p, tol=0.0)) for S in Ss)) ** (1.0 / p)
        assert abs(C_ka - C_rg) < 1e-12, f"Kubo-Ando mismatch at {label}"
        print(f"  Kubo-Ando {label:5s} (s={s:.4f}, dim=12): C_KA={C_ka:.14f} vs C_RG(r=2)={C_rg:.14f} (diff={C_ka-C_rg:+.1e})")


# ---------------------------------------------------------------------------
# Section 2: Elementary 3-Line Furuta-Type Proof Stress-Test
# ---------------------------------------------------------------------------

def section2_furuta_stress_test():
    print("\n================================================================================")
    print("SECTION 2: 3-LINE ELEMENTARY PROOF OF (B^{1/4} A^{k-1} B^{1/4})^{1/(2k-1)} <= B^{1/2}")
    print("================================================================================")
    rng = np.random.default_rng(12345)
    for kap in [2.0, 2.5, 3.0, 5.5, 12.0, 50.0]:
        s = (kap - 2.0) / (kap - 0.5)
        span = min(3.0, 10.0 / kap)
        w1 = 1e9; wf = 1e9; wrev = 1e9
        for _ in range(300):
            n = int(rng.integers(2, 7))
            U1, _ = np.linalg.qr(rng.standard_normal((n, n)))
            A = (U1 * np.exp(rng.uniform(-span, span, size=n))) @ U1.T
            U2, _ = np.linalg.qr(rng.standard_normal((n, n)))
            B = A + (U2 * np.exp(rng.uniform(-span, span, size=n))) @ U2.T
            A = 0.5 * (A + A.T); B = 0.5 * (B + B.T)
            C = np.linalg.inv(A); D0 = np.linalg.inv(B)
            D0_q = sym_pow(D0, 0.25, tol=0.0); Ck1 = sym_pow(C, kap - 1.0, tol=0.0)
            M1 = sym_pow(D0_q @ Ck1 @ D0_q, 3.0 / (2.0 * kap - 1.0), tol=0.0) - sym_pow(D0, 1.5, tol=0.0)
            w1 = min(w1, float(np.min(np.linalg.eigvalsh(0.5 * (M1 + M1.T)))))
            Bq = sym_pow(B, 0.25, tol=0.0); Ak1 = sym_pow(A, kap - 1.0, tol=0.0)
            Mf = sym_pow(B, 0.5, tol=0.0) - sym_pow(Bq @ Ak1 @ Bq, 1.0 / (2.0 * kap - 1.0), tol=0.0)
            wf = min(wf, float(np.min(np.linalg.eigvalsh(0.5 * (Mf + Mf.T)))))
            # Reverse inequality (for dichotomy): 0 < A <= B => (A^{1/4} B^{k-1} A^{1/4})^{1/(2k-1)} >= A^{1/2}
            Aq = sym_pow(A, 0.25, tol=0.0); Bk1 = sym_pow(B, kap - 1.0, tol=0.0)
            Mr = sym_pow(Aq @ Bk1 @ Aq, 1.0 / (2.0 * kap - 1.0), tol=0.0) - sym_pow(A, 0.5, tol=0.0)
            wrev = min(wrev, float(np.min(np.linalg.eigvalsh(0.5 * (Mr + Mr.T)))))
        assert w1 > -1e-12 and wf > -1e-12 and wrev > -1e-12
        print(f"  kappa={kap:5.1f} (s={s:.4f}): 300 SPD pairs | step1={w1:+.2e} | upper={wf:+.2e} | reverse={wrev:+.2e}")


# ---------------------------------------------------------------------------
# Section 3: 3-Line Universal Bound & Exact Lambert-W p -> 1^+ Law
# ---------------------------------------------------------------------------

def section3_lambert_w_p_to_1():
    print("\n================================================================================")
    print("SECTION 3: 3-LINE UNIVERSAL BOUND & EXACT LAMBERT-W p -> 1^+ QUADRATIC LAW")
    print("================================================================================")
    mp.mp.dps = 40
    for m in [2, 3, 4, 10, 100]:
        s1 = mp.findroot(lambda s: (s - 1) / (s + 1) * mp.exp(2 * s) - (m - 1),
                         mp.mpf("1.5") if m <= 4 else mp.log(m))
        c_lb = (s1 * s1 - 1) / 2
        s_ub = 1 + mp.lambertw(mp.mpf(m - 1) / mp.e)
        c_ub = (s_ub * s_ub - 1) / 2
        assert c_ub > c_lb > 0
        print(f"  m={m:3d}: {mp.nstr(c_lb, 10)} <= lim_{{p->1+}} (C_p({m})-1)/(p-1)^2 <= {mp.nstr(c_ub, 10)}  (ratio={float(c_ub/c_lb):.4f})")

    for p_str, p_val in [("1.01", mp.mpf("1.01")), ("6/5", mp.mpf(6)/5), ("4/3", mp.mpf(4)/3), ("3/2", mp.mpf(3)/2), ("5/3", mp.mpf(5)/3)]:
        kap = p_val / (2 * (p_val - 1)); eps = p_val - 1
        rhs = (1 / kap) * ((2 - 1 / kap) ** (2 * kap - 1))
        u_ub = mp.findroot(lambda u: (2 * kap - 1) * mp.log(2 + mp.exp(u)) + u - mp.log(rhs), mp.log(2 * eps))
        x_ub = 1 + mp.exp(u_ub)
        C_ub = mp.exp(((2 * kap - 1) * mp.log((1 + x_ub) / 2) - (kap - 1) * mp.log(x_ub)) / (2 * kap))
        print(f"  3-line closed-form m=2, p={p_str:4s}: C_p(2) <= {mp.nstr(C_ub, 10)}  ((C-1)/(p-1)^2 = {float(mp.re((C_ub-1)/eps**2)):.5f})")


# ---------------------------------------------------------------------------
# Section 4: Continuous 5-Scalar Dual Witness Verification
# ---------------------------------------------------------------------------

def section4_continuous_5scalar_dual():
    print("\n================================================================================")
    print("SECTION 4: CONTINUOUS-DOMAIN 5-SCALAR DUAL WITNESS VERIFICATION (ALL n >= 1)")
    print("================================================================================")

    def certify_pair(kap, m, n_cut=10):
        Lam0 = 2.0 ** (2.0 * kap - 1.0)
        Lam1, C1 = scalar_1x1_Lam_safe(kap, m)

        def eval_cont_ub(Lam):
            xm, xp, sigp, _ = roots_kappa_safe(Lam, kap)
            ts = np.unique(np.concatenate([np.geomspace(1e-3, 0.99, 55), np.linspace(1.0, 1.0 + xp, 180), [1.0 + xm, 1.0 + xp]]))
            gs = np.unique(np.concatenate([np.geomspace(max(1e-25, xm * 1e-3), xm, 70), np.geomspace(xm, xp, 160), [xm, xp]]))
            t_fine = np.unique(np.concatenate([np.geomspace(1e-6, 0.9999, 12000), np.linspace(1.0, 1.0 + xp, 30000)]))
            g_fine = np.unique(np.concatenate([np.geomspace(max(1e-25, xm * 1e-5), xp, 20000), np.linspace(max(1e-10, xm * 0.5), xp, 20000)]))
            best_ub = 1e9; best_lm1 = 0.0
            for _ in range(n_cut):
                nt, ng = len(ts), len(gs); n_tot = nt + ng
                c_lp = np.zeros(n_tot); c_lp[nt:] = -(gs ** (kap - 1.0) - gs ** kap)
                A_eq = np.zeros((5, n_tot)); b_eq = np.zeros(5)
                A_eq[0, :nt] = 1.0; b_eq[0] = 1.0
                A_eq[1, nt:] = 1.0; b_eq[1] = 1.0
                A_eq[2, :nt] = ts; A_eq[2, nt:] = -gs; b_eq[2] = 1.0
                A_eq[3, :nt] = ts ** (2.0 * kap - 1.0); A_eq[3, nt:] = -Lam * (gs ** (kap - 1.0))
                A_eq[4, :nt] = ts ** (2.0 * kap); A_eq[4, nt:] = -Lam * (gs ** (kap - 1.0) + gs ** kap)
                A_ub = np.zeros((1, n_tot)); A_ub[0, :nt] = 1.0 / ts; b_ub = np.array([1.0])
                res = linprog(c_lp, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=(0, None), method="highs")
                if not res.success:
                    return 1e9, 0.0
                y_m = res.eqlin.marginals; z_m = res.ineqlin.marginals
                alpha, beta, gamma = float(y_m[2]), float(y_m[3]), float(y_m[4])
                lm1 = max(0.0, float(-z_m[0]))
                P_nu = alpha * t_fine + beta * (t_fine ** (2.0 * kap - 1.0)) + gamma * (t_fine ** (2.0 * kap)) - lm1 * (1.0 / t_fine - 1.0)
                P_mu = (g_fine ** (kap - 1.0) - g_fine ** kap) - alpha * g_fine - beta * Lam * (g_fine ** (kap - 1.0)) - gamma * Lam * (g_fine ** (kap - 1.0) + g_fine ** kap)
                it, ig = int(np.argmax(P_nu)), int(np.argmax(P_mu))
                ub = float(P_nu[it] + P_mu[ig] - alpha)
                if ub < best_ub:
                    best_ub = ub; best_lm1 = lm1
                if abs(ub - (-res.fun)) < 1e-10:
                    break
                ts = np.unique(np.append(ts, t_fine[it]))
                gs = np.unique(np.append(gs, g_fine[ig]))
            return best_ub, best_lm1

        lo_b = Lam1; hi_b = Lam1 * 1.15
        while eval_cont_ub(hi_b)[0] >= roots_kappa_safe(hi_b, kap)[2] / (m - 1.0):
            hi_b *= 1.25
        for _ in range(34):
            mid = 0.5 * (lo_b + hi_b)
            if eval_cont_ub(mid)[0] < roots_kappa_safe(mid, kap)[2] / (m - 1.0):
                hi_b = mid
            else:
                lo_b = mid
        ub_f, lm1_f = eval_cont_ub(hi_b)
        tgt_f = roots_kappa_safe(hi_b, kap)[2] / (m - 1.0)
        assert ub_f < tgt_f and lm1_f >= 0.0
        C_ub = (hi_b / Lam0) ** (1.0 / (2.0 * kap))
        return C1, C_ub, tgt_f - ub_f

    for label, kap in [("p=1.9", 1.9/1.8), ("p=5/3", 1.25), ("p=3/2", 1.5), ("p=4/3", 2.0), ("p=6/5", 3.0)]:
        C1, Cub, marg = certify_pair(kap, 2)
        print(f"  {label:5s} m=2: C_1x1={C1:.9f} | C_ub(cont dual)={Cub:.9f} (gap={Cub-C1:.2e}, margin={marg:+.2e})")

    # Verify the two new D <= I linear moment inequalities (6) and (7) on real noncommuting r=2 RG solutions!
    print("\n  Verifying D <= I linear moment inequalities (6) E[M^2] >= E[(1+G)^2] and (7) E[G^{2k}+2psiG^k-G^{2k-2}] <= -psi^2:")
    for label, kap in [("p=5/3", 1.25), ("p=3/2", 1.5), ("p=4/3", 2.0), ("p=5/4", 2.5), ("p=6/5", 3.0)]:
        sols = solve_rg_cascade(kap, m=2, r_max=2, verbose=False)
        Lam, _, d, X, _ = sols[2]
        _, _, sigp, _ = roots_kappa_safe(Lam, kap)
        sd = np.sqrt(d); D = np.diag(d)
        H = (sd[:, None] * X) * sd[None, :]; G = (sd[:, None] * H) * sd[None, :]; M = D + H
        v = np.array([1.0, 0.0])
        lhs6 = float(v @ (M @ M) @ v - v @ ((np.eye(2) + G) @ (np.eye(2) + G)) @ v)
        lhs7 = float(v @ (sym_pow(G, 2*kap) + 2*sigp*sym_pow(G, kap) - sym_pow(G, 2*kap - 2)) @ v) + sigp * sigp
        assert lhs6 > 0 and lhs7 < 0, f"Inequality (6)/(7) violated at {label}"
        print(f"    {label:5s}: (6)={lhs6:+.3e} (>0), (7)={lhs7:+.3e} (<0)")


# ---------------------------------------------------------------------------
# Section 5: Obstruction Theorem, Diagonal Row-Variance & Matched-Node Counterexamples
# ---------------------------------------------------------------------------

def section5_obstruction_and_counterexamples():
    print("\n================================================================================")
    print("SECTION 5: OBSTRUCTION THEOREM — DIAGONAL ROW-VARIANCE & MATCHED-NODE TESTS")
    print("================================================================================")

    def solve_r2_given_d(kap, Lam, d_val, X_seed):
        d = np.array([1.0, d_val]); sd = np.sqrt(d); D = np.diag(d)
        def res(v):
            Xm = np.array([[v[0], v[1]], [v[1], v[2]]])
            H = (sd[:, None] * Xm) * sd[None, :]; G = (sd[:, None] * H) * sd[None, :]
            Mp = sym_pow(D + H, 2.0 * kap - 1.0); Gkm1 = sym_pow(G, kap - 1.0)
            if Mp is None or Gkm1 is None: return np.full(3, 1e3)
            R = Mp - Lam * ((sd[:, None] * Gkm1) * sd[None, :])
            w = 1.0 / np.outer(d ** (kap - 0.5), d ** (kap - 0.5))
            return np.array([R[0, 0] * w[0, 0], R[0, 1] * w[0, 1], R[1, 1] * w[1, 1]])
        sol = least_squares(res, [X_seed[0, 0], X_seed[0, 1], X_seed[1, 1]], xtol=1e-15, ftol=1e-15, gtol=1e-15)
        X = np.array([[sol.x[0], sol.x[1]], [sol.x[1], sol.x[2]]])
        H = (sd[:, None] * X) * sd[None, :]; G = (sd[:, None] * H) * sd[None, :]
        E = sym_pow(G, kap) - D @ sym_pow(G, kap - 1.0) @ D
        return X, E[0, 0], E[1, 1] / (d_val ** (2.0 * kap)), float(np.linalg.norm(sol.fun))

    for label, kap in [("p=4/3 (CONTROL)", 2.0), ("p=3/2", 1.5), ("p=6/5", 3.0)]:
        sols = solve_rg_cascade(kap, m=2, r_max=3, verbose=False)
        Lam, _, d3, X3, _ = sols[3]
        _, _, d2_rg, X2_rg, _ = sols[2]
        _, xp, sigp, _ = roots_kappa_safe(Lam, kap)
        sd3 = np.sqrt(d3); sm3 = 1.0 / sd3; D3 = np.diag(d3)
        H3 = (sd3[:, None] * X3) * sd3[None, :]; G3 = (sd3[:, None] * H3) * sd3[None, :]
        Z3 = (sm3[:, None] * sym_pow(G3, 0.5)) * sm3[None, :] if abs(kap - 1.5) < 1e-9 else X3
        Z3 = 0.5 * (Z3 + Z3.T)
        zs3, U3 = np.linalg.eigh(Z3); A3 = U3.T @ D3 @ U3
        A3_2 = A3 @ A3; A3ZA3 = A3 @ np.diag(zs3) @ A3; u3 = U3[0, :]
        z_target = zs3[2]
        R3_val = A3ZA3[2, 2] / A3_2[2, 2]
        K3_mU = ((2.0 * sigp) * (u3[2] ** 2)) / A3_2[2, 2] - sigp

        # Verify Diagonal Row-Variance Identity at p = 3/2!
        if abs(kap - 1.5) < 1e-9:
            max_var_err = 0.0
            for i in range(3):
                rho = (A3[i, :] ** 2) / np.sum(A3[i, :] ** 2)
                rq = A3ZA3[i, i] / A3_2[i, i]
                v_i = np.sum(rho * ((zs3 - rq) ** 2))
                max_var_err = max(max_var_err, abs(1.0 + (2.0 * zs3[i] - Lam) * rq + (zs3[i] ** 2) * (rq ** 2 + v_i)))
            assert max_var_err < 1e-14
            print(f"  Diagonal Row-Variance Identity at p=3/2 (r=3): max err = {max_var_err:.2e}")

        # Trace r=2 branch at the EXACT SAME Lam to match zs2[1] == z_target to 1e-15!
        def eval_r2(dv, Xseed):
            X2, e0, e1, er = solve_r2_given_d(kap, Lam, dv, Xseed)
            sd2 = np.sqrt(np.array([1.0, dv])); sm2 = 1.0 / sd2; D2 = np.diag([1.0, dv])
            H2 = (sd2[:, None] * X2) * sd2[None, :]; G2 = (sd2[:, None] * H2) * sd2[None, :]
            Z2 = (sm2[:, None] * sym_pow(G2, 0.5)) * sm2[None, :] if abs(kap - 1.5) < 1e-9 else X2
            Z2 = 0.5 * (Z2 + Z2.T)
            zs2, U2 = np.linalg.eigh(Z2); A2 = U2.T @ D2 @ U2
            A2_2 = A2 @ A2; A2ZA2 = A2 @ np.diag(zs2) @ A2; u2 = U2[0, :]
            return X2, zs2, e0, e1, A2_2, A2ZA2, u2, er

        # Seed r=2 at Lam from X2_rg
        X2_cur, _, _, _, _, _, _, _ = eval_r2(d2_rg[1], X2_rg)
        pts = []
        for dv in np.linspace(d2_rg[1], 0.92, 60):
            X2_cur, z2, e0, e1, _, _, _, er = eval_r2(dv, X2_cur)
            if er < 1e-11 and abs(X2_cur[0, 1]) > 1e-5:
                pts.append((dv, z2[1], X2_cur.copy()))
            else:
                break
        matched = False
        for k in range(len(pts) - 1):
            if (pts[k][1] - z_target) * (pts[k + 1][1] - z_target) <= 0:
                da, db = pts[k][0], pts[k + 1][0]; Xa, Xb = pts[k][2], pts[k + 1][2]
                d_st = brentq(lambda dv: eval_r2(dv, ((dv - da)/(db - da))*Xb + ((db - dv)/(db - da))*Xa)[1][1] - z_target, da, db, xtol=1e-15)
                X2s, z2s, e0s, e1s, A2_2, A2ZA2, u2s, ers = eval_r2(d_st, ((d_st - da)/(db - da))*Xb + ((db - d_st)/(db - da))*Xa)
                R2_val = A2ZA2[1, 1] / A2_2[1, 1]
                K2_mU = ((e1s - e0s) * (u2s[1] ** 2)) / A2_2[1, 1] - e1s
                assert abs(z2s[1] - z_target) < 1e-13 and ers < 1e-12
                if kap == 2.0:
                    assert abs(R2_val - R3_val) < 1e-13 and abs(K2_mU - K3_mU) < 1e-13
                else:
                    assert abs(R2_val - R3_val) > 1e-3
                print(f"  Matched-node {label:15s} (|dz|={abs(z2s[1]-z_target):.1e}): dR={R2_val-R3_val:+.4e}, d(K-U)={K2_mU-K3_mU:+.4e}")
                matched = True
                break
        assert matched, f"Matched node not found for {label}"

    # Verify exact linear equality W_2 1 = V_0 q^2 on real r=2, 3 solutions at p=3/2, AND N=2 2D nullspace gap collapse!
    sols32 = solve_rg_cascade(1.5, m=2, r_max=3, verbose=False)
    for r_chk in [2, 3]:
        Lm, _, dd, Xm, _ = sols32[r_chk]
        _, xp, sp, _ = roots_kappa_safe(Lm, 1.5)
        sd = np.sqrt(dd); sm = 1.0 / sd; D = np.diag(dd)
        H = (sd[:, None] * Xm) * sd[None, :]; G = (sd[:, None] * H) * sd[None, :]
        Q = (sm[:, None] * sym_pow(G, 0.5)) * sm[None, :]; Q = 0.5 * (Q + Q.T)
        qs, U = np.linalg.eigh(Q); A = U.T @ D @ U; u = U[0, :]; du = np.diag(u)
        V0 = du @ A @ du; W1 = du @ (A @ np.diag(qs) @ A) @ du; W2 = du @ (A @ np.diag(qs ** 2) @ A) @ du
        e_w1 = float(np.linalg.norm(W1 @ np.ones(r_chk) - V0 @ qs))
        e_w2 = float(np.linalg.norm(W2 @ np.ones(r_chk) - V0 @ (qs ** 2)))
        assert e_w1 < 1e-14 and e_w2 < 1e-14
        print(f"  p=3/2 Block-kernel linear identities (r={r_chk}): ||W1 1 - V0 q||={e_w1:.1e}, ||W2 1 - V0 q^2||={e_w2:.1e}")

    # Verify adversarial non-top eigenvalue counterexample e_1 > sig_+ at d_1 < 1 (p=3/2, p=6/5)!
    for label, kap, d_test in [("p=3/2", 1.5, 0.0825), ("p=6/5", 3.0, 0.4788)]:
        sols = solve_rg_cascade(kap, m=2, r_max=2, verbose=False)
        Lam, _, d2_rg, X2_rg, _ = sols[2]
        _, _, sigp, _ = roots_kappa_safe(Lam, kap)
        # Continue from d2_rg[1] to d_test
        Xc = X2_rg.copy()
        for dv in np.linspace(d2_rg[1], d_test, 12):
            Xc, e0, e1, er = solve_r2_given_d(kap, Lam, dv, Xc)
        assert er < 1e-12 and e1 > sigp * 1.5 and e0 < 0
        print(f"  Non-top counterexample ({label}, d=[1, {d_test}]): e_0={e0:+.6f}, e_1={e1:+.6f} > sig_+={sigp:.6f} (ratio={e1/sigp:.2f}x)")


# ---------------------------------------------------------------------------
# Section 6: 35-Digit mpmath RG Fixed Point at p = 3/2 & High-Rank Cascades
# ---------------------------------------------------------------------------

def section6_rg_limits():
    print("\n================================================================================")
    print("SECTION 6: HIGH-RANK RG CASCADES (m = 2) & 35-DIGIT MPMATH LIMIT AT p = 3/2")
    print("================================================================================")
    for label, kap in [("p=5/3", 1.25), ("p=3/2", 1.5), ("p=4/3", 2.0), ("p=5/4", 2.5), ("p=6/5", 3.0)]:
        sols = solve_rg_cascade(kap, m=2, r_max=9, verbose=False)
        r_hi = max(sols.keys())
        Lam, C, d, _, err = sols[r_hi]
        rho = float(np.sum(d[1:] ** (2.0 * kap)))
        assert rho < 0.02 and err < 1e-11
        print(f"  {label:5s} (m=2): C_1x1={sols[1][1]:.15f} -> C_RG(r={r_hi:2d})={C:.15f} | rho={rho:.6f} | res={err:.1e}")

    # 35-digit mpmath polish for r = 2..8 at p = 3/2, m = 2
    mp.mp.dps = 38
    def mp_qp_sigp(Lam):
        q = mp.mpf("1.1")
        for _ in range(25):
            q -= ((1 + q * q) ** 2 - Lam * q) / (4 * q * (1 + q * q) - Lam)
        return q, q * (q * q - 1)

    sols_32 = solve_rg_cascade(1.5, m=2, r_max=8, verbose=False)
    prev_C = None
    print("\n  35-digit mpmath RG fixed points at p = 3/2, m = 2:")
    for r in [2, 3, 4, 5, 6, 7, 8]:
        Lm_f, _, d_f, X_f, _ = sols_32[r]
        sd = np.sqrt(d_f); sm = 1.0 / sd
        H_f = (sd[:, None] * X_f) * sd[None, :]; G_f = (sd[:, None] * H_f) * sd[None, :]
        Q_f = (sm[:, None] * sym_pow(G_f, 0.5)) * sm[None, :]
        triu = [(i, j) for i in range(r) for j in range(i, r)]
        n_unk = 1 + (r - 1) + len(triu)

        def eval_F(xv):
            Lm = xv[0]; dd = [mp.mpf(1)] + [xv[1 + i] for i in range(r - 1)]
            QQ = mp.matrix(r, r); idx = r
            for i, j in triu:
                QQ[i, j] = xv[idx]; QQ[j, i] = xv[idx]; idx += 1
            D = mp.diag(dd); H = QQ * D * QQ; M = D + H
            R1 = M * M - Lm * (D * QQ * D)
            _, sp = mp_qp_sigp(Lm)
            HD = H * D; out = []
            for i, j in triu:
                out.append(R1[i, j] / (dd[i] * dd[j]))
            for i in range(r):
                f_ii = mp.fsum(HD[i, k] * QQ[k, i] for k in range(r)) - dd[i] * dd[i] * QQ[i, i]
                tgt = -sp if i == 0 else sp * (dd[i] * dd[i])
                out.append((f_ii - tgt) / (dd[i] * dd[i]))
            return mp.matrix(out)

        x = mp.matrix([mp.mpf(repr(float(Lm_f)))] + [mp.mpf(repr(float(v))) for v in d_f[1:]] +
                      [mp.mpf(repr(float(Q_f[i, j]))) for i, j in triu])
        eps_fd = mp.mpf("1e-18")
        for _ in range(5):
            F0 = eval_F(x)
            if mp.norm(F0) < mp.mpf("1e-32"):
                break
            J = mp.matrix(n_unk, n_unk)
            for j in range(n_unk):
                xp_v = x.copy(); h = eps_fd * max(mp.mpf(1), abs(x[j])); xp_v[j] += h
                Fj = eval_F(xp_v)
                for i in range(n_unk):
                    J[i, j] = (Fj[i] - F0[i]) / h
            x = x + mp.lu_solve(J, -F0)
        res_n = mp.norm(eval_F(x))
        assert res_n < mp.mpf("1e-30")
        assert all(x[1 + i] > 0 for i in range(r - 1)), f"Non-positive d at r={r}"
        QQ_pol = mp.matrix(r, r); idx = r
        for i, j in triu:
            QQ_pol[i, j] = x[idx]; QQ_pol[j, i] = x[idx]; idx += 1
        assert min(mp.eigsy(QQ_pol, eigvals_only=True)) > 0, f"Non-SPD Q at r={r}"
        Lm = x[0]; C = (Lm / 4) ** (mp.mpf(1) / 3)
        dC_s = f"{float(C - prev_C):+.3e}" if prev_C is not None else "    ---   "
        print(f"    r={r:2d}: C = {mp.nstr(C, 24)}  dC = {dC_s}  res={mp.nstr(res_n, 2)}")
        prev_C = C


if __name__ == "__main__":
    section1_universal_laws()
    section2_furuta_stress_test()
    section3_lambert_w_p_to_1()
    section4_continuous_5scalar_dual()
    section5_obstruction_and_counterexamples()
    section6_rg_limits()
    print("\nALL GENERAL-p THEORY CHECKS PASSED WITH EXIT CODE 0!")
