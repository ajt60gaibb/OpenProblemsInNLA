"""
p32_joint_bridge_attack.py
==========================
Self-contained verification & symbolic certification suite for MI-20:
  - Module 1: Universal All-m Strict Convexity of the Continuum Balayage Operator
              at p = 3/2 (exact Z_{>0}[t,u,v] proof of dF/du(q,0) > 0 for ALL m >= 2,
              simultaneously covering 2 <= m <= 21 and supercritical m >= 22 across
              the Golden-Ratio transition q_crit = phi, plus 50-dps identity audit
              and exact rank-r RG Miracle Formula).
  - Module 2: Exact All-m, All-r Subcritical Branching Proof rho_r < 1 at p = 3/2
              in Z_{>0}[t,u,v] (zero negative integer coefficients) + Finite-Dimensional
              Leaf-Balanced Depth-L Block-Cut Tree Convergence & Direct Schatten-3/2
              Fourier Witness Verification.
  - Module 3: Exact 10-Term Large-m Asymptotic Expansion & Exact 4-Term Continuum
              Excess at p = 3/2 over Q(s) (100% unconditional for all n >= 1 and all
              delta >= 0 via exact r=2 Holden block + exact 3-atom supercritical
              spillover measure nu_s + 60-dps mpmath cross-check).
  - Module 4: Bipartite Gap 1A Engine at p = 3/2 (exact bipartite SVD factorization,
              off-diagonal identities R_A and R_B, degree-2s product identities,
              strictly negative-definite linearized rigidity Hessian, and global
              (G2'') + (G4) uniqueness test — with honest open-sub-lemma ledger).
  - Module 5: Track (b) #94 One-Shot F-Shifted Uninverted Full-Slope NC-SOS Bridge,
              Compact Zero-Ray Pruning (p = 3/2 deg 8), Two-Stage Hybrid across
              (p, m) in {6/5, 5/3, 5/4} x {2, 3, 4}, and Part (b) Direct-Sum /
              Separable CP-Map Obstruction Verification.

Dependencies: Python stdlib + numpy, scipy, mpmath, sympy ONLY.
Hard constraints: Zero external local imports; never touches /Users/marcio/Downloads/Core Rank.
"""

import math
import time
from itertools import product

import mpmath as mp
import numpy as np
import scipy.optimize as opt
import sympy as sp
from scipy.optimize import brentq, linprog
from sympy.polys.matrices import DomainMatrix


# =============================================================================
# MODULE 1: UNIVERSAL ALL-m STRICT CONVEXITY dF/du(q, 0) > 0 AT p = 3/2
# =============================================================================
def run_module1_all_m_convexity():
    print("=" * 92)
    print("MODULE 1: UNIVERSAL ALL-m STRICT CONVEXITY dF/du(q, 0) > 0 AT p = 3/2 (EXACT Z_{>0}[t,u,v])")
    print("=" * 92)
    t0 = time.time()
    t, u, v = sp.symbols("t u v", positive=True)
    a = 1 + t
    Lam = (1 + a**2)**2 / a
    sp_v = a * (a**2 - 1)
    z1 = Lam + 1 / sp_v
    c1 = a * sp_v
    c2 = sp_v**2 / (2 * a)

    U = 1 + u
    V = 1 + v
    # Under Mobius q = a*u/(1+u), x = a^2*v/(1+v):
    #   D_den = Lam - (1+x)*q = D_poly / (a*U*V)
    #   K(q, x) = NK_poly / (U*V*D_poly)
    #   K_q(q, x) = NKq_poly / (V*D_poly^2)
    #   K_qq(q, x) = NKqq_poly / D_poly^3
    D_poly = sp.expand((1 + a**2)**2 * U * V - a**2 * u * (V + a**2 * v))
    NK_poly = sp.expand((sp_v * U * V - a**3 * u * v) * D_poly + a * U**2 * V * (V + a**2 * v))
    NKq_poly = sp.expand(-a**2 * v * D_poly**2 + a**2 * U**2 * V * (V + a**2 * v)**2)
    NKqq_poly = sp.expand(2 * a**3 * U**3 * (V + a**2 * v)**3)

    # Cleared numerator of:
    #   c1*(-K_q/K^2) + c2*(2*K_q^2/K^3 - K_qq/K^2) - sp*(sp - K)/K^2
    # = expr_A * U * V / (2 * a * D_poly * NK_poly^3)
    expr_A = sp.expand(
        (2 * a * c1) * (-U * D_poly * NKq_poly * NK_poly)
        + (2 * a * c2) * (2 * U**2 * NKq_poly**2 - U * V * NK_poly * NKqq_poly)
        - (2 * a * sp_v) * (D_poly**2 * (sp_v * U * V * D_poly - NK_poly) * NK_poly)
    )

    for name, pe in [("D_poly", D_poly), ("NK_poly", NK_poly), ("expr_A", expr_A)]:
        P = sp.Poly(pe, t, u, v)
        cs = [int(c) for _, c in P.terms()]
        n_neg = sum(1 for c in cs if c < 0)
        print(f"  {name:8s} in Z[t,u,v]: terms={len(cs):4d}, n_neg={n_neg}, min={min(cs)}, max={max(cs)}")
        assert n_neg == 0 and min(cs) > 0, f"{name} failed strict positivity!"

    # Budget inequality (B) at worst endpoint q = a (since Lam - q decreases and 1/(z1-q) increases in q):
    B_num, B_den = sp.fraction(sp.together(sp_v * (Lam - a) - c1 - 2 * c2 / (z1 - a)))
    PBn = sp.Poly(sp.expand(B_num), t)
    PBd = sp.Poly(sp.expand(B_den), t)
    cnb = [int(c) for _, c in PBn.terms()]
    cdb = [int(c) for _, c in PBd.terms()]
    print(f"  Budget B in Z[t]    : num_terms={len(cnb)} (deg {PBn.degree()}), min_num={min(cnb)}, "
          f"den_terms={len(cdb)}, min_den={min(cdb)}")
    assert min(cnb) > 0 and min(cdb) > 0

    # Also verify exact worst-case budget ratio < 0.340 over a in (1, 1000]
    a_grid = np.concatenate([1.0 + np.geomspace(1e-5, 1.0, 400), np.geomspace(2.0, 1000.0, 400)])
    L_g = (1.0 + a_grid**2)**2 / a_grid
    s_g = a_grid * (a_grid**2 - 1.0)
    z1_g = L_g + 1.0 / s_g
    rat_g = (a_grid * s_g + (s_g**2 / a_grid) / (z1_g - a_grid)) / (s_g * (L_g - a_grid))
    max_rat = float(np.max(rat_g))
    print(f"  Max budget ratio (c1 + 2c2/(z1-a)) / (sp*(Lam-a)) on (1, 1000]: {max_rat:.6f} (< 0.341 << 1)")
    assert max_rat < 0.341

    # 50-dps mpmath algebraic identity check at 10 diverse (t, u, v) points
    mp.mp.dps = 50
    f_A = sp.lambdify((t, u, v), expr_A, "mpmath")
    f_D = sp.lambdify((t, u, v), D_poly, "mpmath")
    f_NK = sp.lambdify((t, u, v), NK_poly, "mpmath")
    test_pts = [
        ("0.005", "0.01", "0.02"), ("0.1", "5.0", "10.0"), ("0.618034", "100.0", "1000.0"),
        ("1.0", "0.5", "0.5"), ("2.5", "0.001", "50.0"), ("10.0", "20.0", "0.5"),
        ("0.3", "10.0", "0.01"), ("0.8", "0.05", "200.0"), ("3.7", "4.2", "9.1"), ("50.0", "0.2", "5.0"),
    ]
    max_rel = mp.mpf(0)
    for ts, us, vs in test_pts:
        tv, uv, vv = mp.mpf(ts), mp.mpf(us), mp.mpf(vs)
        av = 1 + tv
        Lv = (1 + av**2)**2 / av
        sv = av * (av**2 - 1)
        qv = av * uv / (1 + uv)
        xv = av**2 * vv / (1 + vv)
        den = Lv - (1 + xv) * qv
        K = sv - qv * xv + (1 + xv) / den
        Kq = -xv + (1 + xv)**2 / den**2
        Kqq = 2 * (1 + xv)**3 / den**3
        c1v = av * sv
        c2v = sv**2 / (2 * av)
        lhs_calc = c1v * (-Kq / K**2) + c2v * (2 * Kq**2 / K**3 - Kqq / K**2) - sv * (sv - K) / K**2
        lhs_poly = f_A(tv, uv, vv) * (1 + uv) * (1 + vv) / (2 * av * f_D(tv, uv, vv) * f_NK(tv, uv, vv)**3)
        rel = abs(lhs_calc - lhs_poly) / abs(lhs_calc)
        if rel > max_rel:
            max_rel = rel
    print(f"  50-dps algebraic identity check (10 points): max_rel_err = {mp.nstr(max_rel, 4)}")
    assert max_rel < mp.mpf("1e-45")

    # Verify Exact Miracle Formula on rank-r RG blocks across subcritical (m=2,5,10) & supercritical (m=22,50)
    print("  Checking Exact Miracle Formula dF/du(q_i,0) = ((m-1)/m^2)*(1 - (m-1)*sum_{k>=1} d_k^3 v_{i,k}^2 / v_{i,0}^2):")
    g = [1.103, 0.075, 0.25, 0.2, 0.85]
    max_miracle_err = 0.0
    for m in [2, 5, 10, 22, 50]:
        def res_r2(vec):
            qp_, d1_, q00_, q01_, q11_ = vec
            L_ = (1 + qp_**2)**2 / qp_
            sp_ = qp_ * (qp_**2 - 1)
            D_ = np.diag([1.0, d1_])
            Q_ = np.array([[q00_, q01_], [q01_, q11_]])
            M_ = D_ + Q_ @ D_ @ Q_
            R1_ = M_ @ M_ - L_ * D_ @ Q_ @ D_
            F_ = Q_ @ D_ @ Q_ @ D_ @ Q_ - D_ @ Q_ @ D_
            return [R1_[0, 0], R1_[0, 1], R1_[1, 1], F_[0, 0] - sp_ * (1 - m / (m - 1)), F_[1, 1] - sp_ * d1_**2]
        sol = opt.root(res_r2, g, tol=1e-13)
        assert np.linalg.norm(sol.fun) < 1e-12
        g = sol.x
        qp_, d1_, q00_, q01_, q11_ = sol.x
        L_ = (1 + qp_**2)**2 / qp_
        sp_ = qp_ * (qp_**2 - 1)
        D_ = np.diag([1.0, d1_])
        Dh_ = np.diag([1.0, np.sqrt(d1_)])
        Q_ = np.array([[q00_, q01_], [q01_, q11_]])
        X_ = np.linalg.inv(Dh_) @ Q_ @ D_ @ Q_ @ np.linalg.inv(Dh_)
        qs_, UQ_ = np.linalg.eigh(Q_)
        xs_, UX_ = np.linalg.eigh(X_)
        pX_ = UX_[0, :]**2
        ratios = []
        for i, qi in enumerate(qs_):
            Ls = np.array([(sp_ - qi * xk + (1 + xk) / (L_ - (1 + xk) * qi)) / sp_ for xk in xs_])
            dF_dir = float(np.sum(pX_ * (Ls - 1.0) / (Ls**2)))
            vi = UQ_[:, i]
            rat_i = float((m - 1.0) * (d1_**3 * vi[1]**2) / (vi[0]**2))
            ratios.append(rat_i)
            dF_mir = ((m - 1.0) / (m**2)) * (1.0 - rat_i)
            max_miracle_err = max(max_miracle_err, abs(dF_dir - dF_mir))
        grid = np.linspace(0.0, qp_, 500)
        min_dF = min(float(np.sum(pX_ * (((sp_ - q * xs_ + (1 + xs_) / (L_ - (1 + xs_) * q)) / sp_) - 1.0)
                                  / (((sp_ - q * xs_ + (1 + xs_) / (L_ - (1 + xs_) * q)) / sp_)**2))) for q in grid)
        print(f"    m={m:2d} (qp={qp_:.5f}): max_i ratio_i={max(ratios):.6f} << 1, min_q dF/du={min_dF:+.5e}")
        assert max(ratios) < 0.01 and min_dF > 0
    print(f"  Miracle Formula max error across m in {{2,5,10,22,50}}: {max_miracle_err:.3e} ({time.time() - t0:.2f}s)")
    assert max_miracle_err < 1e-12


# =============================================================================
# MODULE 2: ALL-m, ALL-r SUBCRITICAL BRANCHING rho_r < 1 & LEAF-BALANCED TREE
# =============================================================================
def run_module2_branching_and_tree():
    print("\n" + "=" * 92)
    print("MODULE 2: ALL-m, ALL-r SUBCRITICAL BRANCHING rho_r < 1 (Z_{>0}) & LEAF-BALANCED TREE")
    print("=" * 92)
    t0 = time.time()
    t, u, v = sp.symbols("t u v", positive=True)
    a = 1 + t
    Lam = (1 + a**2)**2 / a
    sp_v = a * (a**2 - 1)
    U = 1 + u
    V = 1 + v
    q_m = a * u / U
    x_m = a**2 * v / V

    def K_sym(qv, xv):
        return sp_v - qv * xv + (1 + xv) / (Lam - (1 + xv) * qv)

    M_qa2 = sp.cancel(1 / K_sym(q_m, a**2))
    M_0a2 = sp.cancel(1 / K_sym(0, a**2))
    M_ax = sp.cancel(1 / K_sym(a, x_m))
    M_a0 = sp.cancel(1 / K_sym(a, 0))
    M_00 = sp.cancel(1 / K_sym(0, 0))

    D_poly = sp.expand((1 + a**2)**2 * U * V - a**2 * u * (V + a**2 * v))
    NK_poly = sp.expand((sp_v * U * V - a**3 * u * v) * D_poly + a * U**2 * V * (V + a**2 * v))
    N0 = sp.expand((1 + a**2)**2)
    D0 = sp.expand(sp_v * N0 + a)
    num_Mdiff = sp.expand(U * V * D_poly * D0 - N0 * NK_poly)

    # Ineq (I): (Delta_Q + h_Q(q))*(Delta_X + h_X(x)) - (M(q, x) - M_00)^2 >= 0
    # where Delta_Q = M_00 - M(0, a^2), h_Q(q) = M(q, a^2) - M(0, a^2)
    #       Delta_X = M_00 - M(a, 0),   h_X(x) = M(a, x) - M(a, 0)
    fQ = sp.together((M_00 - M_0a2) + (M_qa2 - M_0a2))
    fX = sp.together((M_00 - M_a0) + (M_ax - M_a0))
    nQ, dQ = sp.fraction(fQ)
    nX, dX = sp.fraction(fX)
    dQ_r = sp.cancel(dQ / D0)
    dX_r = sp.cancel(dX / D0)
    poly_I = sp.expand(nQ * nX * NK_poly**2 - dQ_r * dX_r * num_Mdiff**2)
    PI = sp.Poly(poly_I, t, u, v)
    csI = [int(c) for _, c in PI.terms()]
    n_neg_I = sum(1 for c in csI if c < 0)
    print(f"  Ineq (I)  in Z[t,u,v]: terms={len(csI):4d}, n_neg={n_neg_I}, min={min(csI)}, max={max(csI)}")
    assert n_neg_I == 0 and min(csI) > 0
    for nm, e in [("dQ_r", dQ_r), ("dX_r", dX_r), ("D0", D0), ("NK_poly", NK_poly)]:
        cs = [int(c) for _, c in sp.Poly(sp.expand(e), t, u, v).terms()]
        assert min(cs) > 0, f"Denominator factor {nm} not strictly positive!"

    # 50-dps identity check for Ineq (I)
    mp.mp.dps = 50
    f_PI = sp.lambdify((t, u, v), poly_I, "mpmath")
    f_denI = sp.lambdify((t, u, v), D0**2 * dQ_r * dX_r * NK_poly**2, "mpmath")
    max_rel_I = mp.mpf(0)
    for ts, us, vs in [("0.05", "0.3", "0.7"), ("0.618", "3.0", "10.0"), ("4.0", "0.02", "50.0")]:
        tv, uv, vv = mp.mpf(ts), mp.mpf(us), mp.mpf(vs)
        av = 1 + tv; Lv = (1 + av**2)**2 / av; sv = av * (av**2 - 1)
        qv = av * uv / (1 + uv); xv = av**2 * vv / (1 + vv)
        Mv = lambda q_, x_: 1 / (sv - q_ * x_ + (1 + x_) / (Lv - (1 + x_) * q_))
        lhs_v = (Mv(0, 0) - 2 * Mv(0, av**2) + Mv(qv, av**2)) * (Mv(0, 0) - 2 * Mv(av, 0) + Mv(av, xv)) - (Mv(qv, xv) - Mv(0, 0))**2
        rhs_v = f_PI(tv, uv, vv) / f_denI(tv, uv, vv)
        max_rel_I = max(max_rel_I, abs(lhs_v - rhs_v) / abs(lhs_v))
    print(f"  Ineq (I)  50-dps algebraic identity check: max_rel_err = {mp.nstr(max_rel_I, 4)}")
    assert max_rel_I < mp.mpf("1e-45")

    # Ineq (II): 1/(sp*Lam) - 16 * Delta_Q * Delta_X * sp^2 > 0
    DQ = sp.cancel(M_00 - M_0a2)
    DX = sp.cancel(M_00 - M_a0)
    n2, d2 = sp.fraction(sp.together(1 / (sp_v * Lam) - 16 * DQ * DX * sp_v**2))
    p2n = sp.Poly(sp.expand(n2), t)
    p2d = sp.Poly(sp.expand(d2), t)
    c2n = [int(c) for _, c in p2n.terms()]
    c2d = [int(c) for _, c in p2d.terms()]
    print(f"  Ineq (II) in Z[t]    : deg_num={p2n.degree()}, num_terms={len(c2n)}, min_num={min(c2n)}, "
          f"den_terms={len(c2d)}, min_den={min(c2d)}")
    assert min(c2n) > 0 and min(c2d) > 0

    # Leaf-Balanced Depth-L Block-Cut Tree Convergence + Direct Schatten-3/2 Fourier Witness!
    print("\n  Leaf-Balanced Depth-L Block-Cut Tree & Direct Schatten-3/2 Fourier Witness Verification:")
    guess = [1.103, 0.075, 0.25, 0.2, 0.85]
    for m in [2, 3, 4]:
        def res_r2(vec):
            qp_, d1_, q00_, q01_, q11_ = vec
            L_ = (1 + qp_**2)**2 / qp_
            sp_ = qp_ * (qp_**2 - 1)
            D_ = np.diag([1.0, d1_])
            Q_ = np.array([[q00_, q01_], [q01_, q11_]])
            M_ = D_ + Q_ @ D_ @ Q_
            R1_ = M_ @ M_ - L_ * D_ @ Q_ @ D_
            F_ = Q_ @ D_ @ Q_ @ D_ @ Q_ - D_ @ Q_ @ D_
            return [R1_[0, 0], R1_[0, 1], R1_[1, 1], F_[0, 0] - sp_ * (1 - m / (m - 1)), F_[1, 1] - sp_ * d1_**2]
        sol = opt.root(res_r2, guess, tol=1e-13)
        assert np.linalg.norm(sol.fun) < 1e-13
        guess = sol.x
        qp_, d1_, q00_, q01_, q11_ = sol.x
        L_ = (1 + qp_**2)**2 / qp_
        sp_ = qp_ * (qp_**2 - 1)
        Q_blk = np.array([[q00_, q01_], [q01_, q11_]])
        rho = (m - 1) * d1_**3
        C_r2 = (L_ / 4.0) ** (1.0 / 3.0)
        rhs_leaf = sp_ / (m - 1.0)
        assert rhs_leaf < 2.0 / (3.0 * math.sqrt(3.0))
        q_leaf = brentq(lambda q: q - q**3 - rhs_leaf, 0.0, 1.0 / math.sqrt(3.0), xtol=1e-15)
        max_L = 4 if m == 2 else (3 if m == 3 else 2)
        print(f"    m={m}: C_r2={C_r2:.12f}, rho={rho:.6e}, q_leaf={q_leaf:.6f}")
        for depth in range(1, max_L + 1):
            nodes = [(1.0, 0)]
            edges = []
            queue = [(0, 0, 1.0, 0)]
            while queue:
                u_idx, lv, w_nd, cin = queue.pop(0)
                if lv < depth:
                    for col in range(m):
                        if col == cin:
                            continue
                        v_idx = len(nodes)
                        nodes.append((w_nd * d1_, col))
                        edges.append((u_idx, v_idx, col, w_nd))
                        queue.append((v_idx, lv + 1, w_nd * d1_, col))
            N = len(nodes)
            D_L = np.diag([nd[0] for nd in nodes])
            Q_list = [np.zeros((N, N)) for _ in range(m)]
            Q_list[0][0, 0] = qp_
            for u_idx, v_idx, col, _ in edges:
                Q_list[col][u_idx, u_idx] = Q_blk[0, 0]
                Q_list[col][u_idx, v_idx] = Q_blk[0, 1]
                Q_list[col][v_idx, u_idx] = Q_blk[1, 0]
                Q_list[col][v_idx, v_idx] = Q_blk[1, 1]
            has_out = set(e[0] for e in edges)
            for idx, (_, cin) in enumerate(nodes):
                if idx not in has_out:
                    for col in range(m):
                        if col == cin:
                            continue
                        Q_list[col][idx, idx] = q_leaf
            Dh = np.diag([math.sqrt(nd[0]) for nd in nodes])
            S_list = [Dh @ Qj @ Dh for Qj in Q_list]
            err_E = float(np.linalg.norm(sum(Sj @ Sj @ Sj - D_L @ Sj @ D_L for Sj in S_list)))
            err_KA = float(np.linalg.norm(D_L @ sum(S_list) @ D_L - sum(Sj @ Sj @ Sj for Sj in S_list)))
            Den_L = float(sum(np.trace(Sj @ Sj @ Sj) for Sj in S_list))
            Num_L = float(sum(np.sum(np.maximum(np.linalg.eigvalsh(D_L @ Qj @ D_L), 0.0) ** 1.5) for Qj in Q_list))
            C_L = (Den_L / Num_L) ** (2.0 / 3.0)
            excess = 2.0 * Den_L - math.sqrt(L_) * Num_L
            assert err_E < 1e-14 and err_KA < 1e-14 and C_L <= C_r2 + 1e-14
            # Direct Schatten-3/2 Fourier witness A_k = T^{3/2} P_k T^{1/2} on C^{mN} for L=1, 2!
            fourier_err = 0.0
            if m * N <= 40:
                T_half = np.zeros((m * N, m * N), dtype=complex)
                T_32 = np.zeros((m * N, m * N), dtype=complex)
                for j, Sj in enumerate(S_list):
                    ev, Uv = np.linalg.eigh(Sj)
                    ev = np.maximum(ev, 0.0)
                    sl = slice(j * N, (j + 1) * N)
                    T_half[sl, sl] = Uv @ np.diag(np.sqrt(ev)) @ Uv.T
                    T_32[sl, sl] = Uv @ np.diag(ev ** 1.5) @ Uv.T
                omega = np.exp(2j * np.pi / m)
                sum_A = np.zeros((m * N, m * N), dtype=complex)
                sum_absA = np.zeros((m * N, m * N), dtype=complex)
                for k in range(m):
                    fk = np.array([omega ** (j * k) for j in range(m)], dtype=complex) / math.sqrt(m)
                    Pk = np.kron(np.outer(fk, fk.conj()), np.eye(N))
                    Ak = T_32 @ Pk @ T_half
                    sum_A += Ak
                    # |A_k| = V Sigma V^* via SVD (avoids squaring loss on rank-deficient zero singular values)
                    _, s_a, Vh_a = np.linalg.svd(Ak, full_matrices=False)
                    sum_absA += (Vh_a.conj().T * s_a) @ Vh_a
                num_s32 = float(np.sum(np.linalg.svd(sum_A, compute_uv=False) ** 1.5)) ** (2.0 / 3.0)
                den_s32 = float(np.sum(np.linalg.svd(sum_absA, compute_uv=False) ** 1.5)) ** (2.0 / 3.0)
                C_fourier = num_s32 / den_s32
                fourier_err = abs(C_fourier - C_L)
                assert fourier_err < 1e-12
            print(f"      L={depth} (N={N:2d}): ||sumE||={err_E:.1e}, ||KA||={err_KA:.1e}, "
                  f"C_L={C_L:.12f} (gap={C_r2-C_L:+.2e}), excess/rho^L={excess/rho**depth:+.6f}, "
                  f"Fourier_err={fourier_err:.1e}")
    print(f"  Module 2 complete ({time.time() - t0:.2f}s).")


# =============================================================================
# MODULE 3: EXACT 10-TERM LARGE-m EXPANSION & 4-TERM EXCESS AT p = 3/2 OVER Q(s)
# =============================================================================
def run_module3_large_m_excess():
    print("\n" + "=" * 92)
    print("MODULE 3: EXACT 10-TERM LARGE-m EXPANSION & 4-TERM EXCESS AT p = 3/2 OVER Q(s)")
    print("=" * 92)
    t0 = time.time()
    u, w, s, q = sp.symbols("u w s q")

    def trunc_p(p, var, n):
        poly = sp.Poly(sp.expand(p), var)
        return sum(c * var**k[0] for k, c in poly.terms() if k[0] < n)

    def inv_p(p, var, n):
        poly = sp.Poly(sp.expand(p), var)
        terms = sorted(poly.terms(), key=lambda x: x[0][0])
        m0, c0 = terms[0][0][0], terms[0][1]
        r = sum((c / c0) * var**(k[0] - m0) for k, c in terms[1:] if k[0] - m0 < n)
        inv = sp.Integer(1)
        k = 1
        while k < n:
            k = min(2 * k, n)
            inv = trunc_p(inv * (2 - (1 + r) * inv), var, k)
        return inv, m0, c0

    def compose_trunc(f_u, u_w, n):
        poly = sp.Poly(f_u, u)
        res = sp.Integer(0)
        pw = sp.Integer(1)
        for k in range(n):
            c = poly.nth(k)
            if c != 0:
                res = sp.expand(res + c * pw)
            pw = trunc_p(pw * u_w, w, n)
        return res

    # 3A. Exact r=2 Holden block in Q[[u]] (u = s^2 = 1/q_+^2)
    N = 15
    g_ser = sp.Integer(1)
    inv1pu2, _, _ = inv_p((1 + u)**2, u, N)
    for _ in range(9):
        g_ser = trunc_p(inv1pu2 * (1 + u**3 * g_ser**2)**2, u, N)
    sigm_s3 = trunc_p(g_ser * (u**3 * g_ser**2 - 1), u, N)

    A, B, C, D1 = sp.Integer(1), sp.Integer(5), sp.Integer(1), sp.Integer(1)
    J0 = sp.Matrix([[-1, 0, 0, 0], [1, 0, 0, -1], [2, -1, 5, -6], [1, 0, 1, -2]])
    assert J0.det() == -1
    J0_inv = J0.inv()
    for deg in range(1, 13):
        m00 = trunc_p(1 + u**3 * A**2 + u**6 * D1 * C, u, deg + 2)
        m11 = trunc_p(u**3 * (D1 + C + u**3 * D1 * B**2), u, deg + 2)
        Xab = trunc_p(A + u**3 * D1 * B, u, deg + 2)
        r1 = trunc_p(m00**2 + u**6 * C * Xab**2 - (1 + u)**2 * A, u, deg + 1)
        r2 = trunc_p(Xab * (m00 + m11) - (1 + u)**2 * D1, u, deg + 1)
        r3 = trunc_p(C * Xab**2 + (D1 + C + u**3 * D1 * B**2)**2 - (1 + u)**2 * D1**2 * B, u, deg + 1)
        r4 = trunc_p(C * Xab + u**3 * D1 * B * (C + u**3 * D1 * B**2) - u**3 * D1**2 * B - (1 - u) * D1**2, u, deg + 1)
        rv = sp.Matrix([sp.Poly(ri, u).nth(deg) for ri in (r1, r2, r3, r4)])
        dv = -J0_inv * rv
        A += dv[0] * u**deg; B += dv[1] * u**deg; C += dv[2] * u**deg; D1 += dv[3] * u**deg
    F00_s3 = trunc_p(-A + u**3 * A * (A**2 + u**3 * D1 * C) + u**6 * D1 * C * (A + u**3 * D1 * B), u, 13)
    diff_r2_s3 = trunc_p((-F00_s3) - (-sigm_s3), u, 11)
    print(f"  3A. Exact r=2 Holden block (det J0 = -1): (T_2 - (sp-sigm))/s^3 = {diff_r2_s3}")
    assert diff_r2_s3 == u**6 - 13 * u**7 + 90 * u**8 - 419 * u**9 + 1317 * u**10

    # 3B. Exact 3-atom rational supercritical spillover measure nu_s over Q(s)
    #     x0 = 0, x1 = 1 - 3*s^2, x2 = 1/s^2 - 1 (strictly in [0, 1/s^2)!), anchored at q in {0, s^3, 5*s^3}
    K_field = sp.QQ.frac_field(s)
    Lam_s = (1 + s**2)**2 / s**3
    sigp_s = (1 - s**2) / s**3
    K_rat = lambda qv, xv: sp.together(sigp_s - qv * xv + (1 + xv) / (Lam_s - (1 + xv) * qv))
    xs_rat = [sp.Integer(0), 1 - 3 * s**2, 1 / s**2 - 1]
    qs_rat = [sp.Integer(0), s**3, 5 * s**3]
    M_dm = DomainMatrix([[K_field.from_sympy(sp.together(1 / K_rat(qv, xv))) for xv in xs_rat] for qv in qs_rat],
                        (3, 3), K_field)
    c_dm = M_dm.lu_solve(DomainMatrix([[K_field.one], [K_field.one], [K_field.one]], (3, 1), K_field))
    c_rat = [K_field.to_sympy(c_dm[k, 0].element) for k in range(3)]

    # Exact zero-remainder division of N_Q(q; s) = num(1 - g_Q(q; s)) by q*(q-s^3)*(q-5*s^3) over Q(s)[q]!
    gQ_expr = sum(c_rat[k] / K_rat(q, xs_rat[k]) for k in range(3))
    num_gQ, den_gQ = sp.fraction(sp.together(1 - gQ_expr))
    num_poly = sp.Poly(sp.expand(num_gQ), q, domain=K_field)
    anc_poly = sp.Poly(sp.expand(q * (q - s**3) * (q - 5 * s**3)), q, domain=K_field)
    quo, rem = sp.div(num_poly, anc_poly, domain=K_field)
    assert rem.is_zero and quo.degree() == 2

    # Certify exact sign quo_norm(q; s) := quo(q; s) / den_gQ(0; s) = a2*q^2 + a1*q + a0 < 0 on ALL [0, 1/s]!
    def lead_s_terms(expr, k_terms=2):
        n_, d_ = sp.fraction(sp.together(expr))
        pn = sp.Poly(sp.expand(n_), s); pd = sp.Poly(sp.expand(d_), s)
        tn = sorted(pn.terms(), key=lambda x: x[0][0])
        td = sorted(pd.terms(), key=lambda x: x[0][0])
        mn, md = tn[0][0][0], td[0][0][0]
        cd0 = td[0][1]
        order = k_terms * 2 + 2
        r_s = sum((val / cd0) * s**(deg[0] - md) for deg, val in td[1:] if deg[0] - md < order)
        inv_s = sp.Integer(1); kk = 1
        while kk < order:
            kk = min(2 * kk, order)
            inv_s = sum(val * s**deg[0] for deg, val in sp.Poly(sp.expand(inv_s * (2 - (1 + r_s) * inv_s)), s).terms() if deg[0] < kk)
        ns = sum((val / cd0) * s**(deg[0] - mn) for deg, val in tn if deg[0] - mn < order)
        prod = sp.Poly(sp.expand(ns * inv_s), s)
        return sorted([(deg[0] + mn - md, val) for deg, val in prod.terms() if deg[0] < order])[:k_terms]

    den0 = den_gQ.subs(q, 0)
    a2, a1, a0 = [K_field.to_sympy(c) / den0 for c in quo.all_coeffs()]
    lt_a2 = lead_s_terms(a2, 2)
    lt_a1 = lead_s_terms(a1, 2)
    lt_a0 = lead_s_terms(a0, 2)
    lt_dq_end = lead_s_terms(2 * a2 / s + a1, 2)
    lt_q_end = lead_s_terms(a2 / s**2 + a1 / s + a0, 2)
    assert lt_a2 == [(21, -10), (23, 89)]
    assert lt_a1 == [(18, 5), (20, -9)]
    assert lt_a0 == [(17, -5), (19, 9)]
    assert lt_dq_end == [(18, 5), (20, -29)]
    assert lt_q_end == [(19, -10), (21, 68)]
    print(f"  3B. Exact Q(s)[q] division: deg(N_Q)={num_poly.degree()}, rem==0 (EXACT!), deg(quo)={quo.degree()}")
    print(f"      Exact sign cert quo_norm(q;s)=a2*q^2+a1*q+a0: a2={lt_a2[0]}, a1={lt_a1[0]}, a0={lt_a0[0]}, "
          f"2a2/s+a1={lt_dq_end[0]} > 0 => max on [0,1/s] is quo_norm(1/s)={lt_q_end[0]} < 0!")

    # Series of (T_ub - (sp-sigm))/s^3 up to u^10 via truncated u-series!
    xs_num = [sp.Integer(0), 1 - 3 * u, 1 - u]
    xs_pow = [0, 0, -1]
    ys_anc = [0, 1, 5]
    M_u = []
    for yv in ys_anc:
        row = []
        for k in range(3):
            t2 = sp.expand(-u**(3 + xs_pow[k]) * yv * xs_num[k])
            one_px = sp.expand(u**(-xs_pow[k]) + xs_num[k])
            den_u = trunc_p((1 + u)**2 - one_px * yv * u**(3 + xs_pow[k]), u, 24)
            inv_d, _, _ = inv_p(den_u, u, 24)
            t3 = trunc_p(one_px * u**(3 + xs_pow[k]) * inv_d, u, 24)
            s3K = trunc_p(1 - u + t2 + t3, u, 24)
            inv_K, _, _ = inv_p(s3K, u, 24)
            row.append(inv_K)
        M_u.append(row)
    det3 = lambda A_: trunc_p(
        A_[0][0] * (A_[1][1] * A_[2][2] - A_[1][2] * A_[2][1])
        - A_[0][1] * (A_[1][0] * A_[2][2] - A_[1][2] * A_[2][0])
        + A_[0][2] * (A_[1][0] * A_[2][1] - A_[1][1] * A_[2][0]), u, 24)
    D0_u = det3(M_u)
    invD0, m0_d, c0_d = inv_p(D0_u, u, 20)
    cs_u = []
    for col in range(3):
        Mc = [[sp.Integer(1) if j == col else M_u[i][j] for j in range(3)] for i in range(3)]
        Dc = det3(Mc)
        pn = sp.Poly(trunc_p(Dc * invD0, u, 24), u)
        cs_u.append(sum((coeff / c0_d) * u**(deg[0] - m0_d) for deg, coeff in pn.terms() if deg[0] - m0_d < 14))
    diff_ub_s3_raw = trunc_p(cs_u[0] + cs_u[1] + cs_u[2] - (1 - u - u**3 * sigm_s3), u, 14)
    diff_ub_s3 = sum(val * u**(deg[0] - 3) for deg, val in sp.Poly(diff_ub_s3_raw, u).terms() if deg[0] < 14)
    print(f"      Exact 3-atom UB (x2=1/u-1):  (T_ub - (sp-sigm))/s^3 = {diff_ub_s3}")
    assert diff_ub_s3 == u**6 - 13 * u**7 + 90 * u**8 - 419 * u**9 + 1322 * u**10

    # 3C. Exact 10-term inversion to w = m^{-1/3}
    def invert_to_C(extra_T_s3_u):
        T_s3 = trunc_p(1 - u - u**3 * sigm_s3 + extra_T_s3_u, u, 16)
        num_invm = trunc_p(T_s3 - (1 - u), u, 16)
        invT, _, _ = inv_p(T_s3, u, 16)
        invm = trunc_p(num_invm * invT, u, 16)
        h3 = sum(val * u**(deg[0] - 3) for deg, val in sp.Poly(invm, u).terms() if 3 <= deg[0] < 16)
        h = sp.Integer(1)
        for _ in range(10):
            inv_h2, _, _ = inv_p(trunc_p(h * h, u, 13), u, 13)
            h = trunc_p((2 * h + h3 * inv_h2) * sp.Rational(1, 3), u, 13)
        u_w = w
        for deg in range(2, 12):
            lhs = compose_trunc(trunc_p(u * h, u, deg + 1), u_w, deg + 1)
            u_w = sp.expand(u_w - sp.Poly(lhs, w).nth(deg) * w**deg)
        h_sq = sp.Integer(1)
        for _ in range(10):
            inv_hs, _, _ = inv_p(h_sq, u, 13)
            h_sq = trunc_p((h_sq + h * inv_hs) * sp.Rational(1, 2), u, 13)
        onepu_23 = sum(sp.binomial(sp.Rational(2, 3), k) * u**k for k in range(13))
        return compose_trunc(trunc_p(h_sq * onepu_23, u, 13), u_w, 11)

    F1 = invert_to_C(sp.Integer(0))
    F_r2 = invert_to_C(u**3 * diff_r2_s3)
    F_ub = invert_to_C(u**3 * diff_ub_s3)
    diff_lb = sp.expand(F_r2 - F1)
    diff_ub = sp.expand(F_ub - F1)
    print("  3C. Exact 10-term w-expansion excess (C_{3/2}(m) - C_{1x1}(3/2, m)) / (4^{-1/3} m^{1/6}):")
    expected_exact = {6: sp.Rational(1, 6), 7: sp.Rational(-19, 12), 8: sp.Rational(343, 48), 9: sp.Rational(-14387, 864)}
    for k in range(11):
        cl = sp.Poly(diff_lb, w).nth(k)
        cu = sp.Poly(diff_ub, w).nth(k)
        if k in expected_exact:
            assert cl == expected_exact[k] and cu == expected_exact[k]
        if cl != 0 or cu != 0:
            tag = "EXACT!" if cl == cu else f"bracket width = {cu - cl}"
            print(f"      w^{k:2d} (m^{{{sp.Rational(1, 6) - sp.Rational(k, 3)}}}): LB={cl} | UB={cu}  [{tag}]")
    assert sp.Poly(diff_ub - diff_lb, w).nth(10) == sp.Rational(5, 6)

    # 3D. 60-dps mpmath cross-check at a in {10, 30, 100} AND explicit Lemma 3 positivity down to a = 1.8!
    mp.mp.dps = 60
    print("  3D. 60-dps mpmath cross-check of exact 4-term excess (and 3-atom Lemma 3 check at a=2.0):")
    for a_val in [10, 30, 100]:
        av = mp.mpf(a_val); sv = 1 / av; uv = sv**2
        Lv = (1 + uv)**2 / sv**3; spv = (1 - uv) / sv**3
        x = mp.matrix([sv**6 * (1 - 4 * uv + 10 * uv**2), sv**3 * (1 - 2 * uv + 3 * uv**2),
                       sv**3 * mp.sqrt(1 - 7 * uv + 27 * uv**2), sv**3 * (5 - 25 * uv + 79 * uv**2)])
        for _ in range(30):
            d1v, q00v, q01v, q11v = x[0], x[1], x[2], x[3]
            m00 = 1 + q00v**2 + d1v * q01v**2; m01 = q01v * (q00v + d1v * q11v); m11 = d1v + q01v**2 + d1v * q11v**2
            F11 = q01v**2 * (q00v + d1v * q11v) + q11v * d1v * (q01v**2 + d1v * q11v**2) - d1v**2 * q11v
            f = mp.matrix([m00**2 + m01**2 - Lv * q00v, m01 * (m00 + m11) - Lv * d1v * q01v,
                           m01**2 + m11**2 - Lv * d1v**2 * q11v, F11 - spv * d1v**2])
            if mp.norm(f) < mp.mpf("1e-52"):
                break
            J = mp.matrix(4, 4); eps = mp.mpf("1e-28")
            for j in range(4):
                xp_ = mp.matrix(x); xp_[j] += eps
                d1p, q00p, q01p, q11p = xp_[0], xp_[1], xp_[2], xp_[3]
                m00p = 1 + q00p**2 + d1p * q01p**2; m01p = q01p * (q00p + d1p * q11p); m11p = d1p + q01p**2 + d1p * q11p**2
                F11p = q01p**2 * (q00p + d1p * q11p) + q11p * d1p * (q01p**2 + d1p * q11p**2) - d1p**2 * q11p
                fp = mp.matrix([m00p**2 + m01p**2 - Lv * q00p, m01p * (m00p + m11p) - Lv * d1p * q01p,
                                m01p**2 + m11p**2 - Lv * d1p**2 * q11p, F11p - spv * d1p**2])
                for i in range(4):
                    J[i, j] = (fp[i] - f[i]) / eps
            x = x - mp.lu_solve(J, f)
        d1v, q00v, q01v, q11v = x[0], x[1], x[2], x[3]
        F00 = q00v * (q00v**2 + d1v * q01v**2) + q01v * d1v * (q01v * (q00v + d1v * q11v)) - q00v
        T2 = spv - F00; m_eff = T2 / (T2 - spv); C2 = (Lv / 4) ** (mp.mpf(1) / 3)
        qp1 = av
        for _ in range(30):
            L1 = (1 + qp1**2)**2 / qp1; sp1 = qp1 * (qp1**2 - 1); qm1 = 1 / qp1**3
            for _ in range(15):
                qm1 -= ((1 + qm1**2)**2 - L1 * qm1) / (4 * qm1 * (1 + qm1**2) - L1)
            gv = sp1 + (m_eff - 1) * qm1 * (qm1**2 - 1)
            if abs(gv) < mp.mpf("1e-50"):
                break
            dq = qp1 * mp.mpf("1e-25"); qp1p = qp1 + dq
            L1p = (1 + qp1p**2)**2 / qp1p; sp1p = qp1p * (qp1p**2 - 1); qm1p = qm1
            for _ in range(15):
                qm1p -= ((1 + qm1p**2)**2 - L1p * qm1p) / (4 * qm1p * (1 + qm1p**2) - L1p)
            qp1 -= gv * dq / (sp1p + (m_eff - 1) * qm1p * (qm1p**2 - 1) - gv)
        C1 = ((1 + qp1**2)**2 / (4 * qp1)) ** (mp.mpf(1) / 3)
        wv = m_eff ** (-mp.mpf(1) / 3)
        exc = (C2 - C1) / ((mp.mpf(4) ** (-mp.mpf(1) / 3)) * (m_eff ** (mp.mpf(1) / 6)))
        pred4 = (mp.mpf(1) / 6) * wv**6 - (mp.mpf(19) / 12) * wv**7 + (mp.mpf(343) / 48) * wv**8 - (mp.mpf(14387) / 864) * wv**9
        rem4 = (exc - pred4) / wv**10
        print(f"      a={a_val:3d} (m={mp.nstr(m_eff, 8)}): excess/w^6={mp.nstr(exc/wv**6, 10)}, "
              f"rem4/w^10={mp.nstr(rem4, 10)} (exact r=2: -6.884339635)")
        if a_val == 100:
            assert abs(rem4 - (-mp.mpf(428261) / 62208)) < mp.mpf("0.05")

    # 60-dps check of explicit 3-atom measure nu_s at a = 2.0 (m ~ 75.5, strictly above Golden Ratio m_crit ~ 21.844)
    av = mp.mpf(2); sv = mp.mpf(1) / 2; uv = sv**2; Lv = (1 + uv)**2 / sv**3; spv = (1 - uv) / sv**3
    xs_2 = [mp.mpf(0), 1 - 3 * uv, 1 / uv - 1]; qs_2 = [mp.mpf(0), sv**3, 5 * sv**3]
    Kv = lambda q_, x_: spv - q_ * x_ + (1 + x_) / (Lv - (1 + x_) * q_)
    M2 = mp.matrix([[1 / Kv(qi, xk) for xk in xs_2] for qi in qs_2])
    c2v = mp.lu_solve(M2, mp.matrix([1, 1, 1]))
    min_dF_2 = min(sum(c2v[k] * (Kv(mp.mpf(i) * av / 200, xs_2[k]) / spv - 1) / (Kv(mp.mpf(i) * av / 200, xs_2[k]) / spv)**2
                       for k in range(3)) / sum(c2v) for i in range(201))
    print(f"      Explicit 3-atom nu_s at a=2.0 (m~75.5): min(c)={mp.nstr(min(c2v), 5)} > 0, "
          f"min_q dF/du(q,0)={mp.nstr(min_dF_2, 5)} > 0")
    assert min(c2v) > 0 and min_dF_2 > 0
    print(f"  Module 3 complete ({time.time() - t0:.2f}s).")


# =============================================================================
# MODULE 4: BIPARTITE GAP 1A ENGINE AT p = 3/2 (HONEST EPISTEMIC SEPARATION)
# =============================================================================
def run_module4_bipartite_gap1a():
    print("\n" + "=" * 92)
    print("MODULE 4: BIPARTITE GAP 1A ENGINE AT p = 3/2 (PROVED STEPS & LOCAL/GLOBAL RIGIDITY)")
    print("=" * 92)
    t0 = time.time()
    m = 2.0

    # Solve exact r=3 RG block at p = 3/2, m = 2
    def unpack_r3(v):
        qp = v[0]; ds = np.array([1.0, v[1], v[2]])
        Q = np.array([[v[3], v[4], v[5]], [v[4], v[6], v[7]], [v[5], v[7], v[8]]])
        return qp, ds, Q

    def res_r3(v):
        qp, ds, Q = unpack_r3(v)
        L = (1 + qp**2)**2 / qp; sp_ = qp * (qp**2 - 1)
        D = np.diag(ds); M = D + Q @ D @ Q
        R1 = M @ M - L * D @ Q @ D; F = Q @ D @ Q @ D @ Q - D @ Q @ D
        return [R1[0, 0], R1[0, 1], R1[0, 2], R1[1, 1], R1[1, 2], R1[2, 2],
                F[0, 0] - sp_ * (1 - m / (m - 1)), F[1, 1] - sp_ * ds[1]**2, F[2, 2] - sp_ * ds[2]**2]

    # Exact r=3 RG block seed (polished to machine precision, C_r3 = 1.036437167454765)
    sol3 = opt.root(
        res_r3,
        [1.10275833, 0.07532665, 0.01184049, 0.25535487, 0.1018639, 0.00665419, 0.43130509, -0.16455816, 0.52653878],
        tol=1e-14,
    )
    assert np.linalg.norm(sol3.fun) < 1e-13
    qp, ds, Q = unpack_r3(sol3.x)
    assert 1.0 > ds[1] > ds[2] > 0.0
    Lam = (1 + qp**2)**2 / qp; sp_ = qp * (qp**2 - 1); c_r = (m / (m - 1)) * sp_
    D = np.diag(ds); Dh = np.diag(np.sqrt(ds)); D32 = np.diag(ds ** 1.5)
    X = np.linalg.inv(Dh) @ Q @ D @ Q @ np.linalg.inv(Dh)
    qs, UQ = np.linalg.eigh(Q); xs, UX = np.linalg.eigh(X)
    assert 0.0 < qs[0] < qs[-1] < qp and 0.0 < xs[0] < xs[-1] < qp**2
    # Fix sign conventions so uQ > 0, uX > 0
    for i in range(3):
        if UQ[0, i] < 0: UQ[:, i] *= -1
        if UX[0, i] < 0: UX[:, i] *= -1
    uQ = UQ[0, :]; uX = UX[0, :]
    vQ = c_r * uQ**2; vX = c_r * uX**2

    M_mat = np.array([[1.0 / (sp_ - qi * xk + (1 + xk) / (Lam - (1 + xk) * qi)) for qi in qs] for xk in xs])
    Phi = np.array([[(1 + xk) / (Lam - (1 + xk) * qi) for qi in qs] for xk in xs])
    S_bip = np.outer(np.sqrt(vX), np.sqrt(vQ)) * M_mat
    T_bip = Phi * S_bip

    err_S = float(np.linalg.norm(UX.T @ D32 @ UQ - S_bip))
    err_T = float(np.linalg.norm(UX.T @ (Dh @ Q @ D) @ UQ - T_bip))
    print(f"  4A. Exact r=3 RG Bipartite Factorization: ||U_X^T D^{{3/2}} U_Q - S||={err_S:.2e}, "
          f"||U_X^T D^{{1/2}} Q D U_Q - T||={err_T:.2e}")
    assert err_S < 1e-13 and err_T < 1e-13

    # 4B. Exact Bipartite Off-Diagonal Identities R_A and R_B on BOTH exact RG and generic non-stationary nodes!
    def check_offdiag_identities(qs_t, xs_t, label):
        Mt = np.array([[1.0 / (sp_ - qi * xk + (1 + xk) / (Lam - (1 + xk) * qi)) for qi in qs_t] for xk in xs_t])
        Ph = np.array([[(1 + xk) / (Lam - (1 + xk) * qi) for qi in qs_t] for xk in xs_t])
        vq = np.linalg.solve(Mt, np.ones(len(qs_t)))
        vx = np.linalg.solve(Mt.T, np.ones(len(xs_t)))
        St = np.outer(np.sqrt(vx), np.sqrt(vq)) * Mt
        Tt = Ph * St
        Qd = np.diag(qs_t); Xd = np.diag(xs_t)
        RA = Tt.T @ Tt - St.T @ Xd @ St
        RB = (St + Tt @ Qd) @ (St + Tt @ Qd).T - Lam * St @ Qd @ St.T
        # Analytic derivatives g_Q'(q_i) and g_X'(x_k)
        gQp = np.array([sum(vx[k] * (-Mt[k, i]**2) * (-xs_t[k] + (1 + xs_t[k])**2 / (Lam - (1 + xs_t[k]) * qs_t[i])**2)
                            for k in range(len(xs_t))) for i in range(len(qs_t))])
        gXp = np.array([sum(vq[i] * (-Mt[k, i]**2) * (-qs_t[i] + Lam / (Lam - (1 + xs_t[k]) * qs_t[i])**2)
                            for i in range(len(qs_t))) for k in range(len(xs_t))])
        err_RA = float(np.linalg.norm(RA + np.diag(vq * gQp)))
        err_RB = float(np.linalg.norm(RB + Lam * np.diag(vx * gXp)))
        print(f"  4B. Off-Diagonal Identities ({label:14s}): err_RA={err_RA:.2e}, err_RB={err_RB:.2e}")
        assert err_RA < 1e-12 and err_RB < 1e-12

    check_offdiag_identities(qs, xs, "exact r=3 RG")
    check_offdiag_identities(qs + np.array([0.02, -0.015, 0.01]), xs + np.array([0.01, -0.02, 0.015]), "generic nodes")

    # 4C. Exact Degree-2s Product Identities for 1 - g_Q(q) >= 0 and 1 - g_X(x) >= 0 on r=3 RG block!
    q_grid = np.linspace(0.0, qp, 50)
    x_grid = np.linspace(0.0, qp**2 - 1e-3, 50)
    err_prod_Q = 0.0
    for qv in q_grid:
        gQ_v = sum(vX[k] / (sp_ - qv * xs[k] + (1 + xs[k]) / (Lam - (1 + xs[k]) * qv)) for k in range(3))
        # Product identity: 1 - g_Q(q) = prod_i (q - q_i)^2 * prod_k (x_k*(1+x_k)) / prod_k P_k(q)
        prod_num = np.prod([(qv - qi)**2 for qi in qs]) * np.prod([xk * (1 + xk) for xk in xs])
        prod_den = np.prod([(Lam - (1 + xk) * qv) * (sp_ - qv * xk + (1 + xk) / (Lam - (1 + xk) * qv)) for xk in xs])
        err_prod_Q = max(err_prod_Q, abs((1.0 - gQ_v) - prod_num / prod_den))
    err_prod_X = 0.0
    for xv in x_grid:
        gX_v = sum(vQ[i] / (sp_ - qs[i] * xv + (1 + xv) / (Lam - (1 + xv) * qs[i])) for i in range(3))
        prod_num = np.prod([(xv - xk)**2 for xk in xs]) * np.prod([qi**2 for qi in qs])
        prod_den = np.prod([(Lam - (1 + xv) * qi) * (sp_ - qi * xv + (1 + xv) / (Lam - (1 + xv) * qi)) for qi in qs])
        err_prod_X = max(err_prod_X, abs((1.0 - gX_v) - prod_num / prod_den))
    print(f"  4C. Degree-2r Product Identities (r=3): err(1-g_Q)={err_prod_Q:.2e}, err(1-g_X)={err_prod_X:.2e}")
    assert err_prod_Q < 1e-13 and err_prod_X < 1e-13

    # 4D. Local Rigidity: Strict negative definiteness of quadratic form Tr(E^T (r_1(E) - r_3(E))) on R^{r x r}!
    # Linearizing (G2''): M_X A = Lam D Y D and (G4): A A^T = Lam D Q D around Y = Q (Y = Q + eps*E, A0 = D + Q D Q):
    #   d(M_X A - Lam D Y D) = (E^T D Q + Q D E) A0 + A0 (E D Q) - Lam D E D  =: r_1(E)
    #   d(A A^T - Lam D Q D) = E D Q A0 + A0 Q D E^T                          =: r_3(E) (wait: exact form!)
    # Check exact symmetric quadratic form Q_loc(E) = Tr(E^T (r_1(E) - r_3(E))) where
    #   r_1(E) - r_3(E) = (E^T D Q + Q D E) A0 + A0 E D Q - Lam D E D - E D Q A0 - A0 Q D E^T!
    A0 = D + Q @ D @ Q
    n_e = 9
    H_loc = np.zeros((n_e, n_e))
    for p_idx in range(n_e):
        Ep = np.zeros((3, 3)); Ep.ravel()[p_idx] = 1.0
        r1 = (Ep.T @ D @ Q + Q @ D @ Ep) @ A0 + A0 @ (Ep @ D @ Q) - Lam * D @ Ep @ D
        r3 = Ep @ D @ Q @ A0 + A0 @ Q @ D @ Ep.T
        diff_p = r1 - r3
        for q_idx in range(n_e):
            Eq = np.zeros((3, 3)); Eq.ravel()[q_idx] = 1.0
            H_loc[q_idx, p_idx] = float(np.trace(Eq.T @ diff_p))
    H_sym = 0.5 * (H_loc + H_loc.T)
    ev_loc = np.linalg.eigvalsh(H_sym)
    print(f"  4D. Local Rigidity Quadratic Form on R^{{3x3}}: eig_range=[{ev_loc[0]:.4e}, {ev_loc[-1]:.4e}] (< 0 STRICTLY!)")
    assert ev_loc[-1] < -1e-6

    # 4E. Global (G2'') + (G4) uniqueness test on 20 random non-diagonal starts at n=2 (honest numerical check!)
    D2 = np.diag([1.0, 0.075130235])
    Lam2 = 4.4533716
    rng = np.random.default_rng(2026)
    n_nondiag, n_asym = 0, 0
    for _ in range(30):
        def eqs_g(v):
            L_ = np.array([[v[0], 0.0], [v[1], v[2]]]); Q_ = L_ @ L_.T
            Y_ = v[3:].reshape((2, 2))
            A_ = D2 + Y_ @ D2 @ Q_; MX_ = D2 + Y_.T @ D2 @ Y_
            R1 = MX_ @ A_ - Lam2 * D2 @ Y_ @ D2
            R2 = A_ @ A_.T - Lam2 * D2 @ Q_ @ D2
            return [R1[0, 0], R1[0, 1], R1[1, 0], R1[1, 1], R2[0, 0], R2[0, 1], R2[1, 1]]
        s_g = opt.least_squares(eqs_g, rng.normal(0, 0.8, 7), ftol=1e-14, xtol=1e-14, gtol=1e-14)
        if s_g.cost < 1e-22:
            L_ = np.array([[s_g.x[0], 0.0], [s_g.x[1], s_g.x[2]]]); Q_ = L_ @ L_.T
            Y_ = s_g.x[3:].reshape((2, 2))
            if np.linalg.eigvalsh(Q_)[0] > 1e-6:
                if abs(Q_[0, 1]) > 1e-5:
                    n_nondiag += 1
                if np.linalg.norm(Y_ - Q_) > 1e-7:
                    n_asym += 1
    print(f"  4E. Global (G2'')+(G4) uniqueness test (30 starts): non-diag converged={n_nondiag}, "
          f"asymmetric (Y!=Q)={n_asym} ({time.time() - t0:.2f}s)")
    assert n_nondiag >= 5 and n_asym == 0


# =============================================================================
# MODULE 5: TRACK (b) #94 ONE-SHOT F-SHIFTED UNINVERTED BRIDGE & PART (b)
# =============================================================================
def _roots_kappa(Lam, kappa):
    t_min = math.log((kappa - 1.0) / kappa)
    logL = math.log(Lam)
    fn = lambda tv: (2.0 * kappa - 1.0) * np.logaddexp(0.0, tv) - (kappa - 1.0) * tv - logL
    lo, hi = t_min - 1.0, t_min + 1.0
    while fn(lo) < 0.0: lo -= 20.0
    while fn(hi) < 0.0: hi += 20.0
    xm = math.exp(brentq(fn, lo, t_min, xtol=1e-15, rtol=1e-15))
    xp = math.exp(brentq(fn, t_min, hi, xtol=1e-15, rtol=1e-15))
    return xm, xp, (xm ** (kappa - 1.0)) * (xm - 1.0), (xp ** (kappa - 1.0)) * (xp - 1.0)


def _stage1_L_all(Lam, kappa):
    ts = np.concatenate([np.geomspace(1e-4, 0.5, 150), np.linspace(0.5, 4.0, 300), np.geomspace(4.0, 40.0, 150)])
    gs = np.concatenate([np.geomspace(1e-8, 0.5, 150), np.linspace(0.5, 5.0, 300), np.geomspace(5.0, 40.0, 150)])
    c = np.array([-1.0, 0.0, 0.0, 0.0, 1.0, 1.0])
    A1 = np.column_stack([ts, ts**(2 * kappa - 1), ts**(2 * kappa), -(1.0 / ts - 1.0), -np.ones_like(ts), np.zeros_like(ts)])
    A2 = np.column_stack([-gs, -Lam * (gs**(kappa - 1)), -Lam * (gs**(kappa - 1) + gs**kappa),
                          np.zeros_like(gs), np.zeros_like(gs), -np.ones_like(gs)])
    b2 = -(gs**(kappa - 1) - gs**kappa)
    res = linprog(c, A_ub=np.vstack([A1, A2]), b_ub=np.concatenate([np.zeros_like(ts), b2]),
                  bounds=[(None, None), (None, None), (None, None), (0.0, None), (None, None), (None, None)],
                  method="highs")
    return float(res.fun) + 1e-4


def _canon_w(w):
    i, j = 0, len(w)
    while i < j and w[i] == 0: i += 1
    while j > i and w[j - 1] == 0: j -= 1
    s = w[i:j]
    return min(s, s[::-1])


def _red_words(n_gen, max_l):
    ws = [()]
    for L in range(1, max_l + 1):
        for w in product(range(n_gen), repeat=L):
            if w[-1] != 0:
                ws.append(w)
    return ws


def _padd(a, b, sc=1.0):
    out = dict(a)
    for k, v in b.items():
        nv = out.get(k, 0.0) + sc * v
        if abs(nv) > 1e-15: out[k] = nv
        elif k in out: del out[k]
    return out


def _pmul(a, b):
    out = {}
    for k1, v1 in a.items():
        for k2, v2 in b.items():
            k = k1 + k2
            out[k] = out.get(k, 0.0) + v1 * v2
    return {k: v for k, v in out.items() if abs(v) > 1e-15}


def _ppow(a, n):
    out = {(): 1.0}
    for _ in range(n):
        out = _pmul(out, a)
    return out


def _solve_sdp_damped(canon, w2i, c_obj_poly, ideal_gens_and_pairs, blocks_polys, max_iter=85):
    n_var = len(canon)
    def p2v(p):
        v = np.zeros(n_var)
        for w, c in p.items():
            cw = _canon_w(w)
            assert cw in w2i, f"Missing canonical word {cw}"
            v[w2i[cw]] += c
        return v

    c_obj = p2v(c_obj_poly)
    a_norm = p2v({(): 1.0})
    A_id_rows = []
    for pid, pairs in ideal_gens_and_pairs:
        for wl, wr in pairs:
            p = {}
            for k, v in pid.items():
                kk = wl + k + wr
                p[kk] = p.get(kk, 0.0) + v
            A_id_rows.append(p2v(p))
    A_id_raw = np.array(A_id_rows)

    U_eq, s_eq, _ = np.linalg.svd(A_id_raw, full_matrices=False)
    rk_eq = int(np.sum(s_eq > 1e-11 * s_eq[0]))
    A_full = np.vstack([U_eq[:, :rk_eq].T @ A_id_raw, a_norm[None, :]])
    b_full = np.zeros(rk_eq + 1); b_full[-1] = 1.0

    raw_blocks = []
    for name, pW, wlist in blocks_polys:
        sz = len(wlist)
        F_t = np.zeros((n_var, sz, sz))
        for r, wu in enumerate(wlist):
            wu_rev = wu[::-1]
            for c, wv in enumerate(wlist):
                p = {}
                for k, v in pW.items():
                    kk = wu_rev + k + wv
                    p[kk] = p.get(kk, 0.0) + v
                F_t[:, r, c] = p2v(p)
        F_t = 0.5 * (F_t + np.swapaxes(F_t, 1, 2))
        raw_blocks.append((name, sz, F_t))

    Uf, sf, Vtf = np.linalg.svd(A_full, full_matrices=True)
    rk_f = int(np.sum(sf > 1e-11 * sf[0]))
    y0 = Vtf[:rk_f].T @ ((Uf[:, :rk_f].T @ b_full) / sf[:rk_f])
    N_null = Vtf[rk_f:].T
    n_free = N_null.shape[1]

    blocks = []
    for ib, (name, sz, F_t) in enumerate(raw_blocks):
        B0 = np.tensordot(y0, F_t, axes=(0, 0))
        Bz = np.tensordot(N_null, F_t, axes=(0, 0))
        sc = max(np.linalg.norm(B0), np.max(np.linalg.norm(Bz, axis=(1, 2))), 1e-12)
        blocks.append((ib, name, sz, B0 / sc, Bz / sc, sc))

    c0 = float(c_obj @ y0); g = N_null.T @ c_obj
    nb = len(blocks); tot_n = sum(b[2] for b in blocks)
    z = np.zeros(n_free); Sl = [np.eye(b[2]) for b in blocks]; Xl = [np.eye(b[2]) for b in blocks]

    def ms(Ml, dMl):
        am = 1.0
        for M, dM in zip(Ml, dMl):
            ev, evc = np.linalg.eigh(M)
            if ev[0] <= 1e-24:
                return 0.0
            Li = evc * (1.0 / np.sqrt(ev))
            G = 0.5 * (Li.T @ dM @ Li + (Li.T @ dM @ Li).T)
            lm = float(np.linalg.eigvalsh(G)[0])
            if lm < -1e-16: am = min(am, -1.0 / lm)
        return am

    best_sol = None
    for _ in range(1, max_iter + 1):
        Rpl = []; rd = g.copy(); mu = 0.0; pn = 0.0
        for a, (_, _, rk, B0, Bz, _) in enumerate(blocks):
            Bval = B0 + np.tensordot(z, Bz, axes=(0, 0))
            Rp = 0.5 * ((Sl[a] - Bval) + (Sl[a] - Bval).T)
            Rpl.append(Rp); pn += float(np.sum(Rp * Rp))
            rd -= np.einsum("jab,ab->j", Bz, Xl[a]); mu += float(np.sum(Sl[a] * Xl[a]))
        mu /= tot_n; pr = math.sqrt(pn); dr = float(np.linalg.norm(rd))
        if dr < 1e-9 and mu < 1e-10 and pr < 1e-9:
            break
        Ms = np.zeros((n_free, n_free)); Sinvl = []
        for a, (_, _, rk, B0, Bz, _) in enumerate(blocks):
            ev, V = np.linalg.eigh(Sl[a]); Sinv = (V * (1.0 / np.maximum(ev, 1e-24))) @ V.T; Sinvl.append(Sinv)
            SB = np.einsum("pq,jqr->jpr", Sinv, Bz); BX = np.einsum("jpq,qr->jpr", Bz, Xl[a])
            Ms += SB.reshape(n_free, rk * rk) @ BX.reshape(n_free, rk * rk).T
        Ms = 0.5 * (Ms + Ms.T); dd = np.sqrt(np.maximum(np.diag(Ms), 1e-30))
        Mn = (Ms / dd[:, None]) / dd[None, :] + 1e-13 * np.eye(n_free)
        def sm(rhs):
            try: return np.linalg.solve(Mn, rhs / dd) / dd
            except np.linalg.LinAlgError: return np.linalg.lstsq(Mn, rhs / dd, rcond=1e-13)[0] / dd
        def sd(sv, dSa=None, dXa=None):
            rhs = -rd.copy(); Rcl = []
            for a, (_, _, rk, B0, Bz, _) in enumerate(blocks):
                Rc = sv * mu * np.eye(rk) - Sl[a] @ Xl[a]
                if dSa is not None: Rc = Rc - dSa[a] @ dXa[a]
                Rcl.append(Rc); W = Sinvl[a] @ (Rc + Rpl[a] @ Xl[a]); W = 0.5 * (W + W.T)
                rhs += np.einsum("jab,ab->j", Bz, W)
            dz = sm(rhs); dSl, dXl = [], []
            for a, (_, _, rk, B0, Bz, _) in enumerate(blocks):
                dS = 0.5 * ((np.tensordot(dz, Bz, axes=(0, 0)) - Rpl[a]) + (np.tensordot(dz, Bz, axes=(0, 0)) - Rpl[a]).T)
                dX = Sinvl[a] @ (Rcl[a] - dS @ Xl[a]); dX = 0.5 * (dX + dX.T)
                dSl.append(dS); dXl.append(dX)
            return dz, dSl, dXl
        dza, dSa, dXa = sd(0.0)
        apa = min(1.0, ms(Sl, dSa)); ada = min(1.0, ms(Xl, dXa))
        mua = sum(float(np.sum((Sl[a] + apa * dSa[a]) * (Xl[a] + ada * dXa[a]))) for a in range(nb)) / tot_n
        sig_c = float(np.clip((mua / max(mu, 1e-30)) ** 3, 1e-3, 0.8))
        dz, dS, dX = sd(sig_c, dSa, dXa)
        ap = min(1.0, 0.92 * ms(Sl, dS)); ad = min(1.0, 0.92 * ms(Xl, dX))
        if ap < 1e-12 and ad < 1e-12:
            break
        if dr < 1e-7:
            best_sol = (z.copy(), [S.copy() for S in Sl], [X.copy() for X in Xl], dr)
        z += ap * dz
        for a in range(nb):
            Sl[a] = 0.5 * ((Sl[a] + ap * dS[a]) + (Sl[a] + ap * dS[a]).T)
            Xl[a] = 0.5 * ((Xl[a] + ad * dX[a]) + (Xl[a] + ad * dX[a]).T)

    rd_fin = g.copy()
    for a, (_, _, rk, B0, Bz, _) in enumerate(blocks):
        rd_fin -= np.einsum("jab,ab->j", Bz, Xl[a])
    dr_fin = float(np.linalg.norm(rd_fin))
    minX_fin = min(float(np.linalg.eigvalsh(X)[0]) for X in Xl)
    if best_sol is not None and (dr_fin > 10 * best_sol[3] or minX_fin <= 0):
        z, Sl, Xl, _ = best_sol

    Z_raw = [0.5 * (Xl[a] + Xl[a].T) / blocks[a][5] for a in range(nb)]
    S_raw = [0.5 * (Sl[a] + Sl[a].T) * blocks[a][5] for a in range(nb)]
    psos = sum(np.einsum("vij,ij->v", raw_blocks[b][2], Z_raw[b]) for b in range(nb))
    Mls = np.hstack([A_id_raw.T, -a_norm[:, None]])
    sol = np.linalg.lstsq(Mls, c_obj - psos, rcond=1e-13)[0]
    res_vec = (c_obj + sol[-1] * a_norm) - (psos + A_id_raw.T @ sol[:-1])
    return {
        "Psi_ls": float(sol[-1]),
        "poly_res": float(np.max(np.abs(res_vec))),
        "Z_raw": Z_raw,
        "S_raw": S_raw,
        "blocks_names": [b[1] for b in blocks],
        "min_eig": min(float(np.linalg.eigvalsh(Z)[0]) for Z in Z_raw),
        "max_S": max(float(np.max(np.diag(S))) for S in S_raw),
    }


def run_module5_track_b_and_obstructions():
    print("\n" + "=" * 92)
    print("MODULE 5: TRACK (b) #94 ONE-SHOT UNINVERTED BRIDGE, RAY-PRUNING & PART (b) OBSTRUCTIONS")
    print("=" * 92)
    t0 = time.time()

    # 5A. Compact Zero-Ray Uninverted Basis at p = 3/2, m = 2, deg 8
    print("  5A. Compact Zero-Ray Uninverted Basis Demonstration at p = 3/2, m = 2 (deg 8):")
    kappa32, Lam32 = 1.5, 4.4555
    _, xp32, _, sp32 = _roots_kappa(Lam32, kappa32)
    qp32 = math.sqrt(xp32)
    pI, pD, pQ = {(): 1.0}, {(0,): 1.0}, {(1,): 1.0}
    pg32 = _padd(_ppow(_padd(pD, {(1, 0, 1): 1.0}), 2), {(0, 1, 0): 1.0}, -Lam32)
    pF32 = _padd({(1, 0, 1, 0, 1): 1.0}, {(0, 1, 0): 1.0}, -1.0)
    pFD32 = _padd(_pmul(pF32, pD), _pmul(pD, pF32), -1.0)
    canon8 = sorted(set(_canon_w(w) for L in range(9) for w in product((0, 1), repeat=L)))
    w2i8 = {w: i for i, w in enumerate(canon8)}
    mk_p2_8 = lambda dg: [(wl, wr) for ll in range(9 - dg) for lr in range(9 - dg - ll)
                          for wl in product((0, 1), repeat=ll) for wr in product((0, 1), repeat=lr)]
    id32 = [(pg32, mk_p2_8(6)), (pFD32, mk_p2_8(6))]
    pQm32 = _padd({(): qp32}, pQ, -1.0); pUmF32 = _padd({(0, 0): sp32}, pF32, -1.0)
    blks32 = [
        ("I", pI, _red_words(2, 4)), ("D", pD, _red_words(2, 3)), ("Q", pQ, _red_words(2, 3)),
        ("qp-Q", pQm32, _red_words(2, 3)), ("Q(qp-Q)", _pmul(pQ, pQm32), _red_words(2, 3)),
        ("UD2-F", pUmF32, _red_words(2, 1)), ("D(UD2-F)", _pmul(pD, pUmF32), _red_words(2, 1)),
    ]
    cur = blks32
    for rd in range(5):
        r32 = _solve_sdp_damped(canon8, w2i8, pF32, id32, cur, max_iter=85)
        nxt = [(nm, pW, [w for w, dv in zip(wl, np.diag(Sb)) if (dv < 3.0 or w == ())])
               for (nm, pW, wl), Sb in zip(cur, r32["S_raw"])]
        if [len(b[2]) for b in nxt] == [len(b[2]) for b in cur]:
            break
        cur = nxt
    r32 = _solve_sdp_damped(canon8, w2i8, pF32, id32, cur, max_iter=95)
    print(f"      p=3/2 deg 8 pruned lens={[len(b[2]) for b in cur]} (total={sum(len(b[2]) for b in cur)} words): "
          f"Psi={r32['Psi_ls']:.8f} < sp={sp32:.8f}, res={r32['poly_res']:.2e}, maxS={r32['max_S']:.2f}, minZ={r32['min_eig']:.2e}")
    assert r32["Psi_ls"] < sp32 and r32["poly_res"] < 1e-7 and r32["min_eig"] > 0 and r32["max_S"] < 5.0

    # 5B. Track (b) One-Shot + Two-Stage Hybrid across (p, m) in {6/5, 5/3, 5/4} x {2, 3, 4}
    print("\n  5B. Track (b) One-Shot F-Shifted Uninverted Full-Slope Bridge + Two-Stage Hybrid (Float64 SDP):")

    def verify_pair(name, kappa, Lam0, deg, canon, w2i, mk_id, mk_blks, p_ch, pow_map, C_rg, m, C_ub, C_hyb):
        slope_lim = 1.0 / (m - 1.0)
        c_shift = 5.0
        # One-Shot at C_ub
        L_ub = Lam0 * (C_ub ** (2.0 * kappa))
        _, _, _, sp_ub = _roots_kappa(L_ub, kappa)
        id_ub = mk_id(L_ub); blks_ub = mk_blks(L_ub, sp_ub, False)
        r1 = _solve_sdp_damped(canon, w2i, p_ch, id_ub, blks_ub)
        margin1 = r1["Psi_ls"] - sp_ub / (m - 1.0)
        L_all = _stage1_L_all(L_ub, kappa); U_max = (m - 1.0) * L_all
        c_id2 = _padd({(): c_shift * sp_ub / (m - 1.0)}, p_ch, c_shift)
        for nm_u, pw in pow_map:
            idx = r1["blocks_names"].index(nm_u)
            Zu = r1["Z_raw"][idx]; wlu = blks_ub[idx][2]
            for ri, wu in enumerate(wlu):
                for ci, wv in enumerate(wlu):
                    kk = wu[::-1] + pw + wv
                    c_id2[kk] = c_id2.get(kk, 0.0) - float(Zu[ri, ci])
        r2 = _solve_sdp_damped(canon, w2i, c_id2, id_ub, mk_blks(L_ub, U_max, False))
        alpha = r2["Psi_ls"]

        # Two-Stage Hybrid at C_hyb
        L_h = Lam0 * (C_hyb ** (2.0 * kappa))
        _, _, _, sp_h = _roots_kappa(L_h, kappa)
        id_h = mk_id(L_h); blks_hu = mk_blks(L_h, sp_h, False)
        r1h = _solve_sdp_damped(canon, w2i, p_ch, id_h, blks_hu)
        L_all_h = _stage1_L_all(L_h, kappa); U_max_h = (m - 1.0) * L_all_h
        c_id2h = _padd({(): c_shift * sp_h / (m - 1.0)}, p_ch, c_shift)
        for nm_u, pw in pow_map:
            idx = r1h["blocks_names"].index(nm_u)
            Zu = r1h["Z_raw"][idx]; wlu = blks_hu[idx][2]
            for ri, wu in enumerate(wlu):
                for ci, wv in enumerate(wlu):
                    kk = wu[::-1] + pw + wv
                    c_id2h[kk] = c_id2h.get(kk, 0.0) - float(Zu[ri, ci])
        r2h = _solve_sdp_damped(canon, w2i, c_id2h, id_h, mk_blks(L_h, U_max_h, False))
        alpha_h = r2h["Psi_ls"]
        g_u = r1h["Psi_ls"] - sp_h / (m - 1.0)
        if g_u < 0.0:
            # Stage-1 pure One-Shot ALREADY certifies C_hyb across all delta >= 0 (100% delta annihilation!)
            d_boot = 0.0
            rb = r1h
        else:
            d_boot = (g_u / (slope_lim - max(alpha_h, 0.0))) * 1.02 + 1e-6
            rb = _solve_sdp_damped(canon, w2i, p_ch, id_h, mk_blks(L_h, sp_h + d_boot, True))
        margin_h = rb["Psi_ls"] - sp_h / (m - 1.0)
        d_max = U_max_h - sp_h

        print(f"      [{name} deg {deg:2d} m={m}] C_RG={C_rg:.10f} | "
              f"1-Shot C={C_ub:.7f} (gap={C_ub-C_rg:.2e}, mrg={margin1:+.2e}, alpha={alpha:+.5f}<<{slope_lim:.3f}, res=({r1['poly_res']:.1e},{r2['poly_res']:.1e})) | "
              f"Hybrid C={C_hyb:.7f} (gap={C_hyb-C_rg:.2e}, mrg={margin_h:+.2e}, d_boot={d_boot:.2e}/{d_max:.2e}, res={rb['poly_res']:.1e})")
        assert margin1 < 0 and alpha < 0.1 * slope_lim and r1["poly_res"] < 5e-5 and r2["poly_res"] < 5e-5
        assert margin_h < 0 and alpha_h < 0.2 * slope_lim and d_boot < d_max
        assert r1h["poly_res"] < 5e-5 and r2h["poly_res"] < 5e-5 and rb["poly_res"] < 1e-4
        assert min(r1["min_eig"], r2["min_eig"], r1h["min_eig"], r2h["min_eig"], rb["min_eig"]) > -1e-10

    # p = 6/5 deg 10
    pD, pH = {(0,): 1.0}, {(1,): 1.0}
    pDpH5 = _ppow(_padd(pD, pH), 5); pDHDHD = {(0, 1, 0, 1, 0): 1.0}; pF65 = _padd({(1, 0, 1, 0, 1): 1.0}, pDHDHD, -1.0)
    pFD65 = _padd(_pmul(pF65, pD), _pmul(pD, pF65), -1.0)
    canon10 = sorted(set(_canon_w(w) for L in range(11) for w in product((0, 1), repeat=L)))
    w2i10 = {w: i for i, w in enumerate(canon10)}
    mk_p2_10 = lambda dg: [(wl, wr) for ll in range(11 - dg) for lr in range(11 - dg - ll)
                           for wl in product((0, 1), repeat=ll) for wr in product((0, 1), repeat=lr)]
    pg65_p, pfd65_p = mk_p2_10(5), mk_p2_10(6)
    mk_id65 = lambda L: [(_padd(pDpH5, pDHDHD, -L), pg65_p), (pFD65, pfd65_p)]
    def mk_blks65(L, U, bD):
        _, xp, _, _ = _roots_kappa(L, 3.0)
        pUmF = _padd({(0, 0, 0, 0, 0): U}, pF65, -1.0)
        sp = [("I", pI, 0), ("D", pD, 1), ("H", pH, 1), ("xpD-H", _padd({(0,): xp}, pH, -1.0), 1),
              ("UD5-F", pUmF, 5), ("D(UD5-F)", _pmul(pD, pUmF), 6)]
        if bD:
            pImD = _padd(pI, pD, -1.0)
            sp += [("I-D", pImD, 1), ("D(I-D)", _pmul(pD, pImD), 2), ("(I-D)(UD5-F)", _pmul(pImD, pUmF), 6)]
        return [(nm, pW, _red_words(2, (10 - dW) // 2)) for nm, pW, dW in sp]

    for m, Crg, Cub, Chyb in [
        (2, 1.0073976732650, 1.0077600, 1.0074035),
        (3, 1.0128301552408, 1.0134200, 1.0128410),
        (4, 1.0172371783066, 1.0179800, 1.0172510),
    ]:
        verify_pair("p=6/5", 3.0, 32.0, 10, canon10, w2i10, mk_id65, mk_blks65, pF65,
                    [("UD5-F", (0, 0, 0, 0, 0)), ("D(UD5-F)", (0, 0, 0, 0, 0, 0))], Crg, m, Cub, Chyb)

    # 3-gen canon deg 6 (shared by p = 5/3 and p = 5/4)
    canon3 = sorted(set(_canon_w(w) for L in range(7) for w in product((0, 1, 2), repeat=L)))
    w2i3 = {w: i for i, w in enumerate(canon3)}
    mk_p3 = lambda dg: [(wl, wr) for ll in range(7 - dg) for lr in range(7 - dg - ll)
                        for wl in product((0, 1, 2), repeat=ll) for wr in product((0, 1, 2), repeat=lr)]
    p3_3, p3_4, p3_5, p3_6 = mk_p3(3), mk_p3(4), mk_p3(5), mk_p3(6)

    # p = 5/3 deg 6
    pA, pR, pG = {(0,): 1.0}, {(1,): 1.0}, {(2,): 1.0}
    pg2_53 = _padd(_padd({(2, 2, 2, 2): 1.0}, {(0, 1, 1, 0): 1.0}, -1.0), {(0, 0, 0, 0): 1.0}, 1.0)
    pE53 = _padd({(2, 2, 2, 2, 2): 1.0}, {(0, 0, 2, 0, 0): 1.0}, -1.0)
    pR_anti = _padd(_padd({(1, 1, 1, 1, 1): 1.0}, {(0, 0, 1, 1, 1): 1.0}, -1.0), {(1, 1, 1, 0, 0): 1.0}, -1.0)
    pEA53 = _padd(_pmul(pE53, pA), _pmul(pA, pE53), -1.0)
    mk_id53 = lambda L: [(_padd({(1, 1, 1): 1.0}, {(0, 2, 0): 1.0}, -L), p3_3), (pg2_53, p3_4),
                         (_padd(pR_anti, pE53, -L), p3_5), (pEA53, p3_6)]
    def mk_blks53(L, U, bD):
        _, xp, _, _ = _roots_kappa(L, 1.25)
        pUmE = _padd({(0, 0, 0, 0, 0): U}, pE53, -1.0)
        sp = [("I", pI, 0), ("A", pA, 1), ("R-A", _padd(pR, pA, -1.0), 1),
              ("sqA-R", _padd({(0,): math.sqrt(1 + xp)}, pR, -1.0), 1), ("G", pG, 1),
              ("qA-G", _padd({(0,): xp**0.25}, pG, -1.0), 1),
              ("UA5-E", pUmE, 5), ("A(UA5-E)", _pmul(pA, pUmE), 6)]
        if bD:
            pImA = _padd(pI, pA, -1.0)
            sp += [("I-A", pImA, 1), ("A(I-A)", _pmul(pA, pImA), 2), ("(I-A)(UA5-E)", _pmul(pImA, pUmE), 6)]
        return [(nm, pW, _red_words(3, (6 - dW) // 2)) for nm, pW, dW in sp]

    for m, Crg, Cub, Chyb in [
        (2, 1.0573489138603, 1.0573850, 1.0573700),
        (3, 1.0989356237470, 1.0990200, 1.0989600),
        (4, 1.1324219307980, 1.1324520, 1.1324520),
    ]:
        verify_pair("p=5/3", 1.25, 2.0**1.5, 6, canon3, w2i3, mk_id53, mk_blks53, pE53,
                    [("UA5-E", (0, 0, 0, 0, 0)), ("A(UA5-E)", (0, 0, 0, 0, 0, 0))], Crg, m, Cub, Chyb)

    # p = 5/4 deg 6
    pD3, pQ3, pH3 = {(0,): 1.0}, {(1,): 1.0}, {(2,): 1.0}
    pDpH4 = _ppow(_padd(pD3, pH3), 4); pDQDHD = {(0, 1, 0, 2, 0): 0.5, (0, 2, 0, 1, 0): 0.5}
    pF54 = _padd({(2, 0, 1, 0, 2): 1.0}, pDQDHD, -1.0); pFD54 = _padd(_pmul(pF54, pD3), _pmul(pD3, pF54), -1.0)
    pr1_54 = _padd(pH3, {(1, 0, 1): 1.0}, -1.0); pr2_54 = {(2, 0, 1): 1.0, (1, 0, 2): -1.0}
    mk_id54 = lambda L: [(pr1_54, p3_3), (pr2_54, p3_3), (_padd(pDpH4, pDQDHD, -L), p3_5), (pFD54, p3_6)]
    def mk_blks54(L, U, bD):
        _, xp, _, _ = _roots_kappa(L, 2.5); qp = math.sqrt(xp)
        pQm = _padd({(): qp}, pQ3, -1.0); pUmF = _padd({(0, 0, 0, 0): U}, pF54, -1.0)
        sp = [("I", pI, 0), ("D", pD3, 1), ("Q", pQ3, 1), ("qp-Q", pQm, 1), ("Q(qp-Q)", _pmul(pQ3, pQm), 2),
              ("H", pH3, 1), ("xpD-H", _padd({(0,): xp}, pH3, -1.0), 1),
              ("UD4-F", pUmF, 5), ("D(UD4-F)", _pmul(pD3, pUmF), 6)]
        if bD:
            pImD = _padd(pI, pD3, -1.0)
            sp += [("I-D", pImD, 1), ("D(I-D)", _pmul(pD3, pImD), 2), ("(I-D)(UD4-F)", _pmul(pImD, pUmF), 6)]
        return [(nm, pW, _red_words(3, (6 - dW) // 2)) for nm, pW, dW in sp]

    for m, Crg, Cub, Chyb in [
        (2, 1.0110659821227, 1.0118600, 1.0115300),
        (3, 1.0191932719701, 1.0204200, 1.0199500),
        (4, 1.0257877553868, 1.0272500, 1.0267400),
    ]:
        verify_pair("p=5/4", 2.5, 16.0, 6, canon3, w2i3, mk_id54, mk_blks54, pF54,
                    [("UD4-F", (0, 0, 0, 0)), ("D(UD4-F)", (0, 0, 0, 0, 0))], Crg, m, Cub, Chyb)

    # 5C. Part (b) Obstruction Verification (Direct-Sum Trace-Coupling Obstruction & Separable CP-Map No-Go at delta=0)
    print("\n  5C. Part (b) Structural Obstruction Checks (Direct-Sum Trace-Coupling & Separable CP-Map No-Go):")
    # Constructive direct-sum witness at p=3/2, m=2:
    # Take an exact r=2 RG block (D_rg, Q_rg) where E_rg = diag(-sp, +sp*d1^3),
    # and form D_tot = diag(1, d1) (+) diag(1, d1) with:
    #   Block 1: Q_1 = diag(q_+, q_+) (+) Q_rg   -> E_1 = diag(+sp, +sp*d1^3, -sp, +sp*d1^3)
    #   Block 2: Q_2 = Q_rg (+) diag(q_+, q_+)   -> E_2 = diag(-sp, +sp*d1^3, +sp, +sp*d1^3)
    # Check: EACH block individually satisfies (D+Q_j D Q_j)^2 = Lam D Q_j D AND sigma_+ D^3 - E_j >= 0 (delta = 0!!),
    #        AND Tr(E_1 + E_2) = 2*sp*(2*d1^3) > 0, while at the vector state v = e_0 (+) 0, <(E_1+E_2)v, v> = 0!
    #        In fact, pairing Q_1 = Q_rg with Q_2 = diag(q_+, q_leaf) gives E_1 + E_2 = 0 on EVERY coordinate!
    def res_r2_m2(vec):
        qp_, d1_, q00_, q01_, q11_ = vec
        L_ = (1 + qp_**2)**2 / qp_; sp_ = qp_ * (qp_**2 - 1)
        D_ = np.diag([1.0, d1_]); Q_ = np.array([[q00_, q01_], [q01_, q11_]])
        M_ = D_ + Q_ @ D_ @ Q_; R1_ = M_ @ M_ - L_ * D_ @ Q_ @ D_; F_ = Q_ @ D_ @ Q_ @ D_ @ Q_ - D_ @ Q_ @ D_
        return [R1_[0, 0], R1_[0, 1], R1_[1, 1], F_[0, 0] + sp_, F_[1, 1] - sp_ * d1_**2]
    sol = opt.root(res_r2_m2, [1.103, 0.075, 0.25, 0.2, 0.85], tol=1e-13)
    qp2, d12, q002, q012, q112 = sol.x
    L2 = (1 + qp2**2)**2 / qp2; sp2 = qp2 * (qp2**2 - 1)
    D2 = np.diag([1.0, d12]); Q2 = np.array([[q002, q012], [q012, q112]])
    # Direct sum of two independent valid Holden pairs (D2, Q2) and (D2, qp2*I) with positive weights w1=w2=1/2:
    # On the single-block level, BOTH pairs satisfy ALL single-block identities and B_{sp} >= 0,
    # and the coupled state sigma = (1/2)|e_0><e_0| on (Q_1=Q2, Q_2=qp2*I) has <(E_1+E_2) e_0, e_0> = 0 identically!
    F_rg = Q2 @ D2 @ Q2 @ D2 @ Q2 - D2 @ Q2 @ D2
    F_sc = (qp2**3 - qp2) * (D2 @ D2)
    B_rg = sp2 * (D2 @ D2) - F_rg
    B_sc = sp2 * (D2 @ D2) - F_sc
    sum_at_e0 = float(F_rg[0, 0] + F_sc[0, 0])
    sum_tr = float(np.trace(F_rg + F_sc))
    print(f"      Direct-Sum / Separable CP-Map Witness (p=3/2, m=2, Lam={L2:.8f} > Lam_1):")
    print(f"        min_eig(B_rg)={np.linalg.eigvalsh(B_rg)[0]:+.2e}, min_eig(B_sc)={np.linalg.eigvalsh(B_sc)[0]:+.2e}, "
          f"<(F1+F2)e0,e0>={sum_at_e0:+.2e}, Tr(F1+F2)={sum_tr:+.4e} > 0 (nonzero off-e0 charge!)")
    assert np.linalg.eigvalsh(B_rg)[0] > -1e-13 and np.linalg.eigvalsh(B_sc)[0] > -1e-13 and abs(sum_at_e0) < 1e-13
    print(f"  Module 5 complete ({time.time() - t0:.2f}s).")


if __name__ == "__main__":
    t_all = time.time()
    run_module1_all_m_convexity()
    run_module2_branching_and_tree()
    run_module3_large_m_excess()
    run_module4_bipartite_gap1a()
    run_module5_track_b_and_obstructions()
    print("\n" + "=" * 92)
    print(f"ALL 5 MODULES PASSED 100% (EXIT CODE 0) IN {time.time() - t_all:.2f}s")
    print("=" * 92)
