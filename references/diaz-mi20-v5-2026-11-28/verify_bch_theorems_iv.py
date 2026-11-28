#!/usr/bin/env python3
"""
verify_bch_theorems_iv.py
=========================
Author:      Marcio Díaz (Space Research AI, https://spaceresearch.ai, marcio.diaz@gmail.com)
Date:        November 28, 2026
Purpose:     100% standalone, zero-numpy, zero-scipy, zero-SDP, pure-`mpmath` (35-digit
             `mpmath.iv` rigorous outward-rounded interval arithmetic) independent verifier
             for both all-dimension (n <= infinity) Version 5 Theorem 21 BCH operator theorems:

               1. Theorem 21(c) — New Unconditional Analytic Record on K_2^{BCH}:
                  Proves K_2^{BCH} < 0.3145 across ALL dimensions n <= infinity and ALL
                  K_2 in [0.3145, K_2^{Thm10}] (348.4x larger breach of V4's Lambert-W
                  barrier K_2^{Thm10} = 0.317235793549... than Theorem 19(b)'s Furuta-free
                  0.31722794!), using ONLY 17 explicit rational dual weights (hardcoded below —
                  zero LP solver trusted!), Furuta domination U >= -t_+ I, the 5-line Global
                  Flux Box ||A||_op <= 2/e, the 7-line Smooth Operator Weight
                  D_b = sqrt((M - b)_+ / (M + t_+)), the exact Sylvester integral split, and
                  the 3-line Young Term-A inequality. Verified with ZERO grid gaps on ALL of
                  [-t_+^{hi}, +infty) by mpmath.iv branch-and-bound + exact breakpoint checks
                  + 1-line analytic tail bound on [8, +infty).

               2. Theorem 21(b) — Universal BCH A Priori Operator Norm Bound:
                  Proves ||V||_op <= 13.412 UNIFORMLY for ALL K_2 in [0, 0.3172358] (all
                  t_+ in [0, 0.278465]) and ALL finite-dim (or bounded self-adjoint) PSD
                  solutions V >= 0 of T_tilde[V^2] = 2(1+t_+) V! Also certifies
                  ||V||_op <= 11.390 at K_2 = 0.3172358 and ||V||_op <= 10.619 at K_2^tree(inf).

Invocation:
    uv run --with mpmath python3 verify_bch_theorems_iv.py
"""
import time
import mpmath as mp
from mpmath import iv

mp.mp.dps = 35
iv.dps = 35


def main():
    t0 = time.time()

    # ==========================================================================
    # PART 1: STANDALONE 35-DIGIT MPMATH.IV CERTIFICATION OF THEOREM 21(c)
    # ==========================================================================
    print("=" * 78)
    print("PART 1: STANDALONE PURE-MPMATH.IV VERIFICATION OF THEOREM 21(c) (K_2^BCH < 0.3145)")
    print("=" * 78)

    K2_LO = mp.mpf("0.3145")
    K2_HI = mp.mpf("0.3172358")

    tp_lo_iv = iv.sqrt(iv.mpf(1) + iv.mpf(2) * iv.mpf(K2_LO)) - iv.mpf(1)
    tp_hi_iv = iv.sqrt(iv.mpf(1) + iv.mpf(2) * iv.mpf(K2_HI)) - iv.mpf(1)
    sig_lo_iv = tp_lo_iv * iv.exp(tp_lo_iv)
    inv_e_iv = iv.exp(-iv.mpf(1))

    # Verify K2_HI strictly encloses V4 Theorem 10 (Lambert-W bound):
    W_lam = mp.lambertw(mp.exp(-1))
    K2_Thm10 = (W_lam**2 + 2 * W_lam) / 2
    assert K2_HI > K2_Thm10, "K2_HI must strictly exceed V4 Thm 10!"
    print(f"  K2_HI = {K2_HI} > K2_Thm10 = {mp.nstr(K2_Thm10, 15)} [OK]")

    # 17 explicit rational (lam, (a, b, c_ref, bf, es, er, eL, eta)) tuples:
    CERT_DATA = [
        ("0.000259",  ("0.76", "1.24", "0.97", "0.45", "0.10", "0.10", "0.10", "6")),
        ("0.0000336", ("0.74", "1.26", "0.97", "0.45", "0.10", "0.10", "0.10", "6")),
        ("0.0000508", ("0.72", "1.28", "0.97", "0.45", "0.10", "0.10", "0.10", "6")),
        ("0.0000145", ("0.72", "1.28", "1.00", "0.45", "0.10", "0.10", "0.10", "6")),
        ("0.0001795", ("0.70", "1.30", "1.00", "0.45", "0.10", "0.10", "0.10", "6")),
        ("0.0000474", ("0.00", "1.32", "0.97", "0.45", "0.25", "0.10", "0.10", "6")),
        ("0.0000484", ("0.66", "1.34", "0.97", "0.45", "0.25", "0.10", "0.10", "6")),
        ("0.0000494", ("0.64", "1.36", "0.97", "0.45", "0.25", "0.10", "0.10", "6")),
        ("0.0000516", ("0.62", "1.38", "0.97", "0.45", "0.25", "0.10", "0.10", "6")),
        ("0.0001425", ("0.60", "1.40", "0.97", "0.45", "0.25", "0.10", "0.10", "6")),
        ("0.0000159", ("0.60", "1.40", "1.00", "0.45", "0.25", "0.10", "0.10", "6")),
        ("0.0000737", ("0.56", "1.44", "1.00", "0.45", "0.25", "0.10", "0.10", "10")),
        ("0.0000606", ("0.54", "1.46", "1.00", "0.45", "0.25", "0.10", "0.10", "10")),
        ("0.0000562", ("0.52", "1.48", "1.00", "0.45", "0.25", "0.10", "0.10", "15")),
        ("0.0001912", ("0.50", "1.50", "0.97", "0.45", "0.45", "0.10", "0.10", "15")),
        ("0.0022241", ("0.50", "1.50", "1.00", "0.45", "0.45", "0.10", "0.10", "15")),
        ("0.0000204", ("0.55", "1.50", "1.00", "0.45", "0.25", "0.10", "0.10", "15")),
    ]

    cert_iv = []
    breaks = {-tp_hi_iv.b}
    for lam_s, cfg in CERT_DATA:
        lam_iv = iv.mpf(lam_s)
        assert lam_iv.a > 0
        a_m, b_m = mp.mpf(cfg[0]), mp.mpf(cfg[1])
        a, b, c_ref, bf, es, er, eL, eta = [iv.mpf(x) for x in cfg]
        lb = iv.exp(-b)
        ec = iv.exp(-c_ref)
        M_R = iv.mpf("0.5") * (b + tp_hi_iv)
        beta = bf * iv.mpf(2) * lb
        cB = (iv.mpf(4) * inv_e_iv**2) / beta
        coeff_r_LB = iv.mpf(4) - iv.mpf(2) * (b - tp_hi_iv) * (iv.mpf(1) - eL)
        # Verify ALL positivity/domain preconditions strictly in interval arithmetic:
        assert a_m >= 0 and b_m > a_m
        assert (b - tp_hi_iv).a > 0
        assert (iv.mpf(2) + tp_lo_iv - b).a > 0
        assert (iv.mpf(2) * lb - beta).a > 0
        assert (iv.mpf(2) * ec - beta).a > 0
        assert coeff_r_LB.a > 0
        A_r_LB = coeff_r_LB / (iv.mpf(4) * ec * (iv.mpf(1) - er))
        a0 = (iv.mpf(4) * inv_e_iv**2) * (iv.mpf(1) + iv.mpf(1) / eta) / (ec**2)
        a1 = (iv.mpf(4) * inv_e_iv**2) * (iv.mpf(1) + eta)
        cert_iv.append(dict(
            lam=lam_iv, a=a, b=b, a_m=a_m, b_m=b_m, c_ref=c_ref, ec=ec,
            M_R=M_R, beta=beta, cB=cB, A_r_LB=A_r_LB, es=es, er=er, eL=eL, a0=a0, a1=a1,
        ))
        breaks.add(a_m)
        breaks.add(b_m)

    breaks.add(mp.mpf("1.0"))
    b_max_m = max(d["b_m"] for d in cert_iv)
    sorted_breaks = sorted(breaks)

    def tanh_iv(x):
        e2 = iv.exp(-iv.mpf(2) * x)
        return (iv.mpf(1) - e2) / (iv.mpf(1) + e2)

    def dtanh_iv(u_iv):
        """Exact enclosure of 1 - tanh(u)/u (even, strictly increasing on [0, +infty))."""
        ua, ub = u_iv.a, u_iv.b
        if ua <= 0 <= ub:
            abs_lo = mp.mpf(0)
            abs_hi = max(-ua, ub)
        else:
            abs_lo = min(abs(ua), abs(ub))
            abs_hi = max(abs(ua), abs(ub))

        def f_pt(x_mp):
            if x_mp == 0:
                return iv.mpf(0)
            if x_mp < mp.mpf("1e-5"):
                x = iv.mpf(x_mp)
                return iv.mpf([(x**2 / 3 - 2 * x**4 / 15).a, (x**2 / 3).b])
            x = iv.mpf(x_mp)
            return iv.mpf(1) - tanh_iv(x) / x

        return iv.mpf([f_pt(abs_lo).a, f_pt(abs_hi).b])

    def eval_F_iv(m_lo, m_hi):
        m = iv.mpf([m_lo, m_hi])
        mid = mp.mpf("0.5") * (m_lo + m_hi)
        em = iv.exp(-m)
        if m_hi <= 1:
            me_lo = (iv.mpf(m_lo) * iv.exp(-iv.mpf(m_lo))).a
            me_hi = (iv.mpf(m_hi) * iv.exp(-iv.mpf(m_hi))).b
        elif m_lo >= 1:
            me_lo = (iv.mpf(m_hi) * iv.exp(-iv.mpf(m_hi))).a
            me_hi = (iv.mpf(m_lo) * iv.exp(-iv.mpf(m_lo))).b
        else:
            me_lo = min((iv.mpf(m_lo) * iv.exp(-iv.mpf(m_lo))).a, (iv.mpf(m_hi) * iv.exp(-iv.mpf(m_hi))).a)
            me_hi = inv_e_iv.b
        me = iv.mpf([me_lo, me_hi])
        g = iv.mpf([max(mp.mpf(0), (inv_e_iv - me).a), max(mp.mpf(0), (inv_e_iv - me).b)])

        F = me
        for d in cert_iv:
            is_in = (mid >= d["a_m"]) and (mid <= d["b_m"])
            if is_in:
                u = iv.mpf("0.5") * (m - d["c_ref"])
                dt = dtanh_iv(u)
                TermB = d["cB"] * (
                    iv.mpf(1) / (iv.mpf(2) * em - d["beta"])
                    + iv.mpf(1) / (iv.mpf(2) * d["ec"] - d["beta"])
                    - iv.mpf(2) * (iv.mpf(1) - dt) / (em + d["ec"] - d["beta"])
                )
                m_tp = m + tp_lo_iv
                assert m_tp.a >= 0
                Psi_k = (
                    (iv.mpf(1) + iv.mpf(1) / d["es"]) * TermB
                    + d["A_r_LB"] * (d["M_R"] / (d["ec"] * d["er"])) * (em - d["ec"])**2
                    + iv.mpf(4) * (d["b"] - tp_lo_iv) * (iv.mpf(1) / d["eL"] - iv.mpf(1)) * d["M_R"] * dt
                    - (iv.mpf(2) + tp_lo_iv - d["b"]) * m_tp
                )
            else:
                if m_hi <= d["b_m"]:
                    Dc2 = iv.mpf(0)
                else:
                    dc_lo = max(mp.mpf(0), ((iv.mpf(m_lo) - d["b"]) / (iv.mpf(m_lo) + tp_lo_iv)).a)
                    dc_hi = max(mp.mpf(0), ((iv.mpf(m_hi) - d["b"]) / (iv.mpf(m_hi) + tp_lo_iv)).b)
                    Dc2 = iv.mpf([dc_lo, dc_hi])
                Psi_k = (
                    (iv.mpf(1) + d["es"]) * (d["a0"] + d["a1"] * Dc2 / ((em + d["ec"])**2))
                    + d["A_r_LB"] * (iv.mpf(4) * inv_e_iv + iv.mpf(2) * g)
                )
            F = F + d["lam"] * Psi_k
        return F

    # Certify EVERY box below sig_target = sig_lo_iv.a - 1e-5 (strict certified margin <= -1e-5!)
    sig_target = sig_lo_iv.a - mp.mpf("1e-5")
    boxes = []
    for i in range(len(sorted_breaks) - 1):
        if sorted_breaks[i + 1] > sorted_breaks[i]:
            boxes.append((sorted_breaks[i], sorted_breaks[i + 1]))
    boxes.append((b_max_m, mp.mpf("2.5")))
    boxes.append((mp.mpf("2.5"), mp.mpf("4.0")))
    boxes.append((mp.mpf("4.0"), mp.mpf("8.0")))

    max_F_ub = mp.mpf("-1e9")
    n_eval = 0
    stack = list(reversed(boxes))
    while stack:
        lo, hi = stack.pop()
        n_eval += 1
        F_box = eval_F_iv(lo, hi)
        if F_box.b < sig_target:
            if F_box.b > max_F_ub:
                max_F_ub = F_box.b
        else:
            if hi - lo < mp.mpf("1e-9"):
                raise RuntimeError(f"Failed box [{lo}, {hi}]: F_ub={F_box.b} >= {sig_target}")
            mid = mp.mpf("0.5") * (lo + hi)
            stack.append((mid, hi))
            stack.append((lo, mid))

    # Infinite tail [8.0, +infty):
    F_tail = iv.mpf(8) * iv.exp(-iv.mpf(8))
    for d in cert_iv:
        Psi_tail = (iv.mpf(1) + d["es"]) * (d["a0"] + d["a1"] / (d["ec"]**2)) + d["A_r_LB"] * (iv.mpf(6) * inv_e_iv)
        F_tail = F_tail + d["lam"] * Psi_tail
    assert F_tail.b < sig_target
    max_F_ub = max(max_F_ub, F_tail.b)

    # Exact breakpoints (closed-interval membership):
    for b_pt in sorted_breaks:
        if b_pt >= -tp_hi_iv.b:
            F_pt = eval_F_iv(b_pt, b_pt)
            assert F_pt.b < sig_target
            max_F_ub = max(max_F_ub, F_pt.b)

    print(f"  [PASS] THEOREM 21(c) CERTIFIED ({n_eval} iv-boxes, ZERO grid gaps, ZERO numpy/scipy/LP!):")
    print(f"    sup_{{mu in [-tp_hi, +inf)}} F(mu) <= {mp.nstr(mp.mpf(max_F_ub), 14)}")
    print(f"    sig_lim(K_2^* = 0.3145)           >= {mp.nstr(mp.mpf(sig_lo_iv.a), 14)}")
    print(f"    Certified margin                  <= {mp.nstr(mp.mpf(max_F_ub - sig_lo_iv.a), 6)} (< -1e-5)")
    print(f"    Infinite tail [8, +inf)           <= {mp.nstr(mp.mpf(F_tail.b), 12)}")
    print(f"    Delta K_2 vs V4 = {mp.nstr(K2_Thm10 - K2_LO, 6)} ({float((K2_Thm10 - K2_LO) / (K2_Thm10 - mp.mpf('0.31722794'))):.1f}x V5 Thm 19(b)!)")

    # ==========================================================================
    # PART 2: STANDALONE 35-DIGIT MPMATH.IV CERTIFICATION OF THEOREM 21(b)
    # ==========================================================================
    print("\n" + "=" * 78)
    print("PART 2: STANDALONE PURE-MPMATH.IV VERIFICATION OF THEOREM 21(b) (||V||_op <= 13.412)")
    print("=" * 78)

    def certify_thmB_interval(tp_lo_str, tp_hi_str, alpha_str="4.0", N_terms=120):
        tp_lo_m, tp_hi_m = mp.mpf(tp_lo_str), mp.mpf(tp_hi_str)
        tp = iv.mpf([tp_lo_m, tp_hi_m])
        c0 = iv.mpf(2) * (iv.mpf(1) + tp)
        al = iv.mpf(alpha_str)

        phis_iv = []
        ws_iv = []
        for k in range(1, N_terms + 1):
            base = (k - mp.mpf("0.5")) * mp.pi
            if tp_lo_m == 0:
                p_lo = base
            else:
                p_lo = mp.findroot(lambda p: tp_lo_m * mp.sin(p) + p * mp.cos(p), (base, k * mp.pi), solver="anderson")
            p_hi = mp.findroot(lambda p: tp_hi_m * mp.sin(p) + p * mp.cos(p), (base, k * mp.pi), solver="anderson")
            a_p = max(base, p_lo - mp.mpf("1e-20"))
            b_p = min(k * mp.pi, p_hi + mp.mpf("1e-20"))
            sgn = iv.mpf(-1)**(k - 1)
            if tp_lo_m > 0:
                assert (sgn * (iv.mpf(tp_lo_m) * iv.sin(iv.mpf(a_p)) + iv.mpf(a_p) * iv.cos(iv.mpf(a_p)))).a > 0
            assert (sgn * (iv.mpf(tp_hi_m) * iv.sin(iv.mpf(b_p)) + iv.mpf(b_p) * iv.cos(iv.mpf(b_p)))).b < 0
            p_iv = iv.mpf([a_p, b_p])
            w_iv = (iv.mpf(1) + tp) * p_iv / (tp + tp**2 + p_iv**2)
            phis_iv.append(p_iv)
            ws_iv.append(w_iv)

        def rho_ub(u_mp):
            u_lo = iv.mpf(u_mp)
            s = sum(w * iv.exp(-p * u_lo) for p, w in zip(phis_iv, ws_iv))
            pN = (iv.mpf(N_terms) + iv.mpf("0.5")) * iv.pi
            tail = ((iv.mpf(1) + tp) / pN) * iv.exp(-pN * u_lo) / (iv.mpf(1) - iv.exp(-iv.pi * u_lo))
            return (s + tail).b

        def H_ub(d_mp):
            d = iv.mpf(d_mp)
            s = sum((w / p) * (iv.mpf(1) - iv.exp(-p * d)) for p, w in zip(phis_iv, ws_iv))
            tail = iv.mpf(2) * (iv.mpf(1) + tp) / (iv.pi**2 * (iv.mpf(N_terms) - iv.mpf("0.5")))
            return (iv.mpf(2) * s + tail).b

        def m_al_lb(s_mp):
            s = iv.mpf(s_mp)
            tot = iv.mpf(0)
            for p, w in zip(phis_iv, ws_iv):
                term = iv.mpf(2) * (al * iv.exp(-p * s) - p * iv.exp(-al * s)) / (al**2 - p**2)
                assert term.a > 0
                tot = tot + w * term
            return tot.a

        T_max = mp.mpf("3.0")
        ts = (
            [mp.mpf(i) / mp.mpf(200) for i in range(20)]
            + [mp.mpf("0.1") + mp.mpf(i) / mp.mpf(50) for i in range(25)]
            + [mp.mpf("0.6") + mp.mpf(i) / mp.mpf(15) for i in range(37)]
        )
        int_ub = iv.mpf(0)
        for i in range(len(ts) - 1):
            t_a, t_b = iv.mpf(ts[i]), iv.mpf(ts[i + 1])
            m_lo = iv.mpf(m_al_lb(ts[i + 1]))
            int_ub = int_ub + (iv.exp(-iv.mpf(2) * al * t_a) - iv.exp(-iv.mpf(2) * al * t_b)) / (iv.mpf(2) * al * m_lo)
        p1, w1 = phis_iv[0], ws_iv[0]
        C_tail = w1 * (iv.mpf(2) * al / (al**2 - p1**2)) * (iv.mpf(1) - (p1 / al) * iv.exp(-(al - p1) * iv.mpf(T_max)))
        assert C_tail.a > 0
        tail_int = iv.exp(-(iv.mpf(2) * al - p1) * iv.mpf(T_max)) / (C_tail * (iv.mpf(2) * al - p1))
        cap_al_ub = (iv.mpf(2) * c0**2 * (int_ub + tail_int)).b

        R_tail = (iv.mpf(rho_ub(T_max)) * iv.exp(iv.mpf(p1.b) * iv.mpf(T_max)) / iv.mpf(C_tail.a)).b

        def check_delta(d_mp, n_s=65):
            H_d = H_ub(d_mp)
            s_grid = [d_mp * (T_max / d_mp)**(mp.mpf(i) / mp.mpf(n_s)) for i in range(n_s + 1)]
            R_u = R_tail
            for i in range(n_s):
                val = (iv.mpf(rho_ub(s_grid[i])) / iv.mpf(m_al_lb(s_grid[i + 1]))).b
                if val > R_u:
                    R_u = val
            B_d = (iv.mpf(R_u) * iv.mpf(cap_al_ub)).b
            disc_iv = iv.mpf(c0.a)**2 - iv.mpf(4) * iv.mpf(H_d) * iv.mpf(B_d)
            assert disc_iv.a > 0, f"delta={d_mp} failed on [{tp_lo_str},{tp_hi_str}]"
            r_lo_iv = (iv.mpf(c0.a) - iv.sqrt(disc_iv)) / (iv.mpf(2) * iv.mpf(H_d))
            r_hi_iv = (iv.mpf(c0.a) + iv.sqrt(disc_iv)) / (iv.mpf(2) * iv.mpf(H_d))
            return r_lo_iv.b, r_hi_iv.a, R_u

        d0 = mp.mpf("0.008")
        r0_lo, r0_hi, R0 = check_delta(d0)

        lam_sw = iv.mpf(r0_hi - mp.mpf("1.0"))
        L_sw = iv.log(lam_sw)
        d_sw = iv.mpf(1) / (lam_sw * (iv.mpf(2) + L_sw))
        assert d_sw.b < d0 and lam_sw.a > mp.mpf("20.0")
        m_al_d0 = iv.mpf(m_al_lb(d0))
        T1_sw = (
            (iv.mpf(2) * (iv.mpf(1) + tp) / iv.pi)
            * (iv.mpf("3.5") + L_sw + iv.log(iv.mpf(2) * (iv.mpf(2) + L_sw) / iv.pi))
            / (iv.mpf(2) + L_sw)
        )
        R_elem_sw = (
            ((iv.mpf(1) + tp) / iv.pi)
            * (iv.mpf("2.5") + L_sw + iv.log(iv.mpf(2) * (iv.mpf(2) + L_sw) / iv.pi))
            / m_al_d0
        )
        T2_elem = R_elem_sw * iv.mpf(cap_al_ub) / lam_sw
        T2_tail = iv.mpf(R0) * iv.mpf(cap_al_ub) / lam_sw
        T2_sw_b = max(T2_elem.b, T2_tail.b)
        assert (T1_sw + iv.mpf(T2_sw_b)).b < c0.a, f"Tail failed on [{tp_lo_str},{tp_hi_str}]: {T1_sw.b} + {T2_sw_b} >= {c0.a}"
        print(
            f"  t_+ in [{tp_lo_str:6s}, {tp_hi_str:8s}]: d0=0.008 -> ({mp.nstr(mp.mpf(r0_lo.b), 6)}, "
            f"{mp.nstr(mp.mpf(r0_hi.a), 6)}), tail={mp.nstr(mp.mpf((T1_sw.b + T2_sw_b).b), 5)}<{mp.nstr(mp.mpf(c0.a), 5)} "
            f"==> ||V||_op <= {mp.nstr(mp.mpf(r0_lo.b), 6)}"
        )
        return mp.mpf(r0_lo.b)

    slices = [
        ("0.0", "0.03"), ("0.03", "0.06"), ("0.06", "0.09"), ("0.09", "0.12"),
        ("0.12", "0.15"), ("0.15", "0.18"), ("0.18", "0.21"), ("0.21", "0.245"),
        ("0.245", "0.278465"),
    ]
    assert mp.mpf("0.278465") > tp_hi_iv.b
    max_V_all = mp.mpf(0)
    for s_lo, s_hi in slices:
        v_cap = certify_thmB_interval(s_lo, s_hi, alpha_str="4.0", N_terms=120)
        if v_cap > max_V_all:
            max_V_all = v_cap

    tp_tree = mp.sqrt(1 + 2 * mp.mpf("0.225928542947")) - 1
    v_tree = certify_thmB_interval(
        mp.nstr(tp_tree - mp.mpf("1e-12"), 18), mp.nstr(tp_tree + mp.mpf("1e-12"), 18),
        alpha_str="4.0", N_terms=180,
    )
    tp_top = mp.sqrt(1 + 2 * K2_HI) - 1
    v_top = certify_thmB_interval(
        mp.nstr(tp_top - mp.mpf("1e-12"), 18), mp.nstr(tp_top + mp.mpf("1e-12"), 18),
        alpha_str="4.0", N_terms=180,
    )

    assert max_V_all <= mp.mpf("13.412")
    print(f"\n  [PASS] THEOREM 21(b) CERTIFIED UNIFORMLY FOR ALL K_2 in [0, 0.3172358]: ||V||_op <= {mp.nstr(max_V_all, 6)} (<= 13.412)")
    print(f"    Pointwise at K_2 = 0.3172358:     ||V||_op <= {mp.nstr(v_top, 6)}")
    print(f"    Pointwise at K_2 = K_2^tree(inf): ||V||_op <= {mp.nstr(v_tree, 6)}")
    print("\n" + "=" * 78)
    print(f"ALL STANDALONE 35-DIGIT MPMATH.IV CERTIFICATIONS PASSED IN {time.time() - t0:.2f}s!")
    print("=" * 78)


if __name__ == "__main__":
    main()
