r"""
100% ZERO-FLOAT, ZERO-GAP, ALL-DIMENSIONS (n >= 1) mpmath.iv CERTIFICATION OF THEOREM 4.1
FOR GENERAL 1 < p < 2 (RATIONAL & IRRATIONAL p, m = 2, 3, 4, AND CONTINUOUS p-INTERVALS)!

Architecture (strict zero-trust separation):
  - UNTRUSTED PROPOSER LAYER (propose_*): uses numpy/scipy ONLY to propose candidate
    decimal-string dual witnesses and approximate matrix eigenvectors. Nothing from this
    layer is ever trusted or used in any certified bound.
  - 100% ZERO-FLOAT PURE mpmath.iv CERTIFICATION KERNEL (iv_*): uses ONLY mpmath and
    mpmath.iv (ZERO float(), ZERO numpy!). Every certified bound holds unconditionally
    for ALL dimensions n >= 1 and ALL multipliers Lam >= Lam(C_cert):
      1) Theorem 3.1 (iv_thm31_C_ub) unconditionally rules out ALL C > C_thm31(p, m)
         via the subtraction-free identity log C = log((1+x)/(2 sqrt(x))) + (1/(2k)) log(2x/(1+x)).
      2) Adaptive interval-C covering (iv_certify_all_Lam_above) partitions [C_cert, C_thm31]
         into exact contiguous intervals and certifies Theorem 4.1 (5-scalar / 7-scalar dual)
         on EVERY sub-box in pure mpmath.iv:
           - P_nu(t) on (0, 1+x_+]: exact near-0^+ singular cutoff -lam_{-1}/t <= -lam_{-1}/t_0
             (guarded cleanly when lam_{-1} = 0) + adaptive branch-and-bound with monotonicity
             pruning & mean-value enclosure.
           - P_mu(g) on (0, x_+]: exact zero-wrapping monotonicity cut at 0^+ via
             g^{2-k} P_mu'(g) (for k < 2) or P_mu'(g) (for k >= 2) + adaptive branch-and-bound.
      3) Exact rank-1 Fourier lower bounds (iv_rank1_lower_bound) in pure mpmath.iv for ALL
         36 pairs (12 rational & irrational exponents x m in {2, 3, 4}).
      4) Noncommuting finite-rank matrix Kubo-Ando lower bounds (iv_matrix_kubo_ando_lb) in
         pure mpmath.iv for BOTH rational and irrational exponents (p in {6/5, 4/3, sqrt(2),
         3/2, phi, 5/3}, m = 2) using our 6-step Frobenius Divided-Difference Lemma
           ||A^s - B^s||_2 <= ||A^s - B^s||_F <= s * lam_max^{s-1} * ||A - B||_F  (all s >= 1)
         + exact interval Cholesky certifying K <= (1 + tau) R_0^2, proving C_p(2) > C_{1x1}(p,2)
         rigorously even at irrational exponents p = sqrt(2) and p = phi!
      5) Continuous p-interval envelope certification (Part C) covering EVERY real number
         p in [1.50, 1.99] (m = 2) with exact contiguous 2D boxes [p_a, p_b] x [C_cap, C_thm31]
         and proving C_p(2) <= C_cap(p_a, p_b) < C_interp(p) = ((1+sqrt(2))/2)^{1 - 1/p}
         strictly for EVERY p in [1.50, 1.99] and EVERY dimension n >= 1!
"""

import heapq
import time
import numpy as np
import mpmath as mp
from mpmath import iv
from scipy.optimize import linprog, brentq, least_squares

mp.mp.dps = 38
iv.dps = 34


# ===========================================================================
# PART 0: 100% ZERO-FLOAT PURE mpmath.iv CERTIFICATION KERNEL
#         (ZERO float(), ZERO numpy anywhere in these functions!)
# ===========================================================================

def iv_pow_nonneg(x_iv, e_iv):
    """
    Rigorous pure-mpmath.iv enclosure of {x^e : x in x_iv, e in e_iv}
    for x_iv subset [0, infty), e_iv subset [0, infty).
    Uses monotonicity in x (increasing for e >= 0) and exact endpoint evaluation
    for interval exponents e_iv.
    """
    xa, xb = mp.mpf(x_iv.a), mp.mpf(x_iv.b)
    ea, eb = mp.mpf(e_iv.a), mp.mpf(e_iv.b)
    assert xa >= 0 and ea >= 0
    if eb == 0:
        return iv.mpf(1)
    if xb == 0:
        return iv.mpf(0) if ea > 0 else iv.mpf([mp.mpf(0), mp.mpf(1)])

    def pt_pow(x_pt):
        if x_pt == 0:
            return iv.mpf(0) if ea > 0 else iv.mpf([mp.mpf(0), mp.mpf(1)])
        return iv.exp(e_iv * iv.log(iv.mpf(x_pt)))

    lo_iv = pt_pow(xa)
    hi_iv = pt_pow(xb)
    return iv.mpf([min(mp.mpf(lo_iv.a), mp.mpf(hi_iv.a)),
                   max(mp.mpf(lo_iv.b), mp.mpf(hi_iv.b))])


def iv_eval_roots_and_sigp_from_C(C_iv, kap_iv):
    """
    Pure-mpmath.iv enclosure of x_+(C, kap) > 1 and sig_+(C, kap) = x_+^{kap-1}(x_+ - 1)
    directly from (C_iv, kap_iv) with ZERO Lam/kap dependency wrapping!
    Using the exact subtraction-free identity:
      log C = log((1 + x) / (2 sqrt(x))) + (1 / (2k)) log(2x / (1 + x))  =: Phi(x, k).
    For x > 1, k > 1:
      - d/dx Phi(x, k) = (k*x - (k - 1)) / (2*k*x*(1 + x)) > 0  (strictly increasing in x!)
      - d/dk Phi(x, k) = -log(2x / (1 + x)) / (2*k^2) < 0       (strictly decreasing in k!)
    Hence x_+(C, k) is STRICTLY INCREASING in BOTH C > 1 and k > 1:
      x_+(C_iv, kap_iv) subset [x_+(C_iv.a, kap_iv.a), x_+(C_iv.b, kap_iv.b)],
    and sig_+(C, k) = x_+^{k-1}(x_+ - 1) is STRICTLY INCREASING in BOTH C > 1 and k > 1!
    """
    assert mp.mpf(C_iv.a) > 1 and mp.mpf(kap_iv.a) > 1

    def point_xp_enclose(C_pt, kap_pt):
        logC_i = iv.log(iv.mpf(C_pt))
        k_i = iv.mpf(kap_pt)
        logC_mp = mp.log(C_pt)

        def g_mp(x):
            return mp.log((1 + x) / (2 * mp.sqrt(x))) + mp.log(2 * x / (1 + x)) / (2 * kap_pt) - logC_mp

        def g_iv(x_pt):
            xi = iv.mpf(x_pt)
            return iv.log((1 + xi) / (2 * iv.sqrt(xi))) + iv.log(2 * xi / (1 + xi)) / (2 * k_i) - logC_i

        lo = mp.mpf(1)
        hi = mp.mpf(2)
        while g_mp(hi) <= 0:
            hi *= 2
        for _ in range(115):
            mid = (lo + hi) / 2
            if g_mp(mid) < 0:
                lo = mid
            else:
                hi = mid
        eps = mp.mpf("1e-26") * max(mp.mpf(1), lo)
        xl = max(mp.mpf(1), lo - eps)
        xh = hi + eps
        assert mp.mpf(g_iv(xl).b) < 0 and mp.mpf(g_iv(xh).a) > 0, "x_+ IVT bracket failed!"
        return iv.mpf([xl, xh])

    xp_lo = point_xp_enclose(mp.mpf(C_iv.a), mp.mpf(kap_iv.a))
    xp_hi = point_xp_enclose(mp.mpf(C_iv.b), mp.mpf(kap_iv.b))
    xp_iv = iv.mpf([mp.mpf(xp_lo.a), mp.mpf(xp_hi.b)])
    sigp_lo = mp.mpf((iv_pow_nonneg(iv.mpf(xp_lo.a), iv.mpf(mp.mpf(kap_iv.a)) - 1) * (iv.mpf(xp_lo.a) - 1)).a)
    sigp_hi = mp.mpf((iv_pow_nonneg(iv.mpf(xp_hi.b), iv.mpf(mp.mpf(kap_iv.b)) - 1) * (iv.mpf(xp_hi.b) - 1)).b)
    return xp_iv, iv.mpf([sigp_lo, sigp_hi])


def iv_thm31_C_ub(kap_iv, m):
    """
    Pure-mpmath.iv certified Theorem 3.1 upper bound on C_p(m) for ALL kap in kap_iv!
    Uses the subtraction-free identity:
      log C(x, k) = log((1 + x) / (2 sqrt(x))) + (1 / (2k)) log(2x / (1 + x)),
    which has ZERO subtraction wrapping and is strictly decreasing in k > 1 for every x > 1.
    """
    assert m >= 2 and mp.mpf(kap_iv.a) > 1
    m_iv = iv.mpf(m)
    rhs_iv = ((m_iv - 1) / kap_iv) * iv_pow_nonneg(1 - 1 / (2 * kap_iv), 2 * kap_iv - 1)
    rhs_hi = mp.mpf(rhs_iv.b)
    ka = iv.mpf(mp.mpf(kap_iv.a))

    def lhs_lo(x_pt):
        xi = iv.mpf(x_pt)
        return iv_pow_nonneg((1 + xi) / 2, 2 * ka - 1) * (xi - 1)

    lo = mp.mpf(1)
    hi = mp.mpf(2)
    while mp.mpf(lhs_lo(hi).a) <= rhs_hi:
        hi *= 2
    for _ in range(110):
        mid = (lo + hi) / 2
        if mp.mpf(lhs_lo(mid).a) <= rhs_hi:
            lo = mid
        else:
            hi = mid
    assert mp.mpf(lhs_lo(hi).a) > rhs_hi
    x_ub = iv.mpf(hi)
    log_C_iv = iv.log((1 + x_ub) / (2 * iv.sqrt(x_ub))) + iv.log(2 * x_ub / (1 + x_ub)) / (2 * kap_iv)
    return mp.mpf(iv.exp(log_C_iv).b)


def iv_certify_dual_box(kap_iv, C_iv, m, dual_strs, max_splits=450):
    """
    100% ZERO-FLOAT PURE mpmath.iv CERTIFICATION OF THEOREM 4.1 (5-SCALAR & 7-SCALAR DUAL).
    Proves that NO finite-dimensional solution of Holden's system (1.1)-(1.2) exists for ANY
    (kap, C) in kap_iv x C_iv and ANY dimension n >= 1!
    """
    assert m >= 2 and mp.mpf(C_iv.a) > 1 and mp.mpf(kap_iv.a) > 1
    alpha, beta, gamma, lm1, l6, l7 = [iv.mpf(s) for s in dual_strs]
    assert mp.mpf(lm1.a) >= 0 and mp.mpf(l6.a) >= 0 and mp.mpf(l7.a) >= 0

    Lam_iv = iv_pow_nonneg(2 * C_iv, 2 * kap_iv) / 2
    xp_iv, sigp_iv = iv_eval_roots_and_sigp_from_C(C_iv, kap_iv)
    psi0_lo = mp.mpf((sigp_iv / (m - 1)).a)
    assert psi0_lo > 0
    psi0_iv = iv.mpf(psi0_lo)

    k2m1 = 2 * kap_iv - 1
    k2 = 2 * kap_iv
    km1 = kap_iv - 1
    k2m2 = 2 * kap_iv - 2
    c_km1 = 1 - beta * Lam_iv - gamma * Lam_iv
    c_k = -(1 + gamma * Lam_iv)

    def eval_Pnu_box(t_box):
        val = (alpha * t_box + l6 * (t_box ** 2)
               + beta * iv_pow_nonneg(t_box, k2m1)
               + gamma * iv_pow_nonneg(t_box, k2))
        if mp.mpf(lm1.b) > 0:
            val = val - lm1 * (1 / t_box - 1)
        return val

    def eval_Pnu_deriv(t_box):
        dval = (alpha + 2 * l6 * t_box
                + beta * k2m1 * iv_pow_nonneg(t_box, k2m2)
                + gamma * k2 * iv_pow_nonneg(t_box, k2m1))
        if mp.mpf(lm1.b) > 0:
            dval = dval + lm1 / (t_box ** 2)
        return dval

    def eval_Pmu_box(g_box):
        g_km1 = iv_pow_nonneg(g_box, km1)
        g_k = iv_pow_nonneg(g_box, kap_iv)
        val = c_km1 * g_km1 + c_k * g_k - alpha * g_box - l6 * ((1 + g_box) ** 2)
        if mp.mpf(l7.b) > 0:
            val = val - l7 * (iv_pow_nonneg(g_box, k2) + 2 * psi0_iv * g_k - iv_pow_nonneg(g_box, k2m2))
        return val

    def eval_Pmu_deriv(g_box):
        d_km1 = km1 * iv.exp((kap_iv - 2) * iv.log(g_box))
        d_k = kap_iv * iv_pow_nonneg(g_box, km1)
        dval = c_km1 * d_km1 + c_k * d_k - alpha - 2 * l6 * (1 + g_box)
        if mp.mpf(l7.b) > 0:
            dval = dval - l7 * (k2 * iv_pow_nonneg(g_box, k2m1)
                                + 2 * psi0_iv * d_k
                                - k2m2 * iv.exp((2 * kap_iv - 3) * iv.log(g_box)))
        return dval

    def eval_Pmu_zero_interval(g_cut):
        """Zero-wrapping rigorous upper bound on sup_{g in (0, g_cut]} P_mu(g)."""
        gb0 = iv.mpf([mp.mpf(0), g_cut])
        if mp.mpf(kap_iv.b) < 2:
            scaled_d = (km1 * c_km1 + kap_iv * c_k * gb0
                        - (alpha + 2 * l6) * iv_pow_nonneg(gb0, 2 - kap_iv)
                        - 2 * l6 * iv_pow_nonneg(gb0, 3 - kap_iv))
            if mp.mpf(l7.b) > 0:
                scaled_d = scaled_d - l7 * (k2 * iv_pow_nonneg(gb0, kap_iv + 1)
                                            + 2 * psi0_iv * kap_iv * gb0
                                            - k2m2 * iv_pow_nonneg(gb0, km1))
            if mp.mpf(scaled_d.a) > 0:
                return mp.mpf(eval_Pmu_box(iv.mpf(g_cut)).b), True
            if mp.mpf(scaled_d.b) < 0:
                return mp.mpf((-l6).b), True
        elif mp.mpf(kap_iv.a) >= 2:
            d0 = (km1 * c_km1 * iv_pow_nonneg(gb0, kap_iv - 2)
                  + kap_iv * c_k * iv_pow_nonneg(gb0, km1)
                  - alpha - 2 * l6 * (1 + gb0))
            if mp.mpf(l7.b) > 0:
                d0 = d0 - l7 * (k2 * iv_pow_nonneg(gb0, k2m1)
                                + 2 * psi0_iv * kap_iv * iv_pow_nonneg(gb0, km1)
                                - k2m2 * iv_pow_nonneg(gb0, 2 * kap_iv - 3))
            if mp.mpf(d0.a) > 0:
                return mp.mpf(eval_Pmu_box(iv.mpf(g_cut)).b), True
            if mp.mpf(d0.b) < 0:
                return mp.mpf((-l6).b), True
        return mp.mpf(eval_Pmu_box(gb0).b), False

    def upper_bound_1d(f_box, df_box, a_lo, b_hi, ub_zero):
        def box_ub(la, lb):
            tb = iv.mpf([la, lb])
            ub_dir = mp.mpf(f_box(tb).b)
            if la > 0:
                dfb = df_box(tb)
                if mp.mpf(dfb.a) > 0:
                    return mp.mpf(f_box(iv.mpf(lb)).b), True
                if mp.mpf(dfb.b) < 0:
                    return mp.mpf(f_box(iv.mpf(la)).b), True
                mid = (la + lb) / 2
                assert la <= mid <= lb
                fm = f_box(iv.mpf(mid))
                ub_mv = mp.mpf((fm + dfb * (tb - iv.mpf(mid))).b)
                return min(ub_dir, ub_mv), False
            return ub_dir, False

        pts = [a_lo]
        if a_lo > 0 and b_hi / a_lo > 10:
            n_log = 20
            r_log = (mp.log(b_hi) - mp.log(a_lo)) / n_log
            for k in range(1, n_log):
                pts.append(mp.exp(mp.log(a_lo) + r_log * k))
        else:
            for k in range(1, 16):
                pts.append(a_lo + (b_hi - a_lo) * k / 16)
        pts.append(b_hi)
        assert pts[0] == a_lo and pts[-1] == b_hi and all(pts[i] <= pts[i + 1] for i in range(len(pts) - 1))

        heap = []
        best_pt_lo = mp.mpf("-inf")
        cnt = 0
        for i in range(len(pts) - 1):
            la, lb = pts[i], pts[i + 1]
            ub, is_ex = box_ub(la, lb)
            mid_lo = mp.mpf(f_box(iv.mpf((la + lb) / 2)).a)
            if mid_lo > best_pt_lo:
                best_pt_lo = mid_lo
            heapq.heappush(heap, (-ub, cnt, la, lb, is_ex))
            cnt += 1

        for _ in range(max_splits):
            neg_ub, _, la, lb, is_ex = heapq.heappop(heap)
            cur_ub = -neg_ub
            if is_ex or (cur_ub - best_pt_lo < mp.mpf("1e-13") * max(mp.mpf(1), abs(cur_ub))):
                heapq.heappush(heap, (neg_ub, cnt, la, lb, is_ex))
                break
            mid = (la + lb) / 2
            mid_lo = mp.mpf(f_box(iv.mpf(mid)).a)
            if mid_lo > best_pt_lo:
                best_pt_lo = mid_lo
            for sa, sb in [(la, mid), (mid, lb)]:
                sub_ub, sub_ex = box_ub(sa, sb)
                heapq.heappush(heap, (-sub_ub, cnt, sa, sb, sub_ex))
                cnt += 1
        return max(ub_zero, -heap[0][0])

    # 1) Bound sup P_nu on (0, 1 + xp_iv.b] (outward-rounded upper endpoint!)
    t_hi = mp.mpf((1 + xp_iv).b)
    if mp.mpf(lm1.a) > 0:
        t0 = mp.mpf("1e-3")

        def nu_zero(t_cut):
            tb0 = iv.mpf([mp.mpf(0), t_cut])
            non_sing = (alpha * tb0 + l6 * (tb0 ** 2)
                        + beta * iv_pow_nonneg(tb0, k2m1)
                        + gamma * iv_pow_nonneg(tb0, k2) + lm1)
            return mp.mpf((non_sing - lm1 / iv.mpf(t_cut)).b)

        ref_nu = mp.mpf(eval_Pnu_box(iv.mpf(mp.mpf(1))).a)
        while nu_zero(t0) > ref_nu and t0 > mp.mpf("1e-30"):
            t0 /= 10
        sup_nu = upper_bound_1d(eval_Pnu_box, eval_Pnu_deriv, t0, t_hi, nu_zero(t0))
    else:
        assert mp.mpf(lm1.b) == 0, "Expected exact zero lm1 in non-singular branch!"
        # lm1 == 0: P_nu is smooth at t = 0 with P_nu(0) = 0; certify monotonicity on [0, t0] for ZERO wrapping!
        t0 = mp.mpf("1e-6")
        ub_nu0 = None
        while t0 >= mp.mpf("1e-30"):
            tb0 = iv.mpf([mp.mpf(0), t0])
            d_nu0 = eval_Pnu_deriv(tb0)
            if mp.mpf(d_nu0.b) < 0:
                ub_nu0 = mp.mpf(0)
                break
            if mp.mpf(d_nu0.a) > 0:
                ub_nu0 = mp.mpf(eval_Pnu_box(iv.mpf(t0)).b)
                break
            t0 /= 100
        if ub_nu0 is None:
            ub_nu0 = mp.mpf(eval_Pnu_box(iv.mpf([mp.mpf(0), t0])).b)
        sup_nu = upper_bound_1d(eval_Pnu_box, eval_Pnu_deriv, t0, t_hi, ub_nu0)

    # 2) Bound sup P_mu on (0, xp_iv.b] using exact zero-wrapping monotonicity cut at 0^+
    g_hi = mp.mpf(xp_iv.b)
    g0 = mp.mpf("1e-8")
    ub_g0, mono_ok = eval_Pmu_zero_interval(g0)
    while not mono_ok and g0 > mp.mpf("1e-80"):
        g0 *= mp.mpf("1e-4")
        ub_g0, mono_ok = eval_Pmu_zero_interval(g0)
    sup_mu = upper_bound_1d(eval_Pmu_box, eval_Pmu_deriv, g0, g_hi, ub_g0)

    ub_hi = mp.mpf((iv.mpf(sup_nu) + iv.mpf(sup_mu) - alpha - l7 * (psi0_iv ** 2)).b)
    ok = (ub_hi < psi0_lo)
    margin_lo = mp.mpf((iv.mpf(psi0_lo) - iv.mpf(ub_hi)).a)
    return ok, margin_lo, ub_hi, psi0_lo


def iv_rank1_upper_bound(p_iv, m):
    """
    100% zero-float pure mpmath.iv certified UPPER bound on C_{1x1}(p, m) for all p in p_iv!
    Since x_+ > 1 > (k-1)/k > x_- > 0 and d/dLam [sig_+(Lam) + (m-1) sig_-(Lam)] > 0:
    certifying sig_+(C_hi, kap) + (m-1) sig_-(C_hi, kap) > 0 for every kap in kap_iv
    rigorously proves C_{1x1}(p, m) < C_hi!
    """
    assert m >= 2 and mp.mpf(p_iv.a) > 1 and mp.mpf(p_iv.b) < 2
    kap_iv = p_iv / (2 * (p_iv - 1))
    assert mp.mpf(kap_iv.a) > 1
    m_iv = iv.mpf(m)

    def eval_F_iv(C_pt):
        C_iv = iv.mpf(C_pt)
        _, sigp_iv = iv_eval_roots_and_sigp_from_C(C_iv, kap_iv)

        def point_xm_enclose(kap_pt):
            k_i = iv.mpf(kap_pt)
            logC_i = iv.log(C_iv)
            logC_mp = mp.log(C_pt)
            x_star = (kap_pt - 1) / kap_pt
            t_hi = mp.log(x_star)

            def g_mp(t):
                x = mp.exp(t)
                return mp.log((1 + x) / (2 * mp.sqrt(x))) + mp.log(2 * x / (1 + x)) / (2 * kap_pt) - logC_mp

            def g_iv(t_pt):
                xi = iv.exp(iv.mpf(t_pt))
                return iv.log((1 + xi) / (2 * iv.sqrt(xi))) + iv.log(2 * xi / (1 + xi)) / (2 * k_i) - logC_i

            t_lo = t_hi - 1
            while g_mp(t_lo) <= 0:
                t_lo -= 10
            a, b = t_lo, t_hi
            for _ in range(115):
                mid = (a + b) / 2
                if g_mp(mid) > 0:
                    a = mid
                else:
                    b = mid
            eps = mp.mpf("1e-26") * max(mp.mpf(1), abs(a))
            tl = a - eps
            th = min(t_hi, b + eps)
            assert mp.mpf(iv.exp(iv.mpf(th)).b) < mp.mpf(((k_i - 1) / k_i).a), "x_- bracket crossed x^*!"
            assert mp.mpf(g_iv(tl).a) > 0 and mp.mpf(g_iv(th).b) < 0, "x_- IVT bracket failed!"
            return iv.mpf([mp.mpf(iv.exp(iv.mpf(tl)).a), mp.mpf(iv.exp(iv.mpf(th)).b)])

        xm_lo = point_xm_enclose(mp.mpf(kap_iv.a))
        xm_hi = point_xm_enclose(mp.mpf(kap_iv.b))
        xm_iv = iv.mpf([mp.mpf(xm_lo.a), mp.mpf(xm_hi.b)])
        sigm_iv = iv_pow_nonneg(xm_iv, kap_iv - 1) * (xm_iv - 1)
        return sigp_iv + (m_iv - 1) * sigm_iv

    lo = mp.mpf(1)
    hi = iv_thm31_C_ub(kap_iv, m)
    assert mp.mpf(eval_F_iv(hi).a) > 0
    for _ in range(70):
        mid = (lo + hi) / 2
        if mid <= lo or mid >= hi:
            break
        if mp.mpf(eval_F_iv(mid).a) > 0:
            hi = mid
        else:
            lo = mid
    assert mp.mpf(eval_F_iv(hi).a) > 0
    return hi


def iv_rank1_lower_bound(p_iv, m, x1_str):
    """
    100% zero-float pure mpmath.iv rank-1 Fourier lower bound (Theorem 1.2, N = 1):
      S_1 = x1 > 0, S_2 = ... = S_m = 1  ==>  M_KA = (x1^s + m - 1)/m, N_KA = (x1 + m - 1)/m,
      C_p(m) >= (N_KA / M_KA)^{1/2} * ((x1^s + m - 1) / (x1^p + m - 1))^{1/p}.
    """
    x1_iv = iv.mpf(x1_str)
    assert mp.mpf(x1_iv.a) > 0
    s_iv = p_iv / (2 - p_iv)
    assert m >= 2 and mp.mpf(p_iv.a) > 1 and mp.mpf(p_iv.b) < 2
    m_iv = iv.mpf(m)
    num_s = iv_pow_nonneg(x1_iv, s_iv) + (m_iv - 1)
    num_1 = x1_iv + (m_iv - 1)
    den_p = iv_pow_nonneg(x1_iv, p_iv) + (m_iv - 1)
    log_lb = iv.log(num_1 / num_s) / 2 + iv.log(num_s / den_p) / p_iv
    return mp.mpf(iv.exp(log_lb).a)


def iv_mat_mul(A, B, N):
    out = [[iv.mpf(0)] * N for _ in range(N)]
    for i in range(N):
        for j in range(N):
            acc = iv.mpf(0)
            for k in range(N):
                acc += A[i][k] * B[k][j]
            out[i][j] = acc
    return out


def iv_mat_transpose(A, N):
    return [[A[j][i] for j in range(N)] for i in range(N)]


def iv_frob_norm_ub(A, N):
    acc = iv.mpf(0)
    for i in range(N):
        for j in range(N):
            acc += A[i][j] ** 2
    return mp.mpf(iv.sqrt(acc).b)


def iv_cholesky_psd(A, N):
    """Exact pure-mpmath.iv Cholesky certifying symmetric A > 0 (all pivots > 0)."""
    L = [[iv.mpf(0)] * N for _ in range(N)]
    for i in range(N):
        for j in range(i + 1):
            acc = A[i][j]
            for k in range(j):
                acc -= L[i][k] * L[j][k]
            if i == j:
                if mp.mpf(acc.a) <= 0:
                    return False
                L[i][i] = iv.sqrt(acc)
            else:
                L[i][j] = acc / L[j][j]
    return True


def iv_matrix_kubo_ando_lb(p_iv, m, S_str_list, R0_strs, V_S_strs, lam_S_strs, V_Y_strs, lam_Y_strs, tau_str):
    """
    100% ZERO-FLOAT PURE mpmath.iv NONCOMMUTING MATRIX KUBO-ANDO LOWER BOUND FOR ANY
    RATIONAL OR IRRATIONAL p in (1, 2)!

    Uses our 6-step Frobenius Divided-Difference Lemma (valid for ALL s >= 1):
      For symmetric S_j > 0, approximate orthogonal V_j with ||V_j^T V_j - I||_F <= delta < 1,
      and positive diagonal L_j = diag(lam_j):
        1) ||V_j - U_j||_F <= delta (U_j exact polar orthogonal factor), ||V_j||_2 <= 1 + delta.
        2) ||V_j L_j^r V_j^T - U_j L_j^r U_j^T||_F <= delta (2 + delta) max(lam_j^r) for any r > 0.
        3) eta_j := ||S_j - V_j L_j V_j^T||_F + delta (2 + delta) max(lam_j) >= ||S_j - U_j L_j U_j^T||_F.
        4) Weyl: lam_i(S_j) in [lam_{j,i} - eta_j, lam_{j,i} + eta_j] (certifies S_j > 0 & Tr(S_j^s)!).
        5) Divided-Difference Lemma: ||S_j^s - U_j L_j^s U_j^T||_F <= s * (max(lam_j) + eta_j)^{s-1} * eta_j.
        6) Loewner upper bound: S_j^s <= V_j L_j^s V_j^T + eps_op_j * I,
           where eps_op_j := s * (max(lam_j) + eta_j)^{s-1} * eta_j + delta (2 + delta) max(lam_j^s).
      Exact interval Cholesky on (1 + tau)^2 R_0^2 N_KA R_0^2 - M_KA_ub > 0 certifies K <= (1 + tau) R_0^2,
      and Weyl on Y_j = R_0 S_j R_0 encloses Tr((R_0 S_j R_0)^p), yielding:
        C_p(m) >= (sum Tr(S_j^s) / ((1 + tau)^p sum Tr((R_0 S_j R_0)^p)))^{1/p}!
    """
    s_iv = p_iv / (2 - p_iv)
    tau_iv = iv.mpf(tau_str)
    assert mp.mpf(tau_iv.a) >= 0
    N = len(S_str_list[0])

    # Parse symmetric S_j and R0 in pure iv (explicitly symmetrizing!)
    Ss = []
    for j in range(m):
        S = [[iv.mpf(S_str_list[j][i][k]) for k in range(N)] for i in range(N)]
        for i in range(N):
            for k in range(i + 1, N):
                S[k][i] = S[i][k]
        Ss.append(S)
    R0 = [[iv.mpf(R0_strs[i][k]) for k in range(N)] for i in range(N)]
    for i in range(N):
        for k in range(i + 1, N):
            R0[k][i] = R0[i][k]

    def cert_sym_eigen(A, V_strs, lam_strs):
        V = [[iv.mpf(V_strs[i][k]) for k in range(N)] for i in range(N)]
        VT = iv_mat_transpose(V, N)
        VTV = iv_mat_mul(VT, V, N)
        E_orth = [[VTV[i][k] - (iv.mpf(1) if i == k else iv.mpf(0)) for k in range(N)] for i in range(N)]
        delta = iv_frob_norm_ub(E_orth, N)
        assert delta < mp.mpf("0.1"), f"Orthogonality error too large: {delta}"
        lams = [iv.mpf(v) for v in lam_strs]
        assert all(mp.mpf(lv.a) > 0 for lv in lams)
        lam_max = max(mp.mpf(lv.b) for lv in lams)
        # Compute V * diag(lams) * V^T
        VL = [[V[i][k] * lams[k] for k in range(N)] for i in range(N)]
        VLVT = iv_mat_mul(VL, VT, N)
        Diff = [[A[i][k] - VLVT[i][k] for k in range(N)] for i in range(N)]
        res_f = iv_frob_norm_ub(Diff, N)
        eta = mp.mpf((iv.mpf(res_f) + iv.mpf(delta) * (2 + iv.mpf(delta)) * iv.mpf(lam_max)).b)
        enc = []
        for lv in lams:
            lo = mp.mpf((iv.mpf(lv.a) - iv.mpf(eta)).a)
            hi = mp.mpf((iv.mpf(lv.b) + iv.mpf(eta)).b)
            assert lo > 0, f"Positive-definiteness check failed: lo={lo}"
            enc.append(iv.mpf([lo, hi]))
        return V, VT, lams, delta, eta, enc

    # Step 1-6 for each S_j: enclose Tr(S_j^s) AND build M_KA_ub!
    num_lo = iv.mpf(0)
    M_ub = [[iv.mpf(0)] * N for _ in range(N)]
    N_ka = [[iv.mpf(0)] * N for _ in range(N)]
    for j in range(m):
        V, VT, lams, delta, eta, enc = cert_sym_eigen(Ss[j], V_S_strs[j], lam_S_strs[j])
        # Lower bound on Tr(S_j^s)
        for ev_iv in enc:
            num_lo += iv_pow_nonneg(ev_iv, s_iv)
        # Loewner upper bound on S_j^s <= V L^s V^T + eps_op * I
        lams_s = [iv_pow_nonneg(lv, s_iv) for lv in lams]
        lam_max_s = max(mp.mpf(ls.b) for ls in lams_s)
        lam_max_tot = max(mp.mpf(ev_iv.b) for ev_iv in enc)
        eps_dd = mp.mpf((s_iv * iv_pow_nonneg(iv.mpf(lam_max_tot), s_iv - 1) * iv.mpf(eta)).b)
        eps_or = mp.mpf((iv.mpf(delta) * (2 + iv.mpf(delta)) * iv.mpf(lam_max_s)).b)
        eps_op = mp.mpf((iv.mpf(eps_dd) + iv.mpf(eps_or)).b)

        VLs = [[V[i][k] * lams_s[k] for k in range(N)] for i in range(N)]
        VLsVT = iv_mat_mul(VLs, VT, N)
        for i in range(N):
            for k in range(N):
                M_ub[i][k] += VLsVT[i][k] / m
                N_ka[i][k] += Ss[j][i][k] / m
            M_ub[i][i] += iv.mpf(eps_op) / m

    # Certify (1 + tau)^2 R0^2 N_KA R0^2 - M_ub > 0 via exact interval Cholesky!
    R02 = iv_mat_mul(R0, R0, N)
    scale_iv = (1 + tau_iv) ** 2
    LHS = iv_mat_mul(iv_mat_mul(R02, N_ka, N), R02, N)
    Cert_mat = [[scale_iv * LHS[i][k] - M_ub[i][k] for k in range(N)] for i in range(N)]
    # Enforce exact symmetry (rounding safety: symmetrize intervals around diagonal)
    for i in range(N):
        for k in range(i + 1, N):
            avg = (Cert_mat[i][k] + Cert_mat[k][i]) / 2
            Cert_mat[i][k] = Cert_mat[k][i] = avg
    assert iv_cholesky_psd(Cert_mat, N), "Interval Cholesky failed for Kubo-Ando K <= (1+tau) R0^2!"

    # Enclose denominator: Tr((K^{1/2} S_j K^{1/2})^p) <= (1 + tau)^p Tr((R0 S_j R0)^p)
    den_ub = iv.mpf(0)
    for j in range(m):
        Yj = iv_mat_mul(iv_mat_mul(R0, Ss[j], N), R0, N)
        for i in range(N):
            for k in range(i + 1, N):
                avg = (Yj[i][k] + Yj[k][i]) / 2
                Yj[i][k] = Yj[k][i] = avg
        _, _, _, _, _, enc_Y = cert_sym_eigen(Yj, V_Y_strs[j], lam_Y_strs[j])
        for ev_iv in enc_Y:
            den_ub += iv_pow_nonneg(ev_iv, p_iv)
    den_ub = den_ub * iv_pow_nonneg(1 + tau_iv, p_iv)

    log_C_lb = iv.log(num_lo / den_ub) / p_iv
    return mp.mpf(iv.exp(log_C_lb).a)


# ===========================================================================
# PART 1: UNTRUSTED HEURISTIC WITNESS PROPOSERS (float/scipy, never trusted!)
# ===========================================================================

def propose_rank1_x1(p_f, m):
    kap_m = mp.mpf(f"{p_f:.17e}") / (2 * (mp.mpf(f"{p_f:.17e}") - 1))
    t_min = mp.log((kap_m - 1) / kap_m)

    def roots_mp(L):
        logL = mp.log(L)
        g = lambda t: (2 * kap_m - 1) * mp.log(1 + mp.exp(t)) - (kap_m - 1) * t - logL
        lo = t_min - 1
        while g(lo) < 0:
            lo -= 10
        hi = t_min + 1
        while g(hi) < 0:
            hi += 10
        a, b = lo, t_min
        for _ in range(110):
            mid = (a + b) / 2
            if g(mid) > 0:
                a = mid
            else:
                b = mid
        xm = mp.exp((a + b) / 2)
        a, b = t_min, hi
        for _ in range(110):
            mid = (a + b) / 2
            if g(mid) < 0:
                a = mid
            else:
                b = mid
        xp = mp.exp((a + b) / 2)
        return xm, xp

    Lam0 = mp.power(2, 2 * kap_m - 1)
    lo = Lam0 * (1 + mp.mpf("1e-22"))
    hi = max(Lam0 * 2, mp.mpf(4) * mp.sqrt(m))

    def eq1(L):
        xm, xp = roots_mp(L)
        return xp ** (kap_m - 1) * (xp - 1) + (m - 1) * xm ** (kap_m - 1) * (xm - 1)

    while eq1(hi) < 0:
        hi *= 2
    for _ in range(110):
        mid = (lo + hi) / 2
        if eq1(mid) < 0:
            lo = mid
        else:
            hi = mid
    xm, xp = roots_mp((lo + hi) / 2)
    x1 = mp.exp((kap_m - 1) * mp.log(xp / xm))
    return mp.nstr(x1, 35)


def propose_dual_witness(kap_f, Lam_f, m, use_7scalar=True):
    """Untrusted scipy LP proposer returning decimal strings (alpha, beta, gamma, lm1, l6, l7)."""
    t_min = np.log((kap_f - 1.0) / kap_f)
    logL = np.log(Lam_f)
    g = lambda t: (2 * kap_f - 1) * np.logaddexp(0.0, t) - (kap_f - 1) * t - logL
    lo = t_min - 1.0
    while g(lo) < 0:
        lo -= 10.0
    hi = t_min + 1.0
    while g(hi) < 0:
        hi += 10.0
    xm = np.exp(brentq(g, lo, t_min, xtol=1e-15))
    xp = np.exp(brentq(g, t_min, hi, xtol=1e-15))
    sigp = (xp ** (kap_f - 1.0)) * (xp - 1.0)
    psi0 = sigp / (m - 1.0)

    xm_safe = max(xm, 1e-250)
    ts = np.unique(np.concatenate([np.geomspace(1e-3, 0.99, 40), np.linspace(1.0, 1.0 + xp, 100), [1.0 + xm_safe, 1.0 + xp]]))
    if xm > 1e-40:
        gs = np.unique(np.concatenate([[0.0], np.geomspace(max(1e-250, xm * 1e-3), xm, 40), np.geomspace(xm, xp, 100), [xm, xp]]))
        g_fine = np.unique(np.concatenate([[0.0], np.geomspace(max(1e-250, xm * 1e-5), xp, 3000), np.linspace(max(1e-12, xm * 0.5), xp, 3000)]))
    else:
        gs = np.unique(np.concatenate([[0.0], np.geomspace(1e-30, xp, 100), [xm_safe, xp]]))
        g_fine = np.unique(np.concatenate([[0.0], np.geomspace(1e-35, xp, 3000), np.linspace(1e-12, xp, 3000), [xm_safe]]))
    t_fine = np.unique(np.concatenate([np.geomspace(1e-6, 0.9999, 2000), np.linspace(1.0, 1.0 + xp, 4000)]))

    s_t1 = max(1.0, (1.0 + xp) ** (2.0 * kap_f - 1.0))
    s_t2 = max(1.0, (1.0 + xp) ** (2.0 * kap_f))
    s_g7 = max(1.0, xp ** (2.0 * kap_f))

    best = None
    for _ in range(10):
        nt, ng = len(ts), len(gs)
        n_tot = nt + ng
        c_lp = np.zeros(n_tot)
        c_lp[nt:] = -(gs ** (kap_f - 1.0) - gs ** kap_f)
        A_eq = np.zeros((5, n_tot))
        b_eq = np.zeros(5)
        A_eq[0, :nt] = 1.0; b_eq[0] = 1.0
        A_eq[1, nt:] = 1.0; b_eq[1] = 1.0
        A_eq[2, :nt] = ts; A_eq[2, nt:] = -gs; b_eq[2] = 1.0
        A_eq[3, :nt] = (ts ** (2 * kap_f - 1)) / s_t1; A_eq[3, nt:] = -Lam_f * (gs ** (kap_f - 1)) / s_t1
        A_eq[4, :nt] = (ts ** (2 * kap_f)) / s_t2; A_eq[4, nt:] = -Lam_f * (gs ** (kap_f - 1) + gs ** kap_f) / s_t2
        if use_7scalar:
            A_ub = np.zeros((3, n_tot)); b_ub = np.zeros(3)
            A_ub[0, :nt] = 1.0 / ts; b_ub[0] = 1.0
            A_ub[1, :nt] = -(ts ** 2); A_ub[1, nt:] = (1.0 + gs) ** 2; b_ub[1] = 0.0
            A_ub[2, nt:] = (gs ** (2 * kap_f) + 2 * psi0 * (gs ** kap_f) - gs ** (2 * kap_f - 2)) / s_g7
            b_ub[2] = -(psi0 ** 2) / s_g7
        else:
            A_ub = np.zeros((1, n_tot)); b_ub = np.array([1.0])
            A_ub[0, :nt] = 1.0 / ts
        res = linprog(c_lp, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=(0, None), method="highs")
        if not res.success:
            if best is not None:
                return best
            if use_7scalar:
                return propose_dual_witness(kap_f, Lam_f, m, use_7scalar=False)
            return None
        ym = res.eqlin.marginals
        zm = res.ineqlin.marginals
        alpha = float(ym[2]); beta = float(ym[3]) / s_t1; gamma = float(ym[4]) / s_t2
        lm1 = max(0.0, float(-zm[0]))
        l6 = max(0.0, float(-zm[1])) if use_7scalar else 0.0
        l7 = max(0.0, float(-zm[2]) / s_g7) if use_7scalar else 0.0

        P_nu = alpha * t_fine + l6 * (t_fine ** 2) + beta * (t_fine ** (2 * kap_f - 1)) + gamma * (t_fine ** (2 * kap_f)) - lm1 * (1.0 / t_fine - 1.0)
        P_mu = ((g_fine ** (kap_f - 1) - g_fine ** kap_f) - alpha * g_fine - l6 * ((1.0 + g_fine) ** 2)
                - beta * Lam_f * (g_fine ** (kap_f - 1)) - gamma * Lam_f * (g_fine ** (kap_f - 1) + g_fine ** kap_f)
                - l7 * (g_fine ** (2 * kap_f) + 2 * psi0 * (g_fine ** kap_f) - g_fine ** (2 * kap_f - 2)))
        it, ig = int(np.argmax(P_nu)), int(np.argmax(P_mu))
        ub = float(P_nu[it] + P_mu[ig] - alpha - l7 * (psi0 ** 2))
        if best is None or ub < best[0]:
            strs = tuple(f"{float(v):.17e}" for v in (alpha, beta, gamma, lm1, l6, l7))
            best = (ub, strs, psi0)
        if abs(ub - (-res.fun)) < 1e-11:
            break
        ts = np.unique(np.append(ts, t_fine[it]))
        gs = np.unique(np.append(gs, g_fine[ig]))
    return best


def propose_rank2_matrix_witness(p_mp, m=2, L_dep=3):
    """
    Untrusted proposer: solves r=2 RG block for arbitrary (rational or irrational) p,
    builds depth-L_dep (N = L_dep + 1 = 4) symmetric SPD matrices S_0, S_1, computes high-precision
    mpmath eigendecompositions V_S, lam_S, R0, V_Y, lam_Y, and returns exact decimal strings
    for the zero-float pure-mpmath.iv certifier!
    """
    p_f = float(p_mp)
    kap = p_f / (2.0 * (p_f - 1.0))
    s_f = kap / (kap - 1.0)

    def roots_f(Lam):
        t_min = np.log((kap - 1.0) / kap); lL = np.log(Lam)
        g = lambda t: (2 * kap - 1) * np.logaddexp(0.0, t) - (kap - 1) * t - lL
        if g(t_min) >= 0:
            return None
        lo = t_min - 1.0
        while g(lo) < 0: lo -= 10.0
        hi = t_min + 1.0
        while g(hi) < 0: hi += 10.0
        xm = np.exp(brentq(g, lo, t_min, xtol=1e-15))
        xp = np.exp(brentq(g, t_min, hi, xtol=1e-15))
        return xm, xp, xp ** (kap - 1) * (xp - 1), xm ** (kap - 1) * (xm - 1)

    Lam0 = 2.0 ** (2 * kap - 1)
    hi = max(Lam0 * 2.0, 4.0)
    while roots_f(hi)[2] + (m - 1) * roots_f(hi)[3] < 0:
        hi *= 2.0
    Lam1 = brentq(lambda L: roots_f(L)[2] + (m - 1) * roots_f(L)[3], Lam0 * (1 + 1e-13), hi, xtol=1e-15)
    xm1, xp1, _, _ = roots_f(Lam1)

    def sym_pow_np(M, pw):
        M = 0.5 * (M + M.T)
        ev, V = np.linalg.eigh(M)
        if ev[0] <= 1e-18:
            return None
        return (V * (ev ** pw)) @ V.T

    triu2 = np.triu_indices(2)
    best_r2 = None
    for d_try in [1e-3, 1e-2, 0.06, 0.2, 0.4]:
        for bf in [-0.2, -0.45]:
            b = bf * np.sqrt(xm1 * xp1)
            def res2(x):
                Lm = x[0]; d = np.array([1.0, np.exp(x[1])])
                X = np.array([[x[2], x[3]], [x[3], x[4]]])
                rt = roots_f(Lm)
                if rt is None: return np.full(6, 1e3)
                _, _, sp, _ = rt
                sd = np.sqrt(d); D = np.diag(d)
                H = (sd[:, None] * X) * sd[None, :]; G = (sd[:, None] * H) * sd[None, :]
                Mp = sym_pow_np(D + H, 2 * kap - 1); Gkm1 = sym_pow_np(G, kap - 1); Gk = sym_pow_np(G, kap)
                if Mp is None or Gkm1 is None or Gk is None: return np.full(6, 1e3)
                R1 = Mp - Lm * ((sd[:, None] * Gkm1) * sd[None, :])
                R2 = Gk - (d[:, None] * Gkm1) * d[None, :] - np.diag([-sp / (m - 1), sp * d[1] ** (2 * kap)])
                w1 = 1.0 / np.outer(d ** (kap - 0.5), d ** (kap - 0.5))
                w2 = 1.0 / np.outer(d ** kap, d ** kap)
                return np.concatenate([(R1 * w1)[triu2], (R2 * w2)[triu2]])
            sol = least_squares(res2, [Lam1 * 1.00001, np.log(d_try), xm1, b, 0.45 * xp1], xtol=1e-15, ftol=1e-15, gtol=1e-15)
            if np.linalg.norm(sol.fun) < 1e-10 and abs(sol.x[3]) > 1e-6 and sol.x[0] > Lam1 + 1e-12:
                if best_r2 is None or sol.x[0] > best_r2[0]:
                    best_r2 = (sol.x[0], np.array([1.0, np.exp(sol.x[1])]), np.array([[sol.x[2], sol.x[3]], [sol.x[3], sol.x[4]]]))
    assert best_r2 is not None
    Lam, d, X = best_r2
    xm, xp, _, _ = roots_f(Lam)
    sd = np.sqrt(d); H2 = (sd[:, None] * X) * sd[None, :]; G2 = (sd[:, None] * H2) * sd[None, :]
    G2_km1 = sym_pow_np(G2, kap - 1)
    N = L_dep + 1
    d_nodes = [d[1] ** k for k in range(N)]
    S_np = []
    for j in range(2):
        Sj = np.zeros((N, N))
        if j == 0:
            Sj[0, 0] = (xp ** (kap - 1)) * (d_nodes[0] ** (2 * kap - 2)); k = 1
        else:
            k = 0
        while k < N:
            if k + 1 < N:
                Sj[k:k + 2, k:k + 2] = (d_nodes[k] ** (2 * kap - 2)) * G2_km1; k += 2
            else:
                Sj[k, k] = (xm ** (kap - 1)) * (d_nodes[k] ** (2 * kap - 2)); k += 1
        S_np.append(0.5 * (Sj + Sj.T))

    # Convert S_np to exact 16-digit decimal strings and compute 35-digit mpmath eigendecompositions!
    S_str_list = [[[f"{S_np[j][i, k]:.16e}" for k in range(N)] for i in range(N)] for j in range(2)]
    S_mp = [mp.matrix([[mp.mpf(S_str_list[j][i][k]) for k in range(N)] for i in range(N)]) for j in range(2)]
    for j in range(2):
        for i in range(N):
            for k in range(i + 1, N):
                S_mp[j][k, i] = S_mp[j][i, k]

    s_mp = p_mp / (2 - p_mp)
    V_S_strs, lam_S_strs = [], []
    M_mp = mp.zeros(N, N)
    N_mp = mp.zeros(N, N)
    for j in range(2):
        ev, V = mp.eigsy(S_mp[j])
        V_S_strs.append([[mp.nstr(V[i, k], 35) for k in range(N)] for i in range(N)])
        lam_S_strs.append([mp.nstr(ev[i], 35) for i in range(N)])
        Ss_j = V * mp.diag([ev[i] ** s_mp for i in range(N)]) * V.T
        M_mp += Ss_j / 2
        N_mp += S_mp[j] / 2

    # Compute exact K = N^{-1/2} (N^{1/2} M N^{1/2})^{1/2} N^{-1/2} and R0 = K^{1/2} in 35-digit mpmath!
    evN, VN = mp.eigsy(N_mp)
    Nh = VN * mp.diag([mp.sqrt(evN[i]) for i in range(N)]) * VN.T
    Nmh = VN * mp.diag([1 / mp.sqrt(evN[i]) for i in range(N)]) * VN.T
    evT, VT = mp.eigsy(Nh * M_mp * Nh)
    K_mp = Nmh * (VT * mp.diag([mp.sqrt(evT[i]) for i in range(N)]) * VT.T) * Nmh
    K_mp = (K_mp + K_mp.T) / 2
    evK, VK = mp.eigsy(K_mp)
    R0_mp = VK * mp.diag([mp.sqrt(evK[i]) for i in range(N)]) * VK.T
    R0_mp = (R0_mp + R0_mp.T) / 2
    R0_strs = [[mp.nstr(R0_mp[i, k], 35) for k in range(N)] for i in range(N)]

    V_Y_strs, lam_Y_strs = [], []
    for j in range(2):
        Yj = R0_mp * S_mp[j] * R0_mp
        Yj = (Yj + Yj.T) / 2
        evY, VY = mp.eigsy(Yj)
        V_Y_strs.append([[mp.nstr(VY[i, k], 35) for k in range(N)] for i in range(N)])
        lam_Y_strs.append([mp.nstr(evY[i], 35) for i in range(N)])

    return S_str_list, R0_strs, V_S_strs, lam_S_strs, V_Y_strs, lam_Y_strs, "1e-15"


# ===========================================================================
# DRIVER: ADAPTIVE CONTIGUOUS ALL-Lam CERTIFICATION (POINT & 2D CONTINUOUS p)
# ===========================================================================

def certify_point_p_m(p_iv, m, C_lb_mp):
    """
    Certifies C_p(m) <= C_cert for ALL n >= 1 and ALL Lam >= Lam(C_cert)
    by combining Theorem 3.1 above C_t31 with contiguous pure-mpmath.iv covering of [C_cert, C_t31].
    """
    kap_iv = p_iv / (2 * (p_iv - 1))
    kap_f = float((mp.mpf(kap_iv.a) + mp.mpf(kap_iv.b)) / 2)
    Lam0_f = 2.0 ** (2 * kap_f - 1)
    C_t31 = iv_thm31_C_ub(kap_iv, m)

    # Heuristic binary search for tightest achievable 7-scalar C_ub
    lo_c = float(C_lb_mp)
    hi_c = float(C_t31)
    n_bis = 40 if (mp.mpf(p_iv.a) > mp.mpf("1.85")) else 30
    for _ in range(n_bis):
        mid_c = 0.5 * (lo_c + hi_c)
        hd = propose_dual_witness(kap_f, Lam0_f * (mid_c ** (2 * kap_f)), m, use_7scalar=True)
        if hd is not None and hd[0] < hd[2] - 1e-14:
            hi_c = mid_c
        else:
            lo_c = mid_c

    gap_est = max(1e-11, hi_c - float(C_lb_mp))
    pad = max(1e-9, gap_est * 0.02) if float(mp.mpf(p_iv.a)) < 1.92 else max(5e-10, gap_est * 0.15)
    C_cert = mp.mpf(f"{min(float(C_t31), hi_c + pad):.14f}")

    # Ensure C_cert is strictly inside the IV-certifiable region before launching full covering!
    for _ in range(8):
        hd_pt = propose_dual_witness(kap_f, Lam0_f * (float(C_cert) ** (2 * kap_f)), m, use_7scalar=True)
        if hd_pt is not None and iv_certify_dual_box(kap_iv, iv.mpf(C_cert), m, hd_pt[1], max_splits=300)[0]:
            break
        C_cert = min(C_t31, C_cert + mp.mpf(f"{max(1e-9, gap_est * 0.05):.14e}"))

    # Pure mpmath.iv contiguous covering of [C_cert, C_t31]
    assert C_cert <= C_t31, f"C_cert={C_cert} exceeds C_t31={C_t31}!"
    covered = []
    stack = [(C_cert, C_t31)]
    while stack:
        ca, cb = stack.pop()
        C_iv = iv.mpf([ca, cb])
        c_mid = 0.5 * float(ca + cb)
        hd = propose_dual_witness(kap_f, Lam0_f * (c_mid ** (2 * kap_f)), m, use_7scalar=True)
        if hd is not None:
            ok, _, _, _ = iv_certify_dual_box(kap_iv, C_iv, m, hd[1], max_splits=350)
            if ok:
                covered.append((ca, cb))
                continue
        assert cb - ca > mp.mpf("1e-13"), f"Interval covering failed on [{ca}, {cb}]!"
        cm = (ca + cb) / 2
        stack.append((cm, cb))
        stack.append((ca, cm))

    # Verify exact contiguity from C_cert to C_t31 in pure mpmath!
    covered.sort(key=lambda pair: pair[0])
    assert covered[0][0] == C_cert and covered[-1][1] == C_t31
    for i in range(len(covered) - 1):
        assert covered[i][1] == covered[i + 1][0], "Gap in certified C-interval covering!"
    return C_cert, len(covered), C_t31


def certify_continuous_p_box(pa, pb, m=2):
    """
    100% zero-float pure mpmath.iv 2D box certification of a constant cap C_p(m) <= C_cap
    valid for EVERY real number p in [pa, pb] and EVERY dimension n >= 1!
    """
    p_iv = iv.mpf([pa, pb])
    kap_iv = p_iv / (2 * (p_iv - 1))
    C_t31_box = iv_thm31_C_ub(kap_iv, m)

    # Heuristic cap just above C_ub at right endpoint pb (since C_p(m) increases with p)
    kap_b = float(pb / (2 * (pb - 1)))
    Lam0_b = 2.0 ** (2 * kap_b - 1)
    C_t31_b = float(iv_thm31_C_ub(iv.mpf(pb) / (2 * (iv.mpf(pb) - 1)), m))
    C_lb_b = iv_rank1_lower_bound(iv.mpf(pb), m, propose_rank1_x1(float(pb), m))
    lo_c = float(C_lb_b)
    hi_c = C_t31_b
    for _ in range(28):
        mid_c = 0.5 * (lo_c + hi_c)
        hd = propose_dual_witness(kap_b, Lam0_b * (mid_c ** (2 * kap_b)), m, use_7scalar=True)
        if hd is not None and hd[0] < hd[2] - 1e-12:
            hi_c = mid_c
        else:
            lo_c = mid_c
    # Pick tight cap well below C_interp(pa) (using adaptive slack!)
    c_interp_pa = float(((1 + mp.sqrt(2)) / 2) ** (1 - 1 / pa))
    slack = min(0.0004, max(1e-5, 0.2 * (c_interp_pa - hi_c)))
    C_cap = mp.mpf(f"{min(float(C_t31_box) - 1e-6, hi_c + slack):.7f}")

    # Adaptive 2D pure-mpmath.iv covering of [pa, pb] x [C_cap, C_t31_box]
    n_boxes = 0
    area_covered = mp.mpf(0)
    stack = [(pa, pb, C_cap, C_t31_box)]
    while stack:
        p1, p2, c1, c2 = stack.pop()
        piv = iv.mpf([p1, p2])
        kiv = piv / (2 * (piv - 1))
        # Early pruning: if Theorem 3.1 ALREADY rules out [c1, c2] on [p1, p2]!
        if c1 >= iv_thm31_C_ub(kiv, m):
            n_boxes += 1
            area_covered += (p2 - p1) * (c2 - c1)
            continue
        civ = iv.mpf([c1, c2])
        pm = float((p1 + p2) / 2)
        km = pm / (2 * (pm - 1))
        cm = float((c1 + c2) / 2)
        hd = propose_dual_witness(km, (2.0 ** (2 * km - 1)) * (cm ** (2 * km)), m, use_7scalar=True)
        if hd is not None:
            ok, _, _, _ = iv_certify_dual_box(kiv, civ, m, hd[1], max_splits=280)
            if ok:
                n_boxes += 1
                area_covered += (p2 - p1) * (c2 - c1)
                continue
        assert (p2 - p1) > mp.mpf("1e-5") or (c2 - c1) > mp.mpf("1e-7"), f"2D box failed on [{p1},{p2}]x[{c1},{c2}]"
        if float(p2 - p1) > 4.0 * float(c2 - c1):
            pm_mp = (p1 + p2) / 2
            stack.append((pm_mp, p2, c1, c2))
            stack.append((p1, pm_mp, c1, c2))
        else:
            cm_mp = (c1 + c2) / 2
            stack.append((p1, p2, cm_mp, c2))
            stack.append((p1, p2, c1, cm_mp))

    # Exact area check confirms partition covers 100% of [pa, pb] x [C_cap, C_t31_box] (disjoint binary tree!)
    total_area = (pb - pa) * (C_t31_box - C_cap)
    assert abs(area_covered - total_area) < mp.mpf("1e-30") * total_area
    return C_cap, n_boxes, C_lb_b


if __name__ == "__main__":
    t_start = time.time()
    print("========================================================================================")
    print("PART A: 100% ZERO-FLOAT mpmath.iv CERTIFICATION OF C_p(m) FOR 12 EXPONENTS x m = 2, 3, 4")
    print("        (RATIONAL & IRRATIONAL p, ALL DIMENSIONS n >= 1, ALL Lam >= Lam_cert!)")
    print("========================================================================================")
    exponents = [
        ("1.1",   iv.mpf("1.1")),
        ("6/5",   iv.mpf(6) / 5),
        ("5/4",   iv.mpf(5) / 4),
        ("4/3",   iv.mpf(4) / 3),
        ("sqrt2", iv.sqrt(2)),
        ("3/2",   iv.mpf(3) / 2),
        ("phi",   (1 + iv.sqrt(5)) / 2),
        ("5/3",   iv.mpf(5) / 3),
        ("1.75",  iv.mpf("1.75")),
        ("1.8",   iv.mpf("1.8")),
        ("1.9",   iv.mpf("1.9")),
        ("1.95",  iv.mpf("1.95")),
    ]
    for m in [2, 3, 4]:
        print(f"\n--- m = {m} ---")
        for label, p_iv in exponents:
            p_mid_f = float((mp.mpf(p_iv.a) + mp.mpf(p_iv.b)) / 2)
            x1_s = propose_rank1_x1(p_mid_f, m)
            C_lb = iv_rank1_lower_bound(p_iv, m, x1_s)
            C_ub, n_box, _ = certify_point_p_m(p_iv, m, C_lb)
            gap = C_ub - C_lb
            assert gap > 0
            if label == "1.9" and m == 2:
                assert gap < mp.mpf("1e-8"), f"Gap at p=1.9, m=2 too large: {gap}"
            if label == "1.95" and m == 2:
                assert gap < mp.mpf("5e-9"), f"Gap at p=1.95, m=2 too large: {gap}"
            if label == "1.95":
                assert gap < mp.mpf("2.5e-8"), f"Gap at p=1.95, m={m} too large: {gap}"
            print(f"  p={label:6s} m={m}: CERTIFIED [{mp.nstr(C_lb, 12)}, {mp.nstr(C_ub, 12)}]  gap={mp.nstr(gap, 3)}  ({n_box:2d} IV boxes)")

    print("\n========================================================================================")
    print("PART B: 100% ZERO-FLOAT mpmath.iv NONCOMMUTING MATRIX KUBO-ANDO LOWER BOUNDS (m = 2)")
    print("        (PROVES C_p(2) > C_{1x1}(p, 2) RIGOROUSLY FOR BOTH RATIONAL & IRRATIONAL p!)")
    print("========================================================================================")
    mat_exponents = [
        ("6/5",   iv.mpf(6) / 5,         mp.mpf(6) / 5),
        ("4/3",   iv.mpf(4) / 3,         mp.mpf(4) / 3),
        ("sqrt2", iv.sqrt(2),            mp.sqrt(2)),
        ("3/2",   iv.mpf(3) / 2,         mp.mpf(3) / 2),
        ("phi",   (1 + iv.sqrt(5)) / 2,  (1 + mp.sqrt(5)) / 2),
        ("5/3",   iv.mpf(5) / 3,         mp.mpf(5) / 3),
    ]
    for label, p_iv, p_mp in mat_exponents:
        C_1x1_ub = iv_rank1_upper_bound(p_iv, 2)
        w = propose_rank2_matrix_witness(p_mp, m=2, L_dep=3)
        C_lb_mat = iv_matrix_kubo_ando_lb(p_iv, 2, *w)
        gain = mp.mpf((iv.mpf(C_lb_mat) - iv.mpf(C_1x1_ub)).a)
        assert C_lb_mat > C_1x1_ub and gain > 0, f"Matrix LB did not rigorously beat C_1x1_ub at p={label}!"
        print(f"  p={label:6s} (dim=8): C_1x1_ub={mp.nstr(C_1x1_ub, 13)} < CERTIFIED C_mat={mp.nstr(C_lb_mat, 13)}  (certified gain>+{mp.nstr(gain, 3)})")

    print("\n========================================================================================")
    print("PART C: 100% ZERO-FLOAT CONTINUOUS p-INTERVAL ENVELOPE COVERING ALL p IN [1.50, 1.99]")
    print("        (m = 2, STRICTLY BEATS RIESZ-THORIN COMPLEX INTERPOLATION AT EVERY p!)")
    print("========================================================================================")
    p_grid = ([mp.mpf(iv.mpf("1.50").a)]
              + [mp.mpf(s) for s in ["1.55", "1.60", "1.65", "1.70", "1.75", "1.80", "1.85", "1.90", "1.93", "1.96", "1.975", "1.985"]]
              + [mp.mpf(iv.mpf("1.99").b)])
    assert p_grid[0] <= mp.mpf(iv.mpf("1.50").a) and p_grid[-1] >= mp.mpf(iv.mpf("1.99").b)
    total_2d_boxes = 0
    for i in range(len(p_grid) - 1):
        pa, pb = p_grid[i], p_grid[i + 1]
        C_cap, n_b, C_lb_b = certify_continuous_p_box(pa, pb, m=2)
        total_2d_boxes += n_b
        # Pure mpmath.iv check that C_cap < C_interp(pa) <= C_interp(p) for ALL p in [pa, pb]!
        C_interp_pa_lo = mp.mpf(iv_pow_nonneg((1 + iv.sqrt(2)) / 2, 1 - 1 / iv.mpf(pa)).a)
        assert C_cap < C_interp_pa_lo, f"Cap {C_cap} did not beat C_interp({pa})={C_interp_pa_lo}!"
        print(f"  p in [{mp.nstr(pa, 5):5s}, {mp.nstr(pb, 5):5s}]: CERTIFIED C_p(2) <= {mp.nstr(C_cap, 8)} < C_interp(pa)={mp.nstr(C_interp_pa_lo, 8)}  ({n_b:3d} 2D IV boxes)")
    print(f"\nALL ZERO-FLOAT mpmath.iv CERTIFICATIONS PASSED (total 2D boxes={total_2d_boxes}, elapsed={time.time()-t_start:.1f}s)!")
