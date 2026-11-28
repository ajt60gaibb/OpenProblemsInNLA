r"""
================================================================================
100% ZERO-FLOAT, PURE mpmath.iv GLOBAL COMPLEX-INTERPOLATION ENVELOPE FOR MI-20
(ALL 1 < p < 2, m = 2, 3, 4, ALL MATRIX DIMENSIONS n >= 1)

ZERO `float()`, ZERO `numpy`, ZERO `scipy` ANYWHERE IN THIS ENTIRE FILE!

MATHEMATICAL FOUNDATIONS (100% SELF-CONTAINED):
  1) Exact Endpoints:
     - p = 1: C_1(m) = 1 (triangle inequality ||sum A_j||_1 <= sum ||A_j||_1 = Tr(sum |A_j|)).
     - p = 2: C_2(m) = sqrt((1 + sqrt(m))/2) (exact 5-line proof:
       |Tr(A_i^* A_j)| <= ||B_j B_i||_1 <= ||B_i||_2^{1/2} ||B_j||_2^{1/2} Tr(B_i B_j)^{1/2}
       => ||sum A_j||_2^2 <= T_0 + sqrt((m-1) T_0 T_1) <= ((1 + sqrt(m))/2) (T_0 + T_1)).

  2) Complex Interpolation Theorem (Log-Convexity of 1/p -> log C_p(m)):
     For any 1 <= p_0 < p < p_1 <= 2, m >= 2, n >= 1, and any A_j = U_j B_j with B_j > 0,
     S := sum_j B_j normalized to ||S||_p = 1, W_j := S^{-1/2} B_j S^{-1/2} (sum W_j = I_n),
     and dual matrix Y = V |Y| with ||Y||_{p'} = 1, define on 0 <= Re(z) <= 1:
       1/p(z) := (1-z)/p_0 + z/p_1,   1/p'(z) := 1 - 1/p(z),
       A_j(z) := U_j S^{p/(2 p(z))} W_j S^{p/(2 p(z))},
       F(z)   := Tr(|Y|^{p'/p'(z)} V^* sum_j A_j(z)).
     On Re(z) = k in {0, 1}, S^{i p gamma t / 2} =: V_t is unitary, so
       |A_j(k + i t)| = V_t^* (S^{p/(2 p_k)} W_j S^{p/(2 p_k)}) V_t,
       sum_j |A_j(k + i t)| = V_t^* S^{p/p_k} V_t  ==>  ||sum |A_j(k + i t)|||_{p_k} = 1,
     hence |F(k + i t)| <= C_{p_k}(m). By Hadamard's Three-Lines Theorem at z = theta
     where theta = (1/p_0 - 1/p) / (1/p_0 - 1/p_1) = p_1 (p - p_0) / (p (p_1 - p_0)):
       C_p(m) <= C_{p_0}(m)^{1 - theta} * C_{p_1}(m)^{theta}.

  3) Certified Dimension-Free Anchors at p in {1, 6/5, 5/4, 4/3, 3/2, 5/3, 2}:
     - p = 6/5, 5/4, 3/2, 5/3: certified in `rigorous_iv_multi_p_bounds.py` (ALL Lam >= Lam_cert!)
     - p = 4/3: upper-bound anchors ("8.60430", "9.06945", "9.46060") from `rigorous_iv_proof_p43.py`
       (whose single-Lam -> all-Lam monotonicity bridge is closed unconditionally by
       `rigorous_iv_p43_all_m_part1.py` & `part2.py`), lower bounds from `rigorous_iv_lower_bounds_p43.py`
     - Prior baseline for comparison:
       * m = 2: Holden's prior curve anchored at {1, 4/3 (<= 1.01854047), 2}
       * m = 3, 4: classical {1, 2} interpolation curve ((1 + sqrt(m))/2)^{1 - 1/p}

  4) Universal Explicit m x m Matrix Lower Bound (ALL real p in [1, 2], ALL m >= 2):
     For T = diag(x, 1, ..., 1) (x > 1), DFT projections P_k = f_k f_k^*, and A_k = T^{a/2} P_k T^{b/2}
     (any a > b > 0):
       ||sum A_k||_p^p = x^{p(a+b)/2} + m - 1,
       ||sum |A_k|||_p^p = ((x^a + m - 1)/(x^b + m - 1))^{p/2} (x^{p b} + m - 1),
     giving the 100% explicit, singularity-free lower bound for EVERY p in [1, 2]:
       C_p(m) >= ((x^{p(a+b)/2} + m - 1)/(x^{p b} + m - 1))^{1/p} * ((x^b + m - 1)/(x^a + m - 1))^{1/2}.
     (For optimal p in (1, 2), a/b = p/(2-p) recovers Holden's exact 1x1 scalar solution;
      near p = 2, fixed b = 1, a = 80, x = 1 + sqrt(m) is smooth up to p = 2 with ZERO 1/(2-p) blowup!)

THEOREMS CERTIFIED BY THIS SCRIPT (100% PURE mpmath.iv, ZERO FLOATS):
  G1. Strict Log-Convexity of All 7 Anchors (every interior rational anchor strictly beats
      interpolation from its neighbors -> 0 redundant anchors!).
  G2. Strict Global Dominance Over Holden's Prior Curve for EVERY real p in (1, 2)
      (exact piecewise-linear log-dominance at every breakpoint -> holds on ALL of (1, 2)!).
  G3. Uniform Global Continuum Enclosure Gap sup_{p in [1, 2]} (U_new(p; m) - L(p; m))
      certified over the ENTIRE continuous interval [1, 2] with zero uncovered cracks!
  G4. Certified Two-Sided Enclosure Table at 15 exponents across (1, 2) for m = 2, 3, 4.
================================================================================
"""

import time
import mpmath as mp
from mpmath import iv

mp.mp.dps = 55
iv.dps = 50


# ==============================================================================
# CERTIFIED ANCHOR DATA (EXACT STRINGS / RATIONALS -> OUTWARD-ROUNDED mpmath.iv)
# ==============================================================================
# Exact certified Lam_cert upper bounds from rigorous_iv_multi_p_bounds.py & rigorous_iv_proof_p43.py:
#   C_p(m) <= (Lam_cert / 2^{2k-1})^{1/(2k)},  kappa = p/(2(p-1)).
CERTIFIED_LAM_UB = {
    # p_key: (p_num, p_den, k_num, k_den, {m: Lam_cert_str})
    "6/5": (6, 5, 3, 1, {2: "33.4505",  3: "34.5515",  4: "35.4668"}),
    "5/4": (5, 4, 5, 2, {2: "16.9073",  3: "17.5995",  4: "18.1790"}),
    "4/3": (4, 3, 2, 1, {2: "8.60430",  3: "9.06945",  4: "9.46060"}),
    "3/2": (3, 2, 3, 2, {2: "4.453377", 3: "4.806190", 4: "5.105198"}),
    "5/3": (5, 3, 5, 4, {2: "3.251598", 3: "3.580802", 4: "3.859845"}),
}

# Exact certified multi-matrix Kubo-Ando lower bounds (rounded DOWNWARD at 13th digit!)
# from rigorous_iv_multi_p_bounds.py and rigorous_iv_lower_bounds_p43.py:
CERTIFIED_MULTI_LB = {
    "6/5": {2: "1.007397668918",  3: "1.012830139513",  4: "1.017237089278"},
    "5/4": {2: "1.011065979791",  3: "1.019193263924",  4: "1.025787707117"},
    "4/3": {2: "1.018371575517",  3: "1.031863848072",  4: "1.042812616134"},
    "3/2": {2: "1.036437168065",  3: "1.063114500990",  4: "1.084719139101"},
    "5/3": {2: "1.057348913859",  3: "1.098935623593",  4: "1.132421930734"},
}

HOLDEN_P43_M2_UB = "1.01854047"


def iv_C2(m):
    """Exact C_2(m) = sqrt((1 + sqrt(m))/2) in mpmath.iv."""
    return iv.sqrt((iv.mpf(1) + iv.sqrt(iv.mpf(m))) / iv.mpf(2))


def iv_C_from_Lam(Lam_str, k_num, k_den):
    k_iv = iv.mpf(k_num) / iv.mpf(k_den)
    return (iv.mpf(Lam_str) / (iv.mpf(2) ** (2 * k_iv - 1))) ** (iv.mpf(1) / (2 * k_iv))


def build_anchors_in_t(m, prior=False):
    """
    Returns anchors sorted by ascending t = 1/p in [1/2, 1]:
      [(label, t_iv, p_iv, U_iv), ...]
    where U_iv is a rigorous interval enclosing the certified upper bound U_i >= C_{p_i}(m).
    """
    C2_iv = iv_C2(m)
    if prior:
        anchors = [("2", iv.mpf(1) / iv.mpf(2), iv.mpf(2), C2_iv)]
        if m == 2:
            anchors.append(("4/3", iv.mpf(3) / iv.mpf(4), iv.mpf(4) / iv.mpf(3), iv.mpf(HOLDEN_P43_M2_UB)))
        anchors.append(("1", iv.mpf(1), iv.mpf(1), iv.mpf(1)))
        return anchors

    anchors = [("2", iv.mpf(1) / iv.mpf(2), iv.mpf(2), C2_iv)]
    for key in ["5/3", "3/2", "4/3", "5/4", "6/5"]:
        pn, pd, kn, kd, lmap = CERTIFIED_LAM_UB[key]
        t_iv = iv.mpf(pd) / iv.mpf(pn)
        p_iv = iv.mpf(pn) / iv.mpf(pd)
        U_iv = iv_C_from_Lam(lmap[m], kn, kd)
        anchors.append((key, t_iv, p_iv, U_iv))
    anchors.append(("1", iv.mpf(1), iv.mpf(1), iv.mpf(1)))
    return anchors


def iv_log_interp_on_segment(t_iv, t0_iv, U0_iv, t1_iv, U1_iv):
    """
    Outward-rounded mpmath.iv enclosure of log-linear interpolation in t = 1/p on [t0, t1]:
      log U(t) = (1 - theta) log U0 + theta log U1,   theta = (t - t0)/(t1 - t0) in [0, 1].
    Strictly asserts theta in [0, 1] with ZERO clamping!
    """
    theta = (t_iv - t0_iv) / (t1_iv - t0_iv)
    assert mp.mpf(theta.a) >= 0 and mp.mpf(theta.b) <= 1, f"theta={theta} outside [0, 1]!"
    return (iv.mpf(1) - theta) * iv.log(U0_iv) + theta * iv.log(U1_iv)


def iv_eval_envelope_t(t_iv, anchors):
    """
    Evaluate piecewise log-linear upper-bound envelope at t_iv (which MUST lie within
    a single adjacent segment [t_i, t_{i+1}] — or we take min over all bracketing pairs!).
    Returns U_iv enclosing U(1/t) for ALL t in t_iv.
    """
    # Exact anchor match check first
    for _, ti, _, Ui in anchors:
        if mp.mpf(ti.a) <= mp.mpf(t_iv.a) and mp.mpf(t_iv.b) <= mp.mpf(ti.b):
            return Ui
    # Otherwise find tightest bracketing pair [ti, tj] containing t_iv!
    best_hi = None
    best_iv = None
    for i in range(len(anchors)):
        ti, Ui = anchors[i][1], anchors[i][3]
        if mp.mpf(ti.b) <= mp.mpf(t_iv.a):
            for j in range(i + 1, len(anchors)):
                tj, Uj = anchors[j][1], anchors[j][3]
                if mp.mpf(tj.a) >= mp.mpf(t_iv.b):
                    val = iv.exp(iv_log_interp_on_segment(t_iv, ti, Ui, tj, Uj))
                    if best_hi is None or mp.mpf(val.b) < best_hi:
                        best_hi = mp.mpf(val.b)
                        best_iv = val
    assert best_iv is not None, f"t_iv={t_iv} not bracketed by anchors!"
    return best_iv


def iv_matrix_lb_fixed_ab(p_iv, m, a_iv, b_iv, x_iv):
    """
    100% pure zero-float mpmath.iv explicit m x m matrix lower bound for ANY p_iv subset [1, 2],
    ANY a > b > 0, and ANY x > 1 (ZERO 1/(2-p) singularity AND ZERO x^{p b} wrapping!):
      Factoring out x^{(a+b)/2} * x^{b/2} = x^{a/2 + b} from numerator and denominator cancels ALL leading x-powers:
      C_p(m) >= ((1 + (m-1)*x^{-p(a+b)/2}) / (1 + (m-1)*x^{-p b}))^{1/p}
                * ((1 + (m-1)*x^{-b}) / (1 + (m-1)*x^{-a}))^{1/2}.
    """
    m1 = iv.mpf(m - 1)
    half = iv.mpf(1) / iv.mpf(2)
    inv_p = iv.mpf(1) / p_iv
    num1 = iv.mpf(1) + m1 * (x_iv ** (-p_iv * (a_iv + b_iv) * half))
    den1 = iv.mpf(1) + m1 * (x_iv ** (-p_iv * b_iv))
    num2 = iv.mpf(1) + m1 * (x_iv ** (-b_iv))
    den2 = iv.mpf(1) + m1 * (x_iv ** (-a_iv))
    val = ((num1 / den1) ** inv_p) * iv.sqrt(num2 / den2)
    return mp.mpf(val.a)


def iv_opt_matrix_lb_on_tbox(t_lo, t_hi, m):
    """
    100% pure zero-float mpmath.iv lower bound valid for EVERY t in [t_lo, t_hi] (p = 1/t in [1/t_hi, 1/t_lo])!
    Chooses optimal (a, b, x) at t_mid in pure mpmath, then evaluates the EXACT fixed-(a, b, x)
    explicit m x m matrix formula over the ENTIRE interval p_box = 1 / [t_lo, t_hi]!
    """
    t_box = iv.mpf([t_lo, t_hi])
    p_box = iv.mpf(1) / t_box
    t_mid = (t_lo + t_hi) / 2
    p_mid = mp.mpf(1) / t_mid

    # Near p = 1 (t > 0.995): trivial 1x1 identity gives C_p(m) >= 1!
    if t_lo >= mp.mpf("0.995"):
        return mp.mpf(1)

    # Near p = 2 (t < 0.505): fixed b=1, a=120, x = 1 + sqrt(m) is smooth up to p = 2!
    if t_hi <= mp.mpf("0.51"):
        a_iv = iv.mpf(120); b_iv = iv.mpf(1)
        x_iv = iv.mpf(1) + iv.sqrt(iv.mpf(m))
        return max(mp.mpf(1), iv_matrix_lb_fixed_ab(p_box, m, a_iv, b_iv, x_iv))

    # Interior (1, 2): pick exact optimal s = p_mid / (2 - p_mid), b = 1, a = s, optimize x = exp(u) by golden section!
    s_m = p_mid / (2 - p_mid)
    def f_pt(u):
        ex = mp.exp(u)
        return ((mp.exp(s_m * u) + m - 1) ** (1 / p_mid - mp.mpf("0.5"))
                * mp.sqrt(ex + m - 1)
                / ((mp.exp(p_mid * u) + m - 1) ** (1 / p_mid)))
    lo_u, hi_u = mp.mpf("0.01"), mp.mpf("10.0")
    gr = (mp.sqrt(5) - 1) / 2
    for _ in range(70):
        c = hi_u - gr * (hi_u - lo_u); d = lo_u + gr * (hi_u - lo_u)
        if f_pt(c) > f_pt(d): hi_u = d
        else: lo_u = c
    x_opt = iv.mpf(mp.exp((lo_u + hi_u) / 2))
    a_opt = iv.mpf(s_m); b_opt = iv.mpf(1)
    lb = iv_matrix_lb_fixed_ab(p_box, m, a_opt, b_opt, x_opt)
    return max(mp.mpf(1), lb)


# ==============================================================================
# THEOREM G1: STRICT LOG-CONVEXITY OF ALL 7 ANCHORS (ZERO REDUNDANT ANCHORS!)
# ==============================================================================
def certify_theorem_G1(m):
    anchors = build_anchors_in_t(m, prior=False)
    slopes = []
    for i in range(len(anchors) - 1):
        lbl0, t0, _, U0 = anchors[i]
        lbl1, t1, _, U1 = anchors[i + 1]
        s_iv = (iv.log(U1) - iv.log(U0)) / (t1 - t0)
        assert mp.mpf(s_iv.b) < 0, f"Slope not negative on [{lbl0}, {lbl1}]!"
        slopes.append((lbl0, lbl1, s_iv))
    # Verify strict convexity: s_0 < s_1 < s_2 < s_3 < s_4 < s_5 < 0!
    min_jump = None
    for i in range(len(slopes) - 1):
        jump = mp.mpf((slopes[i + 1][2] - slopes[i][2]).a)
        assert jump > 0, f"Convexity failed at anchor {anchors[i+1][0]}: jump={jump}"
        if min_jump is None or jump < min_jump:
            min_jump = jump
    # Also quantify how much each interior anchor beats interpolation from its immediate neighbors!
    print(f"\n[THEOREM G1 PASS | m = {m}] ALL 7 ANCHORS STRICTLY LOG-CONVEX IN t = 1/p (min slope jump = +{mp.nstr(min_jump, 4)})!")
    for i in range(1, len(anchors) - 1):
        lbl, ti, _, Ui = anchors[i]
        t_prev, U_prev = anchors[i - 1][1], anchors[i - 1][3]
        t_next, U_next = anchors[i + 1][1], anchors[i + 1][3]
        U_nbr = iv.exp(iv_log_interp_on_segment(ti, t_prev, U_prev, t_next, U_next))
        improv = mp.mpf((U_nbr - Ui).a)
        assert improv > 0, f"Anchor p={lbl} did not beat neighbor interpolation!"
        print(f"    p = {lbl:3s} (t={mp.nstr(mp.mpf(ti.mid), 5)}): U_cert <= {mp.nstr(mp.mpf(Ui.b), 12)}  "
              f"vs neighbor-secant >= {mp.nstr(mp.mpf(U_nbr.a), 12)}  (beats by +{mp.nstr(improv, 4)}!)")


# ==============================================================================
# THEOREM G2: STRICT GLOBAL DOMINANCE OVER HOLDEN'S PRIOR CURVE ON ALL (1, 2)!
# ==============================================================================
def certify_theorem_G2(m):
    anc_new = build_anchors_in_t(m, prior=False)
    anc_pri = build_anchors_in_t(m, prior=True)
    prior_desc = "Holden {1, 4/3<=1.01854047, 2}" if m == 2 else "Classical {1, 2}"
    print(f"\n[THEOREM G2 PASS | m = {m}] STRICT GLOBAL IMPROVEMENT OVER {prior_desc} FOR ALL REAL p in (1, 2):")

    # All interior breakpoints of BOTH piecewise log-linear curves are the 5 interior anchors of anc_new!
    best_abs = mp.mpf(0); best_abs_p = ""
    best_rel = mp.mpf(0); best_rel_p = ""
    for i in range(1, len(anc_new) - 1):
        lbl, ti, _, U_new = anc_new[i]
        U_pri = iv_eval_envelope_t(ti, anc_pri)
        log_diff = iv.log(U_pri) - iv.log(U_new)
        assert mp.mpf(log_diff.a) > 0, f"Dominance failed at p={lbl}!"
        abs_drop = mp.mpf((U_pri - U_new).a)
        rel_exc_red = mp.mpf(((U_pri - U_new) / (U_pri - iv.mpf(1))).a) * 100
        if abs_drop > best_abs:
            best_abs = abs_drop; best_abs_p = lbl
        if rel_exc_red > best_rel:
            best_rel = rel_exc_red; best_rel_p = lbl
        print(f"    p = {lbl:3s}: U_new <= {mp.nstr(mp.mpf(U_new.b), 11)}  <  U_prior >= {mp.nstr(mp.mpf(U_pri.a), 11)}  "
              f"| drop >= {mp.nstr(abs_drop, 4)}  ({mp.nstr(rel_exc_red, 4)}% of prior excess C-1!)")
    print(f"    ==> By piecewise log-linearity in t = 1/p, U_new(p; {m}) < U_prior(p; {m}) STRICTLY for EVERY real p in (1, 2)!")
    print(f"    ==> Peak certified drop at anchor p={best_abs_p}: -{mp.nstr(best_abs, 4)} | Peak excess reduction at p={best_rel_p}: {mp.nstr(best_rel, 4)}%")


# ==============================================================================
# THEOREM G3: UNIFORM GLOBAL CONTINUUM ACCURACY OVER ALL REAL p in [1, 2]!
# ==============================================================================
def certify_theorem_G3(m, n_sub_per_seg=100):
    anc_new = build_anchors_in_t(m, prior=False)
    anc_pri = build_anchors_in_t(m, prior=True)

    # Explicitly assert strict monotonicity (decreasing in t) on every segment!
    for seg_i in range(len(anc_new) - 1):
        t0_iv, U0_iv = anc_new[seg_i][1], anc_new[seg_i][3]
        t1_iv, U1_iv = anc_new[seg_i + 1][1], anc_new[seg_i + 1][3]
        s_iv = (iv.log(U1_iv) - iv.log(U0_iv)) / (t1_iv - t0_iv)
        assert mp.mpf(s_iv.b) < 0, f"Segment {seg_i} not strictly decreasing in t!"

    worst_new_gap = mp.mpf(0); worst_new_loc = None
    worst_pri_gap_lb = mp.mpf(0); worst_pri_loc = None

    # Exact crack-free decomposition of [1/2, 1]:
    #   For each segment seg_i connecting anchor t_i in [t_i.a, t_i.b] to t_{i+1} in [t_{i+1}.a, t_{i+1}.b]:
    #     1) Interior [t_i.b, t_{i+1}.a]: strictly inside [t_i, t_{i+1}] => strict=True (zero clamping!)
    #     2) Seam [t_{i+1}.a, t_{i+1}.b] (for interior anchors): every t >= t_{i+1}.a, and t_{i+1}.a <= t_{i+1}
    #        lies strictly inside [t_i, t_{i+1}], so by strict monotonicity U_new(1/t) <= U_new(1/t_{i+1}.a)!
    covered_boxes = []
    for seg_i in range(len(anc_new) - 1):
        t0_iv, U0_iv = anc_new[seg_i][1], anc_new[seg_i][3]
        t1_iv, U1_iv = anc_new[seg_i + 1][1], anc_new[seg_i + 1][3]
        tA = mp.mpf(t0_iv.b)
        tB = mp.mpf(t1_iv.a)
        assert tA < tB
        edges = [tA + (tB - tA) * k / n_sub_per_seg for k in range(n_sub_per_seg + 1)]
        edges[0] = tA; edges[-1] = tB

        # Subintervals strictly inside [t0_iv.b, t1_iv.a] (ZERO clamping!)
        for k in range(n_sub_per_seg):
            tl = edges[k]; th = edges[k + 1]
            U_new_hi = mp.mpf(iv.exp(iv_log_interp_on_segment(iv.mpf(tl), t0_iv, U0_iv, t1_iv, U1_iv)).b)
            L_box_lo = iv_opt_matrix_lb_on_tbox(tl, th, m)
            gap_ub = mp.mpf((iv.mpf(U_new_hi) - iv.mpf(L_box_lo)).b)
            assert gap_ub > 0, f"Impossible: L_box_lo >= U_new_hi on t in [{tl}, {th}]!"
            if gap_ub > worst_new_gap:
                worst_new_gap = gap_ub
                worst_new_loc = (mp.mpf(1) / th, mp.mpf(1) / tl)
            tm = (tl + th) / 2
            U_pri_lo = mp.mpf(iv_eval_envelope_t(iv.mpf(tm), anc_pri).a)
            U_new_mid_hi = mp.mpf(iv.exp(iv_log_interp_on_segment(iv.mpf(tm), t0_iv, U0_iv, t1_iv, U1_iv)).b)
            pri_err_lb = mp.mpf((iv.mpf(U_pri_lo) - iv.mpf(U_new_mid_hi)).a)
            if pri_err_lb > worst_pri_gap_lb:
                worst_pri_gap_lb = pri_err_lb
                worst_pri_loc = mp.mpf(1) / tm
            covered_boxes.append((tl, th))

        # Tiny seam [t1_iv.a, t1_iv.b] if non-degenerate (for non-dyadic rational anchors like 3/5, 2/3, 4/5, 5/6)
        if mp.mpf(t1_iv.a) < mp.mpf(t1_iv.b):
            tl = mp.mpf(t1_iv.a); th = mp.mpf(t1_iv.b)
            # Pick t_ref = tl - 1e-20 strictly inside (t0_iv.b, t1_iv.a):
            #   theta(t_ref) is strictly inside (0, 1) (ZERO clamping!), and since t_ref < tl <= t
            #   and U_new(1/t) is strictly decreasing in t, U_new(1/t) <= U_new(1/t_ref) for ALL t in [tl, th]!
            t_ref = tl - mp.mpf("1e-20")
            assert mp.mpf(t0_iv.b) < t_ref < tl
            U_new_hi = mp.mpf(iv.exp(iv_log_interp_on_segment(iv.mpf(t_ref), t0_iv, U0_iv, t1_iv, U1_iv)).b)
            L_box_lo = iv_opt_matrix_lb_on_tbox(tl, th, m)
            gap_ub = mp.mpf((iv.mpf(U_new_hi) - iv.mpf(L_box_lo)).b)
            assert gap_ub > 0
            if gap_ub > worst_new_gap:
                worst_new_gap = gap_ub
                worst_new_loc = (mp.mpf(1) / th, mp.mpf(1) / tl)
            covered_boxes.append((tl, th))

    # Assert 100% exact crack-free contiguous coverage of [1/2, 1]!
    assert covered_boxes[0][0] == mp.mpf("0.5") and covered_boxes[-1][1] == mp.mpf("1.0")
    for i in range(len(covered_boxes) - 1):
        assert covered_boxes[i][1] == covered_boxes[i + 1][0], f"Crack between {covered_boxes[i]} and {covered_boxes[i+1]}!"

    ratio_lb = mp.mpf((iv.mpf(worst_pri_gap_lb) / iv.mpf(worst_new_gap)).a)
    print(f"\n[THEOREM G3 PASS | m = {m}] CONTINUUM COVERAGE OF ALL p in [1, 2] ({len(covered_boxes)} contiguous iv-boxes, 0 cracks):")
    print(f"    CERTIFIED UNIFORM GLOBAL GAP:  sup_{{p in [1,2]}} (U_new(p; {m}) - C_p({m})) <= {mp.nstr(worst_new_gap, 5)} "
          f"(worst box p in [{mp.nstr(worst_new_loc[0], 5)}, {mp.nstr(worst_new_loc[1], 5)}])")
    print(f"    vs PRIOR CURVE ERROR:          sup_{{p in [1,2]}} (U_prior(p; {m}) - C_p({m})) >= {mp.nstr(worst_pri_gap_lb, 5)} "
          f"(at p = {mp.nstr(worst_pri_loc, 5)})  ==>  >= {mp.nstr(ratio_lb, 3)}x GLOBAL GAP REDUCTION!!")
    return worst_new_gap, worst_pri_gap_lb


# ==============================================================================
# THEOREM G4: CERTIFIED ENCLOSURE TABLE AT 15 EXPONENTS ACROSS (1, 2)
# ==============================================================================
def certify_table_G4(m):
    anc_new = build_anchors_in_t(m, prior=False)
    anc_pri = build_anchors_in_t(m, prior=True)
    pts = [
        ("1.05", 21, 20), ("1.10", 11, 10), ("1.15", 23, 20),
        ("6/5",   6,  5), ("5/4",   5,  4), ("1.30", 13, 10),
        ("4/3",   4,  3), ("1.40",  7,  5), ("3/2",   3,  2),
        ("1.60",  8,  5), ("5/3",   5,  3), ("1.75",  7,  4),
        ("1.80",  9,  5), ("1.90", 19, 10), ("1.95", 39, 20),
    ]
    print(f"\n[THEOREM G4 | m = {m}] CERTIFIED TWO-SIDED ENCLOSURES ACROSS (1, 2) (ALL n >= 1):")
    print(f"  {'p':>5s} | {'Certified LB':>16s} | {'NEW U_new(p)':>16s} | {'PRIOR U_pri(p)':>16s} | {'Gap U-L':>10s} | {'Drop vs Prior':>13s}")
    print("  " + "-" * 89)
    for lbl, pn, pd in pts:
        t_iv = iv.mpf(pd) / iv.mpf(pn)
        U_new_iv = iv_eval_envelope_t(t_iv, anc_new)
        U_pri_iv = iv_eval_envelope_t(t_iv, anc_pri)
        U_new_hi = mp.mpf(U_new_iv.b)
        U_pri_lo = mp.mpf(U_pri_iv.a)
        # Use certified multi-matrix LB at anchors (outward-rounded downward via .a!), explicit m x m matrix LB over EXACT t_iv elsewhere!
        if lbl in CERTIFIED_MULTI_LB:
            LB_lo = mp.mpf(iv.mpf(CERTIFIED_MULTI_LB[lbl][m]).a)
        else:
            LB_lo = iv_opt_matrix_lb_on_tbox(mp.mpf(t_iv.a), mp.mpf(t_iv.b), m)
        assert LB_lo < U_new_hi < U_pri_lo, f"Ordering failed at p={lbl}, m={m}!"
        gap = mp.mpf((iv.mpf(U_new_hi) - iv.mpf(LB_lo)).b)
        drop = mp.mpf((iv.mpf(U_pri_lo) - iv.mpf(U_new_hi)).a)
        tag = "*" if lbl in CERTIFIED_MULTI_LB else " "
        print(f"  {lbl:>4s}{tag} | {mp.nstr(LB_lo, 13):>16s} | {mp.nstr(U_new_hi, 13):>16s} | {mp.nstr(U_pri_lo, 13):>16s} | "
              f"{mp.nstr(gap, 3):>10s} | -{mp.nstr(drop, 3):>12s}")


if __name__ == "__main__":
    t0 = time.time()
    print("================================================================================")
    print("100% ZERO-FLOAT mpmath.iv GLOBAL COMPLEX-INTERPOLATION CERTIFICATION (1 < p < 2)")
    print("================================================================================")
    for m in [2, 3, 4]:
        print(f"\n################################################################################")
        print(f"###  m = {m}   (C_1({m}) = 1,  C_2({m}) = {mp.nstr(mp.mpf(iv_C2(m).mid), 15)})")
        print(f"################################################################################")
        certify_theorem_G1(m)
        certify_theorem_G2(m)
        certify_theorem_G3(m, n_sub_per_seg=100)
        certify_table_G4(m)
    print(f"\nALL GLOBAL INTERPOLATION THEOREMS G1-G4 CERTIFIED WITH ZERO FLOATS! ({time.time()-t0:.2f}s)")
