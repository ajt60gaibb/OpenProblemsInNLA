"""
100% ZERO-FLOAT, ZERO-GAP mpmath.iv CERTIFICATION OF THE ALL-m THEOREM AT p = 4/3 (PART 1: MODULES 0, 1, 2):

  MODULE 0 (All m >= 2 lower bound on Lam_*(m)):
    Certifies K_0(1/5, 1/5) > 2 * sig_+(a) for ALL a in (1, 1.1407],
    proving Lam_*(m) > 8.599 (i.e. a_*(m) > 1.1407) for EVERY integer m >= 2.

  MODULE 1 (All-Lambda 3x3 Scalar Hankel bound & uniform (eps, tau) box):
    Certifies for EVERY Lam >= 8.599 (compact lam = 1/Lam in [0, 1/8.599]):
      L_hank(Lam) <= 1 / (Lam - c(lam)),   c(lam) := 2.40 + 3.75 * lam,
    and combining with the 1-point lower bound T_0 - sig_+ >= K_0(x_1, x_1) - sig_+ (x_1 = 1/(Lam - 3.6)):
      delta_max(m) <= delta_ub(a)  ==>  eps <= 0.51  AND  tau = a * eps <= 1.06
    for EVERY m >= 2 and EVERY delta in (0, delta_max(m)]!

  MODULE 2 (Universal positivity of Q_tilde(z) for ALL n >= 0, ALL m >= 2, ALL delta in (0, delta_max(m)]):
    Certifies on the compact 2D triangle 0 <= eps <= tau <= 1.06, eps <= 0.51 (with c_e = 5.25, c_g = 0.32):
      c_n(eps, tau) > 0  for EVERY integer n >= 0!
    Hence M_tilde_delta >=_{PSD} 0 SIMULTANEOUSLY for EVERY m >= 2 and EVERY delta in (0, delta_max(m)]!
"""

import time
import mpmath as mp
from mpmath import iv

mp.mp.dps = 35
iv.dps = 30

C_E = iv.mpf("5.25")
C_G = iv.mpf("0.32")


def iv_pos(x):
    return iv.mpf([max(mp.mpf(0), mp.mpf(x.a)), max(mp.mpf(0), mp.mpf(x.b))])


def iv_hull(box, pt):
    return iv.mpf([min(mp.mpf(box.a), pt), max(mp.mpf(box.b), pt)])


# ============================================================================
# MODULE 0: Certify K_0(1/5, 1/5) > 2 * sig_+(a) for ALL a in (1, 1.1407]
# ============================================================================
def certify_module_0():
    t0 = time.time()
    # In a in [1, 1.1407]: Lam(a) = (1+a)^3 / a, sig_+(a) = a^2 - a.
    # At x = 1/5: (1+x)^2 = 36/25, x^2 = 1/25.
    # K_0(1/5, 1/5) - 2*sig_+(a) = (36/25)/(Lam(a) - 36/25) - 1/25 - (a^2 - a).
    # Notice Lam(a) = a^2 + 3a + 3 + 1/a is strictly increasing on a >= 1 (derivative 2a + 3 - 1/a^2 > 0),
    # and a^2 - a is strictly increasing on a >= 1!
    # Therefore K_0(1/5, 1/5) - 2*sig_+(a) is STRICTLY DECREASING on [1, 1.1407]!
    # Checking its value at the right endpoint a = 1.1407 (and checking monotonicity via interval derivative) suffices!
    a_box = iv.mpf(["1.0", "1.1407"])
    dLam_da = 2 * a_box + 3 - 1 / (a_box ** 2)
    dsig_da = 2 * a_box - 1
    assert mp.mpf(dLam_da.a) > 0 and mp.mpf(dsig_da.a) > 0, "Monotonicity failed!"

    a_hi = iv.mpf("1.1407")
    Lam_hi = (1 + a_hi) ** 3 / a_hi
    p1 = iv.mpf(36) / iv.mpf(25)
    x1sq = iv.mpf(1) / iv.mpf(25)
    sig_hi = a_hi * a_hi - a_hi
    margin = p1 / (Lam_hi - p1) - x1sq - sig_hi
    assert mp.mpf(margin.a) > 0, f"Module 0 endpoint failed: margin={margin}"
    assert mp.mpf(Lam_hi.a) > mp.mpf(iv.mpf("8.599").b), f"Module 0 Lam_hi link failed: Lam_hi={Lam_hi}"
    print(f"[MODULE 0 PASS] All a in (1, 1.1407]: dLam/da > {float(dLam_da.a):.3f} > 0, "
          f"K_0(1/5,1/5) - 2*sig_+(1.1407) >= +{float(margin.a):.6e} > 0  ({time.time()-t0:.2f}s)")
    print(f"                ==> Lam_*(m) > {float(Lam_hi.a):.6f} > 8.599 and a_*(m) > 1.1407 for ALL m >= 2!")


# ============================================================================
# MODULE 1: Certify L_hank(Lam) <= 1/(Lam - (2.40 + 3.75/Lam)) for ALL Lam >= 8.599
#           AND eps <= 0.51, tau <= 1.06 for ALL a >= 1.1407!
# ============================================================================
def certify_module_1():
    t0 = time.time()
    lam_max = mp.mpf((iv.mpf(1) / iv.mpf("8.599")).b)  # outward upper bound on 1/8.599 (covers all Lam >= 8.599, a >= 1.1407!)
    c0_iv = iv.mpf("2.40")
    c1_iv = iv.mpf("3.75")

    # Recall: we want to prove that for ALL lam in [0, lam_max], ALL e in (x_-, 1) with
    #   e(1-e) >= psi_ub = lam / (1 - lam * c(lam))   AND   C := e/lam - (1+e)^3 >= 0,
    # and ALL v in (0, v_max(e)] where v_max(e) = sqrt(e*(e/lam - (1+e)^2)) - e*(1+e),
    # we have:
    #   H_val := (B_0 - L_ub) - (v^2 + 3*(1+e)^2*v + C^2/v) < 0,
    # where L_ub = 1 / (1 - lam * c(lam)),  B_0 = 2*(e/lam)*(2+e) - 3*(1+e)^4.
    #
    # Note: e(1-e) >= psi_ub => e <= 1/2 + sqrt(1/4 - psi_ub) < 1 - psi_ub.
    # Even simpler: we ONLY need e in (x_-, 1) AND m4 >= u^2 => 2*(e/lam) - L_ub >= (1+e)^4!
    # Wait: check whether H_val < 0 holds for ALL e in (x_-, 1) even WITHOUT using e(1-e) >= psi_ub?
    # Let's check! In variables (lam, theta) where C = lam * theta (theta >= 0):
    #   s = e / lam  solves  s - (1 + lam*s)^3 = lam * theta.
    #   Note: e = lam * s < 1!
    #
    # PART 1A: Small-to-moderate theta in [0, 30], lam in [0, lam_max] (compact 2D box, lam factored out!).
    #   Dividing H_val by lam > 0 (smooth at lam = 0!):
    #     (B_0 - L_ub) / lam = [2*s - 2*lam^2*s^3 - lam^3*s^4 + 2*theta*(2 + lam*s)] - c(lam)/(1 - lam*c(lam))
    #   Wait: CHECK the exact algebraic identity for B_0 - 1 when s = (1 + e)^3 + lam * theta (e = lam * s)!
    #     B_0 - 1 = 2*s*(2 + e) - 3*(1 + e)^4 - 1
    #             = 2*((1+e)^3 + lam*theta)*(2 + e) - 3*(1 + e)^4 - 1
    #             = [(1+e)^3*(1 - e) - 1] + 2*lam*theta*(2 + e)
    #             = (2*e - 2*e^3 - e^4) + 2*lam*theta*(2 + e)
    #             = lam * [2*s - 2*lam^2*s^3 - lam^3*s^4 + 2*theta*(2 + lam*s)]  EXACTLY!!
    #   And since L_ub - 1 = lam * c(lam) / (1 - lam * c(lam)):
    #     (B_0 - L_ub) / lam = 2*s - 2*lam^2*s^3 - lam^3*s^4 + 2*theta*(2 + lam*s) - c(lam)/(1 - lam*c(lam))!
    #   And for ANY v = lam * vt with 0 < vt <= vt_max:
    #     f(v) / lam = lam * vt^2 + 3*(1 + e)^2 * vt + theta^2 / vt!
    #   Since f'(vt) = 2*lam*vt + 3*(1+e)^2 - theta^2/vt^2 is strictly increasing in vt > 0:
    #     - If 2*lam*vt_max^3 + 3*(1+e)^2*vt_max^2 <= theta^2: min is AT vt = vt_max!
    #     - Wait: for ANY vt in (0, vt_max] AND ANY chosen alpha in [0, 1]:
    #       theta^2/vt = alpha*(theta^2/vt) + (1-alpha)*(theta^2/vt)
    #       3*(1+e)^2*vt + alpha*(theta^2/vt) >= 2*sqrt(3*alpha)*(1+e)*theta,
    #       (1-alpha)*(theta^2/vt) >= (1-alpha)*theta^2 / vt_max!
    #     EVEN BETTER: since vt_max = s*theta / (sqrt(s*(theta + s*(1+e)^2)) + s*(1+e)),
    #     check whether  2*lam*vt_max^3 + 3*(1+e)^2*vt_max^2 <= theta^2  HOLDS EVERYWHERE on theta in [0, 30]?!
    #     Check at lam = 1/8.6, theta = 30: let's handle BOTH cases cleanly via exact monotone derivative!
    #     Specifically, let G(vt) := 2*lam*vt^3 + 3*(1+e)^2*vt^2 - theta^2:
    #       - If G(vt_max) <= 0: f is strictly decreasing on (0, vt_max], so min = f(vt_max) (NO division by 0 since theta^2/vt_max cancels one theta!).
    #       - If G(vt_max) > 0: min is at the unique root vt_* in (0, vt_max) of G(vt_*) = 0, enclosed by 1 Newton/bisection step,
    #         and f(vt_*) = lam*vt_*^2 + 3*(1+e)^2*vt_* + theta^2/vt_*!

    def s_box_from_lam_theta(lam_b, th_b):
        """Rigorous enclosure of the smallest positive root s of s - (1 + lam*s)^3 = lam*theta, with e = lam*s < 1."""
        # Note: as a function of (lam, theta), s is strictly increasing in BOTH lam and theta!
        # Proof: F(s) = s - (1 + lam*s)^3 - lam*theta has F'(s) = 1 - 3*lam*(1+lam*s)^2 > 0 for e < x_m?
        # WAIT: F'(s) = 1 - 3*lam*(1+e)^2 = 0 at 3*(1+e)^2 = Lam, which IS the transition between x_- and x_+!
        # For e in (x_-, x_+), we have s > (1+e)^3, and e = lam*s can be ANYTHING in (x_-, min(1, x_+))!
        # OH!! GOOD CATCH!! s is NOT a single-valued function of theta when e crosses the peak of s - (1+e)^3!
        # INSTEAD, parameterize by (lam, e) DIRECTLY for e >= 0.05, and (lam, theta) ONLY for e <= 0.15 where F'(s) > 0!
        pass

    # EVEN CLEANER PARAMETERIZATION (ZERO BRANCHING, 100% SINGLE-VALUED EVERYWHERE!!):
    # Parameterize directly by (lam, e) — wait, at lam -> 0, e ~ lam -> 0, so split e into TWO OVERLAPPING regions:
    #   REGION 1A: Small s = e / lam in [1, 15], lam in [0, lam_max]  (covers ALL e <= 15 * lam!)
    #     Here e = lam * s is 100% explicit (NO root-finding!), C = s - (1 + lam*s)^3!
    #     WAIT: We need C >= 0, so s >= s_min(lam) = 1 + 3*lam + ...!
    #     To factor out lam cleanly at s ~ 1 + O(lam), set  s = (1 + lam)^3 + lam * u  ? No:
    #     Just set  s = 1 + lam * w  for w in [3, 60] (covers s in [1 + 3*lam, 1 + 60*lam], i.e. theta in [0, ~50])!
    #     AND  s in [1 + 50*lam, 1/lam]  (where C = s - (1+e)^3 >= 40*lam, handled by Region 1B!!)!
    #   WAIT A SECOND!! CHECK THAT!!
    #   In Region 1A: s = 1 + lam * w  with  lam in [0, lam_max]  and  w in [0, 80]!!
    #     - For EVERY (lam, w), e = lam * (1 + lam * w) is an EXPLICIT POLYNOMIAL!
    #     - C / lam = [1 + lam*w - (1 + e)^3] / lam = w - 3*s - 3*lam*s^2 - lam^2*s^3 =: theta (EXPLICIT POLYNOMIAL, ZERO 0/0!!)!
    #     - If theta.b <= 0, this (lam, w) box is INFEASIBLE (C <= 0)!
    #     - Otherwise, vt_max = s*theta / (sqrt(s*(theta + s*(1+e)^2)) + s*(1+e)) is 100% NON-SINGULAR even at theta = 0 and lam = 0!
    #   In Region 1B: e in [min_e, 1] where s = e / lam >= 1 + 75 * lam (wait: when lam -> 0, e >= 75*lam^2 + lam!
    #     Better: parameterize Region 1B by (lam, e) with e in [lam*(1 + 75*lam), 1], i.e. e = lam + u with u in [75*lam^2, 1-lam]!).
    #     WAIT A SECOND!! Check whether at lam = 1/8.6, 1 + 75*lam = 9.72 => e = lam*s = 9.72/8.6 > 1 ALREADY!!
    #     SO FOR ALL lam >= 0.05, REGION 1A (w in [0, 80]) ALREADY COVERS ALL e in (0, 1)!!
    #     AND FOR SMALL lam in [0, 0.05] AND s >= 1 + 75*lam (i.e. theta >= 60), CHECK THE 3-LINE ANALYTIC BOUND FOR REGION 1B!!

    # Let's check Region 1B first (ALL lam in [0, lam_max] and ALL e in (0, 1) with C >= 30 * lam):
    #   Recall: we have e in (0, 1), lam in [0, lam_max], s = e / lam, C = s - (1+e)^3 >= 30 * lam!
    #   Wait: in H_val < 0:
    #     B_0 = 2*s*(2+e) - 3*(1+e)^4 = 2*(C + (1+e)^3)*(2+e) - 3*(1+e)^4 = 2*C*(2+e) + (1+e)^3*(1-e)
    #         <= 6*C + 1 + 2*e  (since (1+e)^3*(1-e) = 1 + 2e - 2e^3 - e^4 <= 1 + 2e!).
    #     Wait: at e < 1, B_0 - L_ub <= B_0 - 1 <= 6*C + 2*e!
    #   NOW LOWER BOUND f(v) = v^2 + 3*(1+e)^2*v + C^2/v  for ALL v in (0, v_max]!!
    #     Case i: Use 3-term weighted AM-GM (VALID FOR ALL v > 0, NO v_max NEEDED!):
    #       v^2 + (1/2)*(C^2/v) + (1/2)*(C^2/v) >= 3 * (1/4)^{1/3} * C^{4/3}
    #       No, we want to beat 6*C + 2*e!
    #       Watch! Split  C^2/v = (1 - a)*(C^2/v) + a*(C^2/v):
    #       Even simpler: by AM-GM on  v^2 + 3*(1+e)^2*v + C^2/v  vs  C^2/v_max:
    #       For ANY v in (0, v_max]:
    #         - EITHER v >= 1/2: then v^2 + 3*(1+e)^2*v + C^2/v >= (1/2)*3*(1+e)^2 + (v^2 + C^2/v)!
    #           Wait: by AM-GM, (1/2)*v^2 + 2*(1/4)*C^2/v >= 3*(1/32)^{1/3}*C^{4/3}, and 3*v + (1/2)*C^2/v >= sqrt(6)*C!
    #           Wait: for C >= 30*lam, C can still be SMALL (e.g. C = 0.001 when lam = 1e-5)!
    #           When C is small (C < 1), v_max <= sqrt(e*(C + e*(1+e)^2)) = sqrt(lam*s*(C + ...)) <= sqrt(lam*s*C + e^2*(1+e)^2)!
    #         - SO ALWAYS COMPARE  C^2 / v_max  WITH  6*C + 2*e  WHEN C = lam*theta (theta >= 30)!
    #           Remember:  C^2 / v_max = C * (sqrt(s*(C/lam + s*(1+e)^2)) + s*(1+e)) / s
    #                                  >= C * sqrt(C / (lam * s)) = C * sqrt(C / e)!!
    #           WAIT A SECOND!! STOP AND STARE AT THAT ONE-LINE FORMULA!!
    #             v_max = sqrt(e*(e/lam - (1+e)^2)) - e*(1+e) <= sqrt(e * C / lam)??
    #           CHECK!!  e/lam - (1+e)^2 = C + e*(1+e)^2!
    #           Wait: sqrt(e*(C + e*(1+e)^2)) - e*(1+e) = e*C / (sqrt(e*C + e^2*(1+e)^2) + e*(1+e))!
    #           DIVIDE C^2 BY v_max!!
    #             C^2 / v_max = C * [ sqrt(C/e + (1+e)^2) + (1+e) ]  EXACTLY!!
    #           OH!! MY!! GOD!! LOOK AT THAT IDENTITY!!
    #             C^2 / v_max  ==  C * ( sqrt(C/e + (1+e)^2) + (1 + e) )   (ZERO lam IN IT!!)
    #           NOW CHECK  C / e  WHEN  C = e/lam - (1+e)^3  AND  theta = C/lam >= 40:
    #             - If e >= 0.05: then e/lam >= 0.05*8.6, wait: we want C/e >= 36!!
    #               C / e = 1/lam - (1+e)^3 / e!
    #               At e in (0, 1) and lam <= 1/8.6:
    #                 - When e >= 0.2 and lam <= 0.02: 1/lam >= 50, (1+e)^3/e <= 1.2^3/0.2 = 8.64 => C/e >= 41.3 => sqrt(C/e) >= 6.4 => C^2/v_max >= 7.6*C!
    #                 - What about large v? If v <= v_max AND 2*v^3 + 3*(1+e)^2*v^2 <= C^2 then f(v) >= f(v_max) >= C^2/v_max!
    #                 - What if 2*v^3 + 3*(1+e)^2*v^2 > C^2? Then v_* < v_max, and at v_*, check f(v_*)!
    #                   Notice: if C >= 20, then 3*(1+e)^2*v + C^2/v + v^2: at v = 2, f(v) >= 6*C + 10 ALREADY!
    #                   Wait: let's check BOTH Region 1A (compact (lam, w)) AND Region 1B (compact (lam, e)) in ONE clean 2D iv branch-and-bound!

    # Wait: LOOK HOW SIMPLE A 2-REGION COMPACT COVER OF ALL (lam, e) WITH lam in [0, lam_max] IS!!
    #   Let lam_split = 0.02 (i.e. Lam = 50):
    #   - Region I:  lam in [lam_split, lam_max],  e in [0, 1]  --> 100% bounded away from lam=0! Standard 2D iv box!
    #   - Region II: lam in [0, lam_split]:
    #       * II-a: w = (e/lam - 1)/lam in [0, 80]  (covers e <= lam*(1 + 80*lam))! Smooth at lam = 0!
    #       * II-b: e in [lam*(1 + 80*lam), 1]  --> HERE e/lam >= 1 + 80*lam AND lam <= 0.02!
    #               Let's prove II-b in 4 PURE ELEMENTARY LINES (ZERO GRID NEEDED!!):
    #               Wait: check for ALL lam in (0, 0.02] and e in [lam*(1+80*lam), 1]:
    #                 Let q := C / e = 1/lam - (1+e)^3/e!
    #                 Wait: at e = lam*(1 + 80*lam), q = [lam*(1+80*lam) - lam*(1+e)^3] / (lam*e) ~ 77/e >= 77!
    #                 At e = 1, q = 1/lam - 8 >= 50 - 8 = 42!
    #                 Minimizing q(e) = 1/lam - (1+e)^3/e over e in [lam*(1+80*lam), 1]:
    #                 (1+e)^3/e is convex on (0, 1], with min at e=1/2 (value 27/4 = 6.75), max at endpoints:
    #                 at e = 1: value = 8; at e = lam*(1+80*lam): 1/lam - (1+e)^3/e = (1 + 80*lam - (1+e)^3)/(lam*(1+80*lam)) >= 70!
    #                 SO q = C / e >= 42  EVERYWHERE ON REGION II-b!!
    #                 THEREFORE:
    #                   - B_0 - 1 = 2*C*(2+e) + (2e - 2e^3 - e^4) <= 6*C + 2*e <= (6 + 2/42)*C = 6.048 * C!
    #                   - Meanwhile, what is min_{0 < v <= v_max} (v^2 + 3*(1+e)^2*v + C^2/v)??
    #                     Compare with 6.048 * C!!
    #                     (a) For v <= v_max:  v_max = e*C / (sqrt(e*C + e^2*(1+e)^2) + e*(1+e)) = C / (sqrt(q + (1+e)^2) + 1 + e)
    #                         Since q >= 42 and 1+e >= 1:  sqrt(q + (1+e)^2) + 1 + e >= sqrt(43) + 1 = 7.557!
    #                         SO  C^2 / v_max >= 7.557 * C  >  6.048 * C!!
    #                     (b) Wait: is v_max <= v_*? What if v_* < v_max?!
    #                         Recall f'(v) = 2*v + 3*(1+e)^2 - C^2/v^2!
    #                         Look at f(v) for ANY v > 0 when C >= 42 * e:
    #                         If v <= C / 6.5: then C^2 / v >= 6.5 * C > 6.048 * C!
    #                         If v >= C / 6.5: wait, v <= v_max <= C / 7.557 < C / 6.5!!
    #                         **OH!! MY!! GOD!! v <= v_max <= C / 7.557 FORCES C^2 / v >= 7.557 * C > 6.048 * C FOR EVERY SINGLE v IN (0, v_max]!!**
    #                         ZERO CASE SPLIT!! ZERO v_* NEEDED!! LITERALLY ONE SINGLE LINE!!

    # Verify Region II-b constants in mpmath.iv!
    lam_split = mp.mpf("0.02")
    lam_sp = iv.mpf(lam_split)
    # Check at left endpoint e_0 = lam*(1 + 80*lam), lam in [0, lam_split]:
    lam_b0 = iv.mpf([0, lam_split])
    e0_max = lam_sp * (1 + 80 * lam_sp)  # = 0.052
    # (1 + e0)^3 <= 1 + 3*e0 + 3*e0^2 + e0^3, and e0 = lam*(1 + 80*lam):
    # q(e0) = [1 + 80*lam - (1 + e0)^3] / [lam*(1 + 80*lam)]
    #       = [80 - 3*(1+80*lam) - 3*lam*(1+80*lam)^2 - lam^2*(1+80*lam)^3] / (1 + 80*lam)
    s0_b = 1 + 80 * lam_b0
    q_left = (80 - 3 * s0_b - 3 * lam_b0 * s0_b**2 - lam_b0**2 * s0_b**3) / s0_b
    q_right = 1 / lam_sp - 8  # = 42
    q_min = min(mp.mpf(q_left.a), mp.mpf(q_right.a))
    # Since e -> (1+e)^3/e is convex on (0, 1] (d^2/de^2 [(1+e)^3/e] = 2/e^3 + 2 > 0!), its max on [e0, 1] is at an endpoint!
    lhs_coeff = iv.mpf(6) + iv.mpf(2) / iv.mpf(q_min)
    rhs_coeff = iv.sqrt(iv.mpf(q_min) + 1) + 1
    assert mp.mpf(rhs_coeff.a) > mp.mpf(lhs_coeff.b), f"Region II-b failed: {rhs_coeff} vs {lhs_coeff}"
    print(f"  [Module 1 / Region II-b PASS] Pure 3-line bound (lam <= 0.02, w >= 80): "
          f"q >= {float(q_min):.2f} ==> C^2/v_max >= {float(rhs_coeff.a):.3f}*C > {float(lhs_coeff.b):.3f}*C >= B_0 - 1!")

    # Verify Region II-a: lam in [0, 0.02], w in [0, 80] (exact adaptive 2D iv branch-and-bound!)
    def check_IIa_box(lam_b, w_b):
        s_b = 1 + lam_b * w_b
        e_b = lam_b * s_b
        th_b = w_b - 3 * s_b - 3 * lam_b * (s_b ** 2) - (lam_b ** 2) * (s_b ** 3)
        if mp.mpf(th_b.b) <= 0:
            return True  # C <= 0 everywhere -> infeasible!
        th_pos = iv_pos(th_b)
        c_b = c0_iv + c1_iv * lam_b
        base_num = 2 * s_b - 2 * (lam_b ** 2) * (s_b ** 3) - (lam_b ** 3) * (s_b ** 4) - c_b / (1 - lam_b * c_b)
        D_vt = iv.sqrt(th_pos / s_b + (1 + e_b) ** 2) + (1 + e_b)
        vt_max = th_pos / D_vt
        G_over_th2 = 2 * lam_b * th_pos / (D_vt ** 3) + 3 * ((1 + e_b) ** 2) / (D_vt ** 2) - 1
        if mp.mpf(G_over_th2.b) <= 0:
            # Since D_vt >= 2*(1+e) > sqrt(3)*(1+e), x -> x + 3*(1+e)^2/x is STRICTLY INCREASING!
            # So D_vt + 3*(1+e)^2/D_vt >= D_lo + 3*(1+e)^2/D_lo (ZERO wrapping in D_vt!)
            D_lo = iv.mpf(mp.mpf(D_vt.a))
            assert mp.mpf((D_lo ** 2 - 3 * ((1 + e_b) ** 2)).a) > 0
            sum_D_lo = D_lo + 3 * ((1 + e_b) ** 2) / D_lo
            coeff_th = 2 * (2 + e_b) - sum_D_lo
            diff_b = base_num + th_pos * coeff_th - lam_b * (vt_max ** 2)
            if mp.mpf(diff_b.b) < 0:
                return True
        else:
            diff_b = base_num + th_pos * (2 * (2 + e_b) - D_vt)
            if mp.mpf(diff_b.b) < 0:
                return True
        return False

    stack = [(mp.mpf(0), lam_split, mp.mpf(0), mp.mpf(80), 0)]
    boxes_IIa = 0
    while stack:
        l0, l1, w0, w1, dep = stack.pop()
        if check_IIa_box(iv.mpf([l0, l1]), iv.mpf([w0, w1])):
            boxes_IIa += 1
            continue
        assert dep < 26, f"Region II-a failed at lam=[{l0},{l1}], w=[{w0},{w1}]"
        if (w1 - w0) / 80 > (l1 - l0) / lam_split:
            wm = (w0 + w1) / 2
            stack.append((l0, l1, wm, w1, dep + 1))
            stack.append((l0, l1, w0, wm, dep + 1))
        else:
            lm = (l0 + l1) / 2
            stack.append((lm, l1, w0, w1, dep + 1))
            stack.append((l0, lm, w0, w1, dep + 1))
    print(f"  [Module 1 / Region II-a PASS] Compact (lam in [0, 0.02], w in [0, 80]) certified in {boxes_IIa} iv boxes!")

    # Verify Region I: lam in [0.02, lam_max], e in [0, 1] (bounded away from lam = 0!)
    def check_I_box(lam_b, e_b):
        c_b = c0_iv + c1_iv * lam_b
        L_ub = 1 / (1 - lam_b * c_b)
        psi_ub = lam_b * L_ub
        # Check e*(1-e) >= psi_ub:
        if mp.mpf((e_b * (1 - e_b) - psi_ub).b) < 0:
            return True
        # Check C = e/lam - (1+e)^3 >= 0:
        C_b = e_b / lam_b - (1 + e_b) ** 3
        if mp.mpf(C_b.b) <= 0:
            return True
        # Check m4 = 2*e/lam - L_ub >= (1+e)^4:
        if mp.mpf((2 * e_b / lam_b - L_ub - (1 + e_b) ** 4).b) < 0:
            return True
        C_pos = iv_pos(C_b)
        base_B0 = ((1 + e_b) ** 3) * (1 - e_b) - L_ub
        # v_max = C / D_v where D_v = sqrt(C/e + (1+e)^2) + (1+e)  (exact!)
        D_v = iv.sqrt(C_pos / e_b + (1 + e_b) ** 2) + (1 + e_b)
        vmax = C_pos / D_v
        G_rat = 2 * C_pos / (D_v ** 3) + 3 * ((1 + e_b) ** 2) / (D_v ** 2) - 1
        if mp.mpf(G_rat.b) <= 0:
            D_lo = iv.mpf(mp.mpf(D_v.a))
            assert mp.mpf((D_lo ** 2 - 3 * ((1 + e_b) ** 2)).a) > 0
            sum_D_lo = D_lo + 3 * ((1 + e_b) ** 2) / D_lo
            coeff_C = 2 * (2 + e_b) - sum_D_lo
            diff_b = base_B0 + C_pos * coeff_C - (vmax ** 2)
            if mp.mpf(diff_b.b) < 0:
                return True
            return False
        else:
            return False

    stack = [(lam_split, lam_max, mp.mpf("0.01"), mp.mpf("0.99"), 0)]
    # Verify e in [0, 0.01] infeasible (C = e/lam - (1+e)^3 < 0) and e in [0.99, 1.0] infeasible (e(1-e) < psi_ub):
    lam_regI = iv.mpf([lam_split, lam_max])
    assert mp.mpf((iv.mpf([0, mp.mpf("0.01")]) / lam_regI - 1).b) < 0
    e_hi_strip = iv.mpf([mp.mpf("0.99"), mp.mpf("1.0")])
    psi_regI = lam_regI / (1 - lam_regI * (c0_iv + c1_iv * lam_regI))
    assert mp.mpf((e_hi_strip * (1 - e_hi_strip) - psi_regI).b) < 0
    boxes_I = 0
    while stack:
        l0, l1, e0, e1, dep = stack.pop()
        if check_I_box(iv.mpf([l0, l1]), iv.mpf([e0, e1])):
            boxes_I += 1
            continue
        assert dep < 36, f"Region I failed at lam=[{l0},{l1}], e=[{e0},{e1}]"
        if (e1 - e0) > (l1 - l0):
            em = (e0 + e1) / 2
            stack.append((l0, l1, em, e1, dep + 1))
            stack.append((l0, l1, e0, em, dep + 1))
        else:
            lm = (l0 + l1) / 2
            stack.append((lm, l1, e0, e1, dep + 1))
            stack.append((l0, lm, e0, e1, dep + 1))
    print(f"  [Module 1 / Region I PASS]    Compact (lam in [0.02, 1/8.599], e in [0, 1]) certified in {boxes_I} iv boxes!")

    # PART 1C: Certify eps_ub <= 0.51 AND tau_ub <= 1.06 for ALL a >= 1.1407 (compact s = 1/a in [0, 1/1.1407])!
    # Recall: Lam = a^2 * (1 + s)^3 = (1 + s)^3 / s^2,  lam = s^2 / (1 + s)^3,  sig_+ = (1 - s) / s^2!
    # x_1 = 1 / (Lam - 3.6) = lam / (1 - 3.6*lam).
    # dT_1 = (1 + x_1)^2 / (Lam - (1 + x_1)^2) - x_1^2 = lam * [ (1 + x_1)^2 / (1 - lam*(1 + x_1)^2) - lam / (1 - 3.6*lam)^2 ]!
    # Notice: m1_ub * psi_ub - sig_+ = sig_+ * (psi_ub / dT_1 - 1)!!
    # FACTOR OUT lam FROM BOTH psi_ub AND dT_1!!
    #   psi_ub / dT_1 = [1 / (1 - lam*c(lam))] / [ (1 + x_1)^2 / (1 - lam*(1 + x_1)^2) - lam / (1 - 3.6*lam)^2 ]!
    #   AND sig_+ = (1 - s) / s^2!
    #   At s -> 0 (lam = s^2 / (1+s)^3 -> 0):
    #     psi_ub / dT_1 - 1 = lam * [ c(lam) - 2*x_1/lam - ... ]!
    #   Let's factor out lam ONCE symbolically so there is ZERO 0/0 at s = 0!!
    #   Exact rational identity:
    #     Let A_d := (1 + x_1)^2 / (1 - lam*(1 + x_1)^2) - lam / (1 - 3.6*lam)^2  (so dT_1 = lam * A_d),
    #     Let B_p := 1 / (1 - lam * c(lam))  (so psi_ub = lam * B_p).
    #     Write  A_d = 1 + lam * A_1(lam)  and  B_p = 1 + lam * B_1(lam)  EXACTLY:
    #       (1 + x_1)^2 = 1 + 2*x_1 + x_1^2 = 1 + lam * [2/(1-3.6*lam) + lam/(1-3.6*lam)^2] =: 1 + lam * P_1(lam),
    #       (1 + x_1)^2 / (1 - lam*(1+x_1)^2) - 1 = lam * [ P_1 + (1 + x_1)^2 ] / (1 - lam*(1+x_1)^2),
    #       so A_1(lam) = [ P_1 + (1 + x_1)^2 ] / (1 - lam*(1+x_1)^2) - 1 / (1 - 3.6*lam)^2  (at lam=0: 2+1-1 = +2!),
    #       and B_1(lam) = c(lam) / (1 - lam*c(lam))  (at lam=0: 2.40!).
    #     THEREFORE:
    #       psi_ub / dT_1 - 1 = (B_p - A_d) / A_d = lam * (B_1(lam) - A_1(lam)) / A_d !!
    #     MULTIPLY BY sig_+ = (1 - s) / s^2  (and recall lam = s^2 / (1 + s)^3, SO s^2 CANCELS IDENTICALLY!!):
    #       delta_ub(s) = ((1 - s) / (1 + s)^3) * (B_1(lam) - A_1(lam)) / A_d !!
    #     AND THEREFORE:
    #       tau_ub^2 = C_E^2 * delta_ub / (a + 1) = C_E^2 * s * delta_ub / (1 + s) !!
    #       eps_ub^2 = s^2 * tau_ub^2 !!
    #   ZERO SINGULARITY AT s = 0!! 100% SMOOTH ON THE ENTIRE COMPACT INTERVAL s in [0, 1/1.1407]!!
    s_max = mp.mpf((iv.mpf(1) / iv.mpf("1.1407")).b)  # outward upper bound on 1/1.1407
    max_eps = mp.mpf(0); max_tau = mp.mpf(0)
    N_s = 400
    s_grid = [mp.mpf(0)] + [mp.mpf((iv.mpf(s_max) * k / N_s).a) for k in range(1, N_s)] + [s_max]
    for k in range(N_s):
        sb = iv.mpf([s_grid[k], s_grid[k + 1]])
        lamb = (sb ** 2) / ((1 + sb) ** 3)
        denom36 = 1 - iv.mpf("3.6") * lamb
        x1b = lamb / denom36
        P1 = 2 / denom36 + lamb / (denom36 ** 2)
        opx1_sq = (1 + x1b) ** 2
        A1 = (P1 + opx1_sq) / (1 - lamb * opx1_sq) - 1 / (denom36 ** 2)
        Ad = 1 + lamb * A1
        cb = c0_iv + c1_iv * lamb
        B1 = cb / (1 - lamb * cb)
        d_ub = ((1 - sb) / ((1 + sb) ** 3)) * (B1 - A1) / Ad
        tau_sq = (C_E ** 2) * sb * d_ub / (1 + sb)
        eps_sq = (sb ** 2) * tau_sq
        tau_hi = mp.mpf(iv.sqrt(iv_pos(tau_sq)).b)
        eps_hi = mp.mpf(iv.sqrt(iv_pos(eps_sq)).b)
        if tau_hi > max_tau: max_tau = tau_hi
        if eps_hi > max_eps: max_eps = eps_hi
    assert max_eps < mp.mpf("0.51") and max_tau < mp.mpf("1.06"), f"Box exceeded: eps={max_eps}, tau={max_tau}"
    print(f"[MODULE 1 PASS] ALL Lam >= 8.599 certified! Uniform bounds across ALL m >= 2:")
    print(f"                max eps <= {float(max_eps):.6f} < 0.51,  max tau <= {float(max_tau):.6f} < 1.06  ({time.time()-t0:.2f}s)")


# ============================================================================
# MODULE 2: Universal positivity c_n(eps, tau) > 0 for ALL n >= 0 on
#           0 <= eps <= tau <= 1.06,  eps <= 0.51 !!
# ============================================================================
def certify_module_2():
    t0 = time.time()
    # Polynomial in w:
    #   P(w) = (1 + (1-eps)*w)*(w^2 + (tau/c_e^2)*w + 1/c_e^2) + c_g*w*(1 - eps*w)^3
    #        = p4*w^4 + p3*w^3 + p2*w^2 + p1*w + p0
    # Wait: at eps = 0, p4 = -c_g*eps^3 = 0, so the large root w4 goes to +infinity as ~ 1/(c_g*eps^3)!
    # To handle w4 cleanly WITHOUT division by zero at eps = 0, work in u4 := 1 / w4 = O(eps^3) (actually r4 = 1 - eps*w4 => s4 := 1 / r4 = O(eps^2)!!)!
    # LOOK HOW CLEAN s4 := 1 / r4 = z_4^{-1} IS!!
    # Recall the original z-polynomial D(z) / A:
    #   d0 = 1 + (eps^2/c_e^2)*(tau/eps + 1) ... wait, multiply by eps:
    #   In z:  P_z(z) := (1 - (1-eps)*z) * ((1-z)^2 + (eps/c_e^2)*(eps + tau*(1-z))) + c_g*eps^2*z^3*(1-z)
    #   Look at the reciprocal polynomial in y := 1 / z  (so y4 = 1 / r4 = O(eps^2) -> 0 smoothly at eps = 0!!):
    #     R(y) := y^4 * P_z(1/y)
    #           = (y - (1-eps)) * ((y - 1)^2 * y + (eps/c_e^2)*(eps*y^3 + tau*(y - 1)*y^2)) + c_g*eps^2*(y - 1)
    #   CHECK AT eps = 0!!
    #     R(y) = (y - 1)^3 * y  -> root y4 = 0 IS SIMPLE (R'(0) = -1)!!
    #   SO y4 = 1 / r4 IS AN ANALYTIC FUNCTION OF (eps, tau) AT eps = 0 WITH y4 = -c_g * eps^2 + O(eps^3)!!
    #   AND A4 / r4 = [ (1 - (1-eps)*r4)*(eps + tau*(1 - r4)) ] / [ ... ] IS ALSO 100% SMOOTH AT eps = 0!!
    #   CHECK: in y = 1/z,
    #     A_4 = -N(r_4) / D'(r_4),   so  (A_4 / r_4) = ...
    #     Wait: N_hat_z(z) = (1 - (1-eps)*z)*(eps + tau*(1-z)),
    #     P_z(z) = (1 - (1-eps)*z)*((1-z)^2 + (eps/c_e^2)*(eps + tau*(1-z))) + c_g*eps^2*z^3*(1-z).
    #     Remember for z = 1 - eps*w: P_z(z) = eps^3 * P(w), N_hat_z(z) = eps^2 * N_hat(w),
    #     so A_j^(z) = -N_hat_z(r_j) / P_z'(r_j) = (1/eps) * (-N_hat(w_j) / (-P'(w_j) / eps)) = N_hat(w_j) / P'(w_j)!!
    #     (Wait: check sign! P_z(z) = eps^3 P((1-z)/eps) => P_z'(z) = -eps^2 P'(w), so -N_hat_z(r_j)/P_z'(r_j) = N_hat(w_j)/P'(w_j)!)
    #     NOW COMPUTE A_4^(z) * (r_1 / r_4) IN TERMS OF y4 = 1 / r4 = O(eps^2)!!
    #       N_hat_z(1/y4) = y4^{-2} * (y4 - (1-eps)) * (eps*y4 + tau*(y4 - 1))
    #       Since P_z(z) = z^4 * R(1/z): at a root R(y4) = 0, P_z'(1/y4) = -(1/y4)^2 * R'(y4)!
    #       THEREFORE:
    #         A_4^(z) = -N_hat_z(1/y4) / P_z'(1/y4) = (y4 - (1-eps)) * (eps*y4 + tau*(y4 - 1)) / R'(y4)!!
    #       AND  A_4^(z) * (r_1 / r_4) = r_1 * y4 * (y4 - (1-eps)) * (eps*y4 + tau*(y4 - 1)) / R'(y4)!!
    #     CHECK THE POWER OF eps AT eps = 0!!
    #       y4 = -c_g * eps^2 + O(eps^3),  R'(y4) = -1 + O(eps),
    #       so A_4^(z) * (r_1 / r_4) = O(eps^2 * tau) = O(eps^3)  (ZERO 0/0 AT eps = 0!!)!
    #       EVEN BETTER: y4 / eps^2 =: q4 satisfies  R(eps^2 * q4) / eps^2 = 0,
    #       so we certify y4 = eps^2 * q4 with q4 in [-0.45, -0.15] in ONE LINE by Krawczyk on R_q(q) = R(eps^2*q)/eps^2!!

    ce2 = C_E * C_E

    def poly_P_and_dP(w, eb, tb):
        # P(w) = (1 + (1-e)w)*(w^2 + (t/ce2)*w + 1/ce2) + c_g * w * (1 - e*w)^3
        u1 = 1 + (1 - eb) * w
        u2 = w * w + (tb / ce2) * w + 1 / ce2
        om = 1 - eb * w
        P = u1 * u2 + C_G * w * (om ** 3)
        dP = (1 - eb) * u2 + u1 * (2 * w + tb / ce2) + C_G * (om ** 2) * (1 - 4 * eb * w)
        return P, dP

    def poly_P_mv(w_m, em, tm, eb, tb):
        """Centered-form enclosure of P(w_m; eb, tb) for real midpoint w_m — zero cancellation!"""
        w0 = iv.mpf(w_m); e0 = iv.mpf(em); t0 = iv.mpf(tm)
        P0, _ = poly_P_and_dP(w0, e0, t0)
        # dP/de = -w*(w^2 + (t*w + 1)/ce2) - 3*c_g*w^2*(1 - e*w)^2
        # dP/dt = w*(1 + (1 - e)*w) / ce2
        dP_de = -w0 * (w0 * w0 + (tb * w0 + 1) / ce2) - 3 * C_G * (w0 * w0) * ((1 - eb * w0) ** 2)
        dP_dt = w0 * (1 + (1 - eb) * w0) / ce2
        return P0 + dP_de * (eb - e0) + dP_dt * (tb - t0)

    def poly_dP_mv(W, w_m, em, tm, eb, tb):
        """Centered-form enclosure of P'(W; eb, tb) around (w_m, em, tm) — zero cancellation!"""
        w0 = iv.mpf(w_m); e0 = iv.mpf(em); t0 = iv.mpf(tm)
        _, dP0 = poly_P_and_dP(w0, e0, t0)
        # P''(w) = 2*(1-e)*(2w + t/ce2) + 2*(1 + (1-e)w) + c_g*(-12*e*(1-e*w)^2 + 12*e^2*w*(1-e*w)) ...
        # Wait: simplify d/dw [c_g*(1-ew)^2*(1-4ew)] = c_g*(-2e(1-ew)(1-4ew) - 4e(1-ew)^2) = -6*c_g*e*(1-ew)*(1 - 2*e*w)!
        omW = 1 - eb * W
        ddP = 2 * (1 - eb) * (2 * W + tb / ce2) + 2 * (1 + (1 - eb) * W) - 6 * C_G * eb * omW * (1 - 2 * eb * W)
        # d/de [P'(w0; e, t)] = -(w0^2 + (t*w0 + 1)/ce2) - w0*(2*w0 + t/ce2) + c_g*d/de[(1-e*w0)^2*(1-4*e*w0)]
        #   d/de[(1-e*w0)^2*(1-4*e*w0)] = -6*w0*(1-e*w0)*(1-2*e*w0)!
        om0 = 1 - eb * w0
        ddP_de = -(3 * w0 * w0 + (2 * tb * w0 + 1) / ce2) - 6 * C_G * w0 * om0 * (1 - 2 * eb * w0)
        # d/dt [P'(w0; e, t)] = ((1-e)*w0 + 1 + (1-e)*w0) / ce2 = (1 + 2*(1-e)*w0) / ce2
        ddP_dt = (1 + 2 * (1 - eb) * w0) / ce2
        return dP0 + ddP * (W - w0) + ddP_de * (eb - e0) + ddP_dt * (tb - t0)

    def poly_P_cpx_mv(wr_m, wi_m, em, tm, eb, tb):
        """Centered-form enclosure of complex P(w_m; eb, tb) — zero cancellation!"""
        w0 = (iv.mpf(wr_m), iv.mpf(wi_m)); e0 = iv.mpf(em); t0 = iv.mpf(tm)
        P0, _ = poly_P_cpx(w0[0], w0[1], e0, t0)
        w2 = cpx_mul(w0, w0)
        u2 = (w2[0] + (tb / ce2) * w0[0] + 1 / ce2, w2[1] + (tb / ce2) * w0[1])
        om = (1 - eb * w0[0], -eb * w0[1]); om2 = cpx_mul(om, om)
        # dP/de = -w*u2 - 3*c_g*w^2*om^2
        tA = cpx_mul((-w0[0], -w0[1]), u2)
        tB = cpx_mul((-3 * C_G * w2[0], -3 * C_G * w2[1]), om2)
        dP_de = cpx_add(tA, tB)
        # dP/dt = w*(1 + (1-e)*w) / ce2
        u1 = (1 + (1 - eb) * w0[0], (1 - eb) * w0[1])
        wu1 = cpx_mul(w0, u1)
        dP_dt = (wu1[0] / ce2, wu1[1] / ce2)
        de = eb - e0; dt = tb - t0
        return (P0[0] + dP_de[0] * de + dP_dt[0] * dt, P0[1] + dP_de[1] * de + dP_dt[1] * dt)

    def poly_dP_cpx_mv(Wr, Wi, wr_m, wi_m, em, tm, eb, tb):
        """Centered-form enclosure of complex P'(W; eb, tb) around (w_m, em, tm) — zero cancellation!"""
        w0 = (iv.mpf(wr_m), iv.mpf(wi_m)); e0 = iv.mpf(em); t0 = iv.mpf(tm)
        _, dP0 = poly_P_cpx(w0[0], w0[1], e0, t0)
        W = (Wr, Wi)
        omW = (1 - eb * Wr, -eb * Wi)
        fW = (1 - 2 * eb * Wr, -2 * eb * Wi)
        omW_fW = cpx_mul(omW, fW)
        # P''(W) = 2*(1-e)*(2W + t/ce2) + 2*(1 + (1-e)W) - 6*c_g*e*omW*(1 - 2eW)
        ddP = (2 * (1 - eb) * (3 * Wr + tb / ce2) + 2 - 6 * C_G * eb * omW_fW[0],
               6 * (1 - eb) * Wi - 6 * C_G * eb * omW_fW[1])
        # d/de [P'(w0; e, t)] = -(3*w0^2 + (2*t*w0 + 1)/ce2) - 6*c_g*w0*(1-e*w0)*(1-2*e*w0)
        w2 = cpx_mul(w0, w0)
        om0 = (1 - eb * w0[0], -eb * w0[1])
        f0 = (1 - 2 * eb * w0[0], -2 * eb * w0[1])
        w_om_f = cpx_mul(w0, cpx_mul(om0, f0))
        ddP_de = (-(3 * w2[0] + (2 * tb * w0[0] + 1) / ce2) - 6 * C_G * w_om_f[0],
                  -(3 * w2[1] + (2 * tb / ce2) * w0[1]) - 6 * C_G * w_om_f[1])
        ddP_dt = ((1 + 2 * (1 - eb) * w0[0]) / ce2, (2 * (1 - eb) * w0[1]) / ce2)
        dW = (Wr - w0[0], Wi - w0[1]); de = eb - e0; dt = tb - t0
        tW = cpx_mul(ddP, dW)
        return (dP0[0] + tW[0] + ddP_de[0] * de + ddP_dt[0] * dt,
                dP0[1] + tW[1] + ddP_de[1] * de + ddP_dt[1] * dt)

    def poly_Rq_and_dRq(q, eb, tb):
        # R(y) = (y - (1-e))*(y*(y-1)^2 + (e/ce2)*y^2*(e*y + t*(y-1))) + c_g*e^2*(y - 1)
        # Put y = e^2 * q and divide by e^2:
        y = (eb ** 2) * q
        # Note y*(y-1)^2 / e^2 = q*(y-1)^2, and (e/ce2)*y^2 / e^2 = (e^3/ce2)*q^2!
        fac1 = y - (1 - eb)
        inner = q * ((y - 1) ** 2) + (eb ** 3 / ce2) * (q ** 2) * (eb * y + tb * (y - 1))
        Rq = fac1 * inner + C_G * (y - 1)
        # Derivative wrt q (dy/dq = e^2):
        dfac1 = eb ** 2
        dinner = ((y - 1) ** 2 + 2 * q * (y - 1) * (eb ** 2)
                  + (eb ** 3 / ce2) * (2 * q * (eb * y + tb * (y - 1)) + (q ** 2) * (eb + tb) * (eb ** 2)))
        dRq = dfac1 * inner + fac1 * dinner + C_G * (eb ** 2)
        return Rq, dRq

    def cpx_div(a, b):
        # (a_r + i a_i) / (b_r + i b_i) in iv
        den = b[0] * b[0] + b[1] * b[1]
        return ((a[0] * b[0] + a[1] * b[1]) / den, (a[1] * b[0] - a[0] * b[1]) / den)

    def cpx_mul(a, b):
        return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])

    def cpx_add(a, b):
        return (a[0] + b[0], a[1] + b[1])

    def cpx_sub(a, b):
        return (a[0] - b[0], a[1] - b[1])

    def poly_P_cpx(wr, wi, eb, tb):
        # Evaluate P(w) and P'(w) at complex iv (wr, wi)
        w = (wr, wi)
        w2 = cpx_mul(w, w)
        u1 = (1 + (1 - eb) * wr, (1 - eb) * wi)
        u2 = (w2[0] + (tb / ce2) * wr + 1 / ce2, w2[1] + (tb / ce2) * wi)
        om = (1 - eb * wr, -eb * wi)
        om2 = cpx_mul(om, om)
        om3 = cpx_mul(om2, om)
        t1 = cpx_mul(u1, u2)
        t2 = cpx_mul((C_G * wr, C_G * wi), om3)
        P = cpx_add(t1, t2)
        # dP = (1-e)*u2 + u1*(2w + t/ce2) + c_g * om^2 * (1 - 4*e*w)
        d1 = ((1 - eb) * u2[0], (1 - eb) * u2[1])
        d2 = cpx_mul(u1, (2 * wr + tb / ce2, 2 * wi))
        d3 = cpx_mul(om2, (C_G * (1 - 4 * eb * wr), -4 * C_G * eb * wi))
        dP = cpx_add(cpx_add(d1, d2), d3)
        return P, dP

    def iv_cpx_log1m(eb, wr, wi):
        """Rigorous enclosure of  log(1 - e*w) / (-e)  for complex w = wr + i wi, SMOOTH AT e = 0!!
        Recall:  -log(1 - e*w) / e = w * sum_{k=0}^inf (e*w)^k / (k + 1)!
        For small e <= 0.08: use exact degree-7 Taylor series + outward-rounded geometric remainder!
        For e > 0.08 (requiring eb.a > 0): use exact (log|1 - e*w|, atan2(-e*wi, 1 - e*wr)) / (-e)!"""
        e_hi = mp.mpf(eb.b)
        if e_hi <= mp.mpf("0.08"):
            ew = (eb * wr, eb * wi)
            ew_abs_hi = iv.mpf(mp.mpf(iv.sqrt(ew[0] * ew[0] + ew[1] * ew[1]).b))
            assert mp.mpf(ew_abs_hi.b) < mp.mpf("0.5")
            w_abs_hi = iv.mpf(mp.mpf(iv.sqrt(wr * wr + wi * wi).b))
            rem = mp.mpf(((ew_abs_hi ** 8) * w_abs_hi / (9 * (1 - ew_abs_hi))).b)
            acc = (iv.mpf(1), iv.mpf(0))
            pw = (iv.mpf(1), iv.mpf(0))
            for k in range(1, 8):
                pw = cpx_mul(pw, ew)
                acc = (acc[0] + pw[0] / (k + 1), acc[1] + pw[1] / (k + 1))
            res = cpx_mul((wr, wi), acc)
            rb = iv.mpf([-rem, rem])
            return (res[0] + rb, res[1] + rb)
        else:
            assert mp.mpf(eb.a) > 0, f"eb.a not > 0 in iv_cpx_log1m: {eb}"
            zr = 1 - eb * wr; zi = -eb * wi
            assert mp.mpf(zr.a) > 0, f"Re(1-ew) not > 0: {zr}"
            re_log = iv.log(zr * zr + zi * zi) / 2
            im_log = iv.atan2(zi, zr)
            return (-re_log / eb, -im_log / eb)

    def iv_real_log1m(eb, w):
        """Rigorous enclosure of -log(1 - e*w) / e for real w < 0 (so 1 - e*w >= 1), smooth at e = 0!"""
        if mp.mpf(eb.b) <= mp.mpf("0.08"):
            ew = eb * w
            ew_hi = iv.mpf(max(abs(mp.mpf(ew.a)), abs(mp.mpf(ew.b))))
            assert mp.mpf(ew_hi.b) < mp.mpf("0.5")
            w_hi = iv.mpf(max(abs(mp.mpf(w.a)), abs(mp.mpf(w.b))))
            rem = mp.mpf(((ew_hi ** 8) * w_hi / (9 * (1 - ew_hi))).b)
            acc = iv.mpf(1); pw = iv.mpf(1)
            for k in range(1, 8):
                pw = pw * ew; acc = acc + pw / (k + 1)
            return w * acc + iv.mpf([-rem, rem])
        else:
            assert mp.mpf(eb.a) > 0, f"eb.a not > 0 in iv_real_log1m: {eb}"
            return -iv.log(1 - eb * w) / eb

    def certify_et_box(e0, e1, t0_b, t1_b):
        if e0 <= 0 and e1 > mp.mpf("0.08"):
            return False  # bisect cleanly across Taylor/exact threshold so eb.a > 0 in else-branch!
        eb = iv.mpf([e0, e1]); tb = iv.mpf([t0_b, t1_b])
        em = (e0 + e1) / 2; tm = (t0_b + t1_b) / 2
        # 1) Find approximate roots at midpoint (em, tm) in mpmath
        # P(w) = -c_g*em^3 w^4 + (1-em + 3*c_g*em^2) w^3 + (1 + (1-em)*tm/ce2 - 3*c_g*em) w^2
        #        + ((1-em)/ce2 + tm/ce2 + c_g) w + 1/ce2
        ce2_m = mp.mpf("5.25") ** 2; cg_m = mp.mpf("0.32")
        c4 = -cg_m * em**3
        c3 = (1 - em) + 3 * cg_m * em**2
        c2 = 1 + (1 - em) * tm / ce2_m - 3 * cg_m * em
        c1 = (1 - em + tm) / ce2_m + cg_m
        c0 = 1 / ce2_m
        # Find initial guesses from cubic [c3, c2, c1, c0] (immune to huge w4 ~ 1/em^3!), then polish on degree-4 P(w)!
        rts3 = mp.polyroots([c3, c2, c1, c0], maxsteps=100, extraprec=30)
        reals = sorted([mp.re(r) for r in rts3 if abs(mp.im(r)) < mp.mpf("1e-8")])
        cpx = [r for r in rts3 if mp.im(r) > mp.mpf("1e-8")]
        if len(reals) < 1 or len(cpx) != 1:
            return False
        w1_m = reals[0]
        w2_m = cpx[0]
        def eval_P4(z):
            v = (((c4 * z + c3) * z + c2) * z + c1) * z + c0
            dv = ((4 * c4 * z + 3 * c3) * z + 2 * c2) * z + c1
            return v, dv
        for _ in range(8):
            v, dv = eval_P4(w1_m); w1_m -= v / dv
            v, dv = eval_P4(w2_m); w2_m -= v / dv
        if w1_m >= 0 or mp.im(w2_m) <= 0:
            return False

        # 2) Real Krawczyk for w1 on box (eb, tb) using zero-cancellation centered forms:
        w1_iv0 = iv.mpf(w1_m)
        P1m = poly_P_mv(w1_m, em, tm, eb, tb)
        _, dP1m0 = poly_P_and_dP(w1_iv0, iv.mpf(em), iv.mpf(tm))
        rad1 = max(abs(mp.mpf((P1m / dP1m0).a)), abs(mp.mpf((P1m / dP1m0).b))) * mp.mpf("1.8") + mp.mpf("1e-15")
        W1 = iv.mpf([w1_m - rad1, w1_m + rad1])
        dP1W = poly_dP_mv(W1, w1_m, em, tm, eb, tb)
        if mp.mpf(dP1W.a) <= 0 and mp.mpf(dP1W.b) >= 0:
            return False
        dP1_mid = iv.mpf((mp.mpf(dP1W.a) + mp.mpf(dP1W.b)) / 2)
        K1 = w1_iv0 - P1m / dP1_mid + (1 - dP1W / dP1_mid) * (W1 - w1_iv0)
        if not (mp.mpf(K1.a) > mp.mpf(W1.a) and mp.mpf(K1.b) < mp.mpf(W1.b) and mp.mpf(K1.b) < 0):
            return False
        w1_iv = K1

        # 3) Complex Krawczyk for w2 on box (eb, tb) using zero-cancellation centered forms:
        w2r_m, w2i_m = mp.re(w2_m), mp.im(w2_m)
        w2r_0, w2i_0 = iv.mpf(w2r_m), iv.mpf(w2i_m)
        P2m = poly_P_cpx_mv(w2r_m, w2i_m, em, tm, eb, tb)
        _, dP2m0 = poly_P_cpx(w2r_0, w2i_0, iv.mpf(em), iv.mpf(tm))
        step2 = cpx_div(P2m, dP2m0)
        rad2 = max(abs(mp.mpf(step2[0].a)), abs(mp.mpf(step2[0].b)),
                   abs(mp.mpf(step2[1].a)), abs(mp.mpf(step2[1].b))) * mp.mpf("1.6") + mp.mpf("1e-15")
        W2r = iv.mpf([w2r_m - rad2, w2r_m + rad2])
        W2i = iv.mpf([w2i_m - rad2, w2i_m + rad2])
        if mp.mpf(W2i.a) <= 0:
            return False
        dP2W = poly_dP_cpx_mv(W2r, W2i, w2r_m, w2i_m, em, tm, eb, tb)
        J_m = ((mp.mpf(dP2W[0].a) + mp.mpf(dP2W[0].b)) / 2, (mp.mpf(dP2W[1].a) + mp.mpf(dP2W[1].b)) / 2)
        if J_m[0]**2 + J_m[1]**2 < mp.mpf("1e-20"):
            return False
        # K2 = w2_m - P2m/J_m + (1 - dP2W/J_m)*(W2 - w2_m)
        q2 = cpx_div(P2m, (iv.mpf(J_m[0]), iv.mpf(J_m[1])))
        rat2 = cpx_div(dP2W, (iv.mpf(J_m[0]), iv.mpf(J_m[1])))
        one_m_rat = (1 - rat2[0], -rat2[1])
        dW2 = (W2r - w2r_0, W2i - w2i_0)
        K2_off = cpx_sub(cpx_mul(one_m_rat, dW2), q2)
        K2r = w2r_0 + K2_off[0]; K2i = w2i_0 + K2_off[1]
        if not (mp.mpf(K2r.a) > mp.mpf(W2r.a) and mp.mpf(K2r.b) < mp.mpf(W2r.b)
                and mp.mpf(K2i.a) > mp.mpf(W2i.a) and mp.mpf(K2i.b) < mp.mpf(W2i.b)):
            return False
        w2r_iv, w2i_iv = K2r, K2i

        # 4) Real Krawczyk for q4 = y4 / eps^2 = 1 / (eps^2 * r4) on box (eb, tb)!
        q4_m = mp.mpf("-0.32")
        for _ in range(15):
            r_v, dr_v = poly_Rq_and_dRq(iv.mpf(q4_m), iv.mpf(em), iv.mpf(tm))
            q4_m -= mp.mpf(r_v.a) / mp.mpf(dr_v.a)
        q4_0 = iv.mpf(q4_m)
        R4m, dR4m = poly_Rq_and_dRq(q4_0, eb, tb)
        rad4 = max(abs(mp.mpf((R4m / dR4m).a)), abs(mp.mpf((R4m / dR4m).b))) * mp.mpf("2.5") + mp.mpf("1e-15")
        Q4 = iv.mpf([q4_m - rad4, q4_m + rad4])
        _, dR4W = poly_Rq_and_dRq(Q4, eb, tb)
        if mp.mpf(dR4W.a) <= 0 and mp.mpf(dR4W.b) >= 0:
            return False
        dR4_mid = iv.mpf((mp.mpf(dR4W.a) + mp.mpf(dR4W.b)) / 2)
        K4 = q4_0 - R4m / dR4_mid + (1 - dR4W / dR4_mid) * (Q4 - q4_0)
        if not (mp.mpf(K4.a) > mp.mpf(Q4.a) and mp.mpf(K4.b) < mp.mpf(Q4.b) and mp.mpf(K4.b) < 0):
            return False
        q4_iv = K4

        # 5) Compute A1, A2, C2 = (A2/A1)*(r1/r2), psi = (log r1 - log r2)/eps, and |A4/A1 * r1/r4|!
        # Use explicit hull(K, w_m) so MVT expansion around w_m is unconditionally rigorous!
        dP1 = poly_dP_mv(iv_hull(w1_iv, w1_m), w1_m, em, tm, eb, tb)
        N1 = (1 + (1 - eb) * w1_iv) * (1 + tb * w1_iv)
        A1 = N1 / dP1
        if mp.mpf(A1.a) <= 0:
            return False
        dP2 = poly_dP_cpx_mv(iv_hull(w2r_iv, w2r_m), iv_hull(w2i_iv, w2i_m), w2r_m, w2i_m, em, tm, eb, tb)
        N2 = cpx_mul((1 + (1 - eb) * w2r_iv, (1 - eb) * w2i_iv), (1 + tb * w2r_iv, tb * w2i_iv))
        A2 = cpx_div(N2, dP2)
        r1 = 1 - eb * w1_iv
        r2 = (1 - eb * w2r_iv, -eb * w2i_iv)
        r12 = cpx_div((r1, iv.mpf(0)), r2)
        C2 = cpx_mul((A2[0] / A1, A2[1] / A1), r12)

        # psi = (log r1 - log r2) / eps = (-log(1 - e*w2)/e) - (-log(1 - e*w1)/e)!
        l1 = iv_real_log1m(eb, w1_iv)
        l2 = iv_cpx_log1m(eb, w2r_iv, w2i_iv)
        psi = (l2[0] - l1, l2[1])
        if mp.mpf(psi[0].b) >= 0:
            return False  # need Re(psi) < 0 strictly!

        # Bound A4 * (r1 / r4) / A1 (100% outward-rounded iv upper bounds):
        y4 = (eb ** 2) * q4_iv
        _, Rprime4 = poly_Rq_and_dRq(q4_iv, eb, tb)
        if mp.mpf(Rprime4.a) <= 0 and mp.mpf(Rprime4.b) >= 0:
            return False
        B4 = q4_iv * r1 * (y4 - (1 - eb)) * (eb * y4 + tb * (y4 - 1)) / (A1 * Rprime4)
        r1r4_hi = mp.mpf((r1 * (eb ** 2) * (-q4_iv)).b)
        if r1r4_hi >= mp.mpf("0.2"):
            return False
        r1r4_hi_iv = iv.mpf(r1r4_hi)
        B4_abs_iv = iv.mpf(max(abs(mp.mpf(B4.a)), abs(mp.mpf(B4.b))))
        eb_hi_iv = iv.mpf(mp.mpf(eb.b))
        c4_slope_hi = mp.mpf(((1 + r1r4_hi_iv) * eb_hi_iv * B4_abs_iv).b)
        c4_n1_hi = mp.mpf((r1r4_hi_iv * (eb_hi_iv ** 2) * B4_abs_iv).b)

        # 6) Check ALL THREE t-regions:
        #   Region A: t in [0, 2.0]: check dPhi/dt = 2*Re(C2 * psi * exp(t*psi)) > c4_slope_hi!
        C2_psi = cpx_mul(C2, psi)
        for k in range(8):
            tb_s = iv.mpf([mp.mpf(k) / 4, mp.mpf(k + 1) / 4])
            er = iv.exp(tb_s * psi[0])
            ang = tb_s * psi[1]
            ex = (er * iv.cos(ang), er * iv.sin(ang))
            dPhi = 2 * (C2_psi[0] * ex[0] - C2_psi[1] * ex[1])
            if mp.mpf(dPhi.a) <= c4_slope_hi:
                return False

        #   Region B: t in [2.0, 4.5]: check 1 + 2*Re(C2 * exp(t*psi)) - c4_n1_hi > 0!
        for k in range(10):
            tb_s = iv.mpf([mp.mpf(2) + mp.mpf(k) / 4, mp.mpf(2) + mp.mpf(k + 1) / 4])
            er = iv.exp(tb_s * psi[0])
            ang = tb_s * psi[1]
            ex = (er * iv.cos(ang), er * iv.sin(ang))
            Phi = 1 + 2 * (C2[0] * ex[0] - C2[1] * ex[1]) - iv.mpf(c4_n1_hi)
            if mp.mpf(Phi.a) <= 0:
                return False

        #   Region C: t >= 4.5: check 2*|C2|*exp(4.5 * Re(psi)) + c4_n1_hi < 0.95 < 1!
        C2_abs_hi = iv.mpf(mp.mpf(iv.sqrt(C2[0] * C2[0] + C2[1] * C2[1]).b))
        psi_re_hi = iv.mpf(mp.mpf(psi[0].b))
        tail_hi = mp.mpf((2 * C2_abs_hi * iv.exp(iv.mpf("4.5") * psi_re_hi) + iv.mpf(c4_n1_hi)).b)
        if tail_hi >= mp.mpf("0.95"):
            return False

        return True

    # Branch-and-bound on the compact triangle 0 <= eps <= 0.51, eps <= tau <= 1.06!
    stack = [(mp.mpf(0), mp.mpf("0.51"), mp.mpf(0), mp.mpf("1.06"), 0)]
    n_boxes = 0
    while stack:
        e0, e1, t0_b, t1_b, dep = stack.pop()
        if t1_b < e0:  # completely outside eps <= tau!
            continue
        if certify_et_box(e0, e1, t0_b, t1_b):
            n_boxes += 1
            continue
        assert dep < 22, f"Module 2 failed at eps=[{e0},{e1}], tau=[{t0_b},{t1_b}]"
        if (t1_b - t0_b) > (e1 - e0):
            tm = (t0_b + t1_b) / 2
            stack.append((e0, e1, tm, t1_b, dep + 1))
            stack.append((e0, e1, t0_b, tm, dep + 1))
        else:
            em = (e0 + e1) / 2
            stack.append((em, e1, t0_b, t1_b, dep + 1))
            stack.append((e0, em, t0_b, t1_b, dep + 1))
    print(f"[MODULE 2 PASS] ALL n >= 0, ALL eps in [0, 0.51], ALL tau in [eps, 1.06] CERTIFIED in {n_boxes} iv boxes! ({time.time()-t0:.2f}s)")
    print(f"                ==> M_tilde_delta >=_PSD 0 for EVERY m >= 2 and EVERY delta in (0, delta_max(m)]!!")


if __name__ == "__main__":
    print("=" * 84)
    print("100% ZERO-FLOAT mpmath.iv CERTIFICATION OF ALL-m p=4/3 THEOREM (PART 1: MODULES 0, 1, 2)")
    print("=" * 84)
    certify_module_0()
    certify_module_1()
    certify_module_2()
    print("=" * 84)
    print("*** PART 1 (MODULES 0, 1, 2) 100% CERTIFIED WITH ZERO GAPS AND ZERO FLOATS!! ***")
    print("=" * 84)
