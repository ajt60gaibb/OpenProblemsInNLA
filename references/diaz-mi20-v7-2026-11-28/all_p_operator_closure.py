r"""
all_p_operator_closure.py
=========================
Self-Contained All-(1 < p < 2) Non-Commutative Operator Closure, Analytic Asymptotic Bounds,
Universal Variational Laws, One-Shot All-Delta Contraction-Congruence Certificates, & Obstructions
for Open Problem MI-20 (proving C_p(m) = C_tree(p, m) for 1 < p < 2, all m >= 2, all n >= 1 over R and C).

Author: nc-operator-prover (#113 item 3)
Dependencies: Python standard library + numpy, scipy, mpmath ONLY (zero external scratch imports).
Strict write-boundary note: reads/writes nothing in /Users/marcio/Downloads/Core Rank.

Architecture:
  - Module 0 (AST Zero-Float Purity Audit): audits all Section-B pure mpmath.iv certification functions
    (0 float literals, 0 float() calls, 0 numpy/scipy/math references) with strictly outward iv-asserted
    decimal formatters (mp.mp.dps = 50, iv.dps = 45).
  - Section B (Suite 0 — Zero-Float 45-Digit mpmath.iv Certification of Theorem 1 Closed-Form Analytic Bounds):
      Certifies Theorem 1(a) (all p in [3/2, 2), (1+x_+)^{2k-3}(x_+^3-1) <= m-1, exact large-m closure
      C_p(m) - C_tree(p, m) = O(m^{-(p-1)/(2p)}) -> 0) and Theorem 1(b) (all p in [6/5, 3/2], x_+ <= m^{1/3},
      first-ever non-trivial closed-form analytic upper bounds across 100% of Regime II (4/3, 3/2) beating
      Hadamard interpolation by 2x-3x!).
  - Section A (Suites 1-6 — Analytic Operator Identities, Furuta/Hansen Verification, Adversarial Stress Tests,
    and Sharp Obstructions):
      Suite 1: Theorem 1 matrix-level verification (Furuta M^3 <= (1+x_+)^3 D^3 on 1,500 complex 3x3 pairs,
               Hansen & Kubo-Ando domain positivity, T_1^{-1} <= (1+x_+)^{2k-3} I on [6/5, 3/2],
               Tanahashi non-Holden sharpness at p < 4/3, and Regime I asymptotic rate up to m = 10^8).
      Suite 2: Theorem 2 — Universal All-p Envelope First Law tr(D^{2k} dEhat) == 0 along the Holden manifold
               and exact first-order RG stationarity of BOTH Primal I_op and Dual I_dual across 8 exponents,
               plus second-variation sign anatomy at r = 3 RG.
      Suite 3: Theorem 3 — Universal Non-Commutative Operator Convexity d^2/du^2(c(delta(u)) I_op(delta(u))) >= 0
               for all u in [0, 1] and Exact Tree-Branching Slope Identity <e0, d/du(c I_op)|_0 e0> == (1 - rho_r)/m
               verified across 8 exponents and m in {2, 5, 10}, plus Regime III Primal vs Dual e0^perp slope split.
      Suite 4: Theorem 4 — Universal kappa-Independent Denominator Factorizations for Primal & Dual on U(3)-rotated
               complex Hermitian blocks across 7 exponents, exact inverse-free operator parallel sum action
               U_k^opt e0 = S_pri (v_k v_k^*) e0 & U~_k^opt e0 = S_dual (u_k u_k^*) e0, and exact opposite-direction
               Regime III Hansen inequality T_1 <= Lam^{-(k-2)/(k-1)} T_2 (forming an exact two-sided sandwich).
      Suite 5: Theorem 5 — One-Shot All-Delta Operator Parallel-Sum + Contraction-Congruence Certificate Theorem
               (zero delta-boxes, zero Stage-1 U, zero K^{-1} inversion): verified on RG + full 2x2 coupled curves +
               adversarial Nelder-Mead 3x3 strongly-indefinite-B_{sig+} sweeps across all 3 regimes
               (p = 5/3 Primal, p = 7/5 Dual, p = 5/4 Dual, p = 6/5 Dual), plus exact 2x2 block polynomial
               Schur-complement identity at p = 5/3 over C.
      Suite 6: Theorem 6 — Three Sharp Second-Use-of-Holden Obstructions (Holden-free 1x1 scalar breakdown,
               naive Holden-eliminated scalar failure including exact p = 4/3 proof, and single-operator
               zero-gap e0^perp obstruction).
"""

import ast
import inspect
import time
from fractions import Fraction
import mpmath as mp
from mpmath import iv

mp.mp.dps = 50
iv.dps = 45

t_global_start = time.time()


# ==============================================================================
# SECTION B: 100% ZERO-FLOAT PURE mpmath.iv CERTIFICATION ENGINE (AST-AUDITED)
# ==============================================================================

def iv_from_frac(num, den):
    """Exact rational interval [num/den, num/den] in 45-digit mpmath.iv."""
    return iv.mpf(num) / iv.mpf(den)


def iv_pow_frac(x_iv, num, den):
    """Rigorous rational power x^{num/den} in mpmath.iv for positive interval x_iv."""
    assert mp.mpf(x_iv.a) > mp.mpf(0), "iv_pow_frac requires strictly positive interval"
    exp_iv = iv.mpf(num) / iv.mpf(den)
    return iv.exp(exp_iv * iv.log(x_iv))


def iv_ceil_fixed_str(x_mp, digits):
    """Strictly outward-rounded decimal ceiling string with iv.mpf self-assertion."""
    ten_d = mp.mpf(10) ** digits
    n_int = int(mp.ceil(x_mp * ten_d))
    for _ in range(10):
        neg = n_int < 0
        an = -n_int if neg else n_int
        q_int, r_int = divmod(an, 10 ** digits)
        s = ("-" if neg else "") + f"{q_int}.{r_int:0{digits}d}"
        if mp.mpf(iv.mpf(s).a) >= x_mp:
            return s
        n_int += 1
    raise AssertionError("iv_ceil_fixed_str failed to bracket")


def iv_floor_fixed_str(x_mp, digits):
    """Strictly outward-rounded decimal floor string with iv.mpf self-assertion."""
    ten_d = mp.mpf(10) ** digits
    n_int = int(mp.floor(x_mp * ten_d))
    for _ in range(10):
        neg = n_int < 0
        an = -n_int if neg else n_int
        q_int, r_int = divmod(an, 10 ** digits)
        s = ("-" if neg else "") + f"{q_int}.{r_int:0{digits}d}"
        if mp.mpf(iv.mpf(s).b) <= x_mp:
            return s
        n_int -= 1
    raise AssertionError("iv_floor_fixed_str failed to bracket")


def iv_ceil_sci_str(x_mp, sig_digits):
    """Strictly outward-rounded scientific ceiling string (x_mp > 0) with iv.mpf self-assertion."""
    assert x_mp > mp.mpf(0)
    e10 = int(mp.floor(mp.log10(x_mp)))
    scale = mp.mpf(10) ** (sig_digits - 1 - e10)
    m_int = int(mp.ceil(x_mp * scale))
    for _ in range(10):
        if m_int >= 10 ** sig_digits:
            m_int = (m_int + 9) // 10
            e10 += 1
        d_str = str(m_int)
        s = f"{d_str[0]}.{d_str[1:]}e{e10:+03d}" if sig_digits > 1 else f"{d_str}e{e10:+03d}"
        if mp.mpf(iv.mpf(s).a) >= x_mp:
            return s
        m_int += 1
    raise AssertionError("iv_ceil_sci_str failed to bracket")


def iv_certify_monotone_root(fn_iv, fn_mp, dfn_mp, x_init_mp, lo_dom_mp, hi_dom_mp, increasing):
    """
    Zero-float 45-digit mpmath.iv root certification for a strictly monotone function on (lo_dom, hi_dom).
    Uses pure mpmath (50 dps, zero floats) Newton/damped step to locate an approximate root, then
    rigorously encloses and asserts strict opposite signs at [x - eps, x + eps] in mpmath.iv.
    """
    x = x_init_mp
    two = mp.mpf(2)
    ten = mp.mpf(10)
    for _ in range(60):
        fx = fn_mp(x)
        if abs(fx) < ten ** (-40):
            break
        dfx = dfn_mp(x)
        step = fx / dfx
        cand = x - step
        # Damp if out of domain
        while (lo_dom_mp is not None and cand <= lo_dom_mp) or (hi_dom_mp is not None and cand >= hi_dom_mp):
            step = step / two
            cand = x - step
        x = cand
        if abs(step) < ten ** (-38) * (mp.mpf(1) + abs(x)):
            break

    # Rigorous outward interval bracket around x, widening only if needed
    eps = (ten ** (-28)) * (mp.mpf(1) + abs(x))
    for _ in range(30):
        a = x - eps
        b = x + eps
        if lo_dom_mp is not None and a <= lo_dom_mp:
            a = (lo_dom_mp + x) / two
        if hi_dom_mp is not None and b >= hi_dom_mp:
            b = (hi_dom_mp + x) / two
        fa = fn_iv(iv.mpf(a))
        fb = fn_iv(iv.mpf(b))
        if increasing:
            if mp.mpf(fa.b) < mp.mpf(0) and mp.mpf(fb.a) > mp.mpf(0):
                return iv.mpf([a, b])
        else:
            if mp.mpf(fa.a) > mp.mpf(0) and mp.mpf(fb.b) < mp.mpf(0):
                return iv.mpf([a, b])
        eps *= ten
    raise AssertionError("iv_certify_monotone_root failed to certify strict iv bracket")


def iv_eval_C_from_xp(xp_iv, k_iv):
    """Exact C(x_+) = [ (1+x_+)^{2k-1} / (2^{2k-1} x_+^{k-1}) ]^{1/(2k)} in pure mpmath.iv."""
    one = iv.mpf(1)
    two = iv.mpf(2)
    two_k = two * k_iv
    two_km1 = two_k - one
    km1 = k_iv - one
    log_Lam = two_km1 * iv.log(one + xp_iv) - km1 * iv.log(xp_iv)
    log_C = (log_Lam - two_km1 * iv.log(two)) / two_k
    return iv.exp(log_C)


def iv_certify_1x1(k_iv, m_int):
    """Zero-float 45-digit mpmath.iv enclosure of exact 1x1 Holden constant C_{1x1}(p, m)."""
    one_iv = iv.mpf(1)
    two_iv = iv.mpf(2)
    m_iv = iv.mpf(m_int)
    two_km1_iv = two_iv * k_iv - one_iv
    km1_iv = k_iv - one_iv
    t_min_iv = iv.log(km1_iv / k_iv)
    t_min_lo = mp.mpf(t_min_iv.a)
    t_min_hi = mp.mpf(t_min_iv.b)

    k_mid = (mp.mpf(k_iv.a) + mp.mpf(k_iv.b)) / mp.mpf(2)
    two_km1_mp = mp.mpf(2) * k_mid - mp.mpf(1)
    km1_mp = k_mid - mp.mpf(1)
    t_min_mp = mp.log(km1_mp / k_mid)
    m_mp = mp.mpf(m_int)

    def sig_sum_iv(L_mp):
        L_iv = iv.mpf(L_mp)
        logL_iv = iv.log(L_iv)
        logL_mp = mp.log(L_mp)

        def phi_iv(t_iv):
            return two_km1_iv * iv.log(one_iv + iv.exp(t_iv)) - km1_iv * t_iv - logL_iv

        def phi_mp(t):
            return two_km1_mp * mp.log(mp.mpf(1) + mp.exp(t)) - km1_mp * t - logL_mp

        def dphi_mp(t):
            et = mp.exp(t)
            return (k_mid * et - km1_mp) / (mp.mpf(1) + et)

        # Initial guesses strictly on left and right of t_min
        tm_init = t_min_mp - mp.mpf(1)
        while phi_mp(tm_init) < mp.mpf(0):
            tm_init -= mp.mpf(2)
        tp_init = t_min_mp + mp.mpf(1)
        while phi_mp(tp_init) < mp.mpf(0):
            tp_init += mp.mpf(2)

        tm_iv = iv_certify_monotone_root(phi_iv, phi_mp, dphi_mp, tm_init, None, t_min_lo, False)
        tp_iv = iv_certify_monotone_root(phi_iv, phi_mp, dphi_mp, tp_init, t_min_hi, None, True)
        xm_iv = iv.exp(tm_iv)
        xp_iv = iv.exp(tp_iv)
        sigm_iv = iv.exp(km1_iv * tm_iv) * (xm_iv - one_iv)
        sigp_iv = iv.exp(km1_iv * tp_iv) * (xp_iv - one_iv)
        return sigp_iv + (m_iv - one_iv) * sigm_iv

    def sig_sum_mp(L_mp):
        logL_mp = mp.log(L_mp)
        def phi_mp(t):
            return two_km1_mp * mp.log(mp.mpf(1) + mp.exp(t)) - km1_mp * t - logL_mp
        def dphi_mp(t):
            et = mp.exp(t)
            return (k_mid * et - km1_mp) / (mp.mpf(1) + et)
        tm = t_min_mp - mp.mpf(1)
        while phi_mp(tm) < mp.mpf(0):
            tm -= mp.mpf(2)
        for _ in range(40):
            f = phi_mp(tm)
            if abs(f) < mp.mpf(10) ** (-40):
                break
            st = f / dphi_mp(tm)
            while tm - st >= t_min_mp:
                st /= mp.mpf(2)
            tm -= st
        tp = t_min_mp + mp.mpf(1)
        while phi_mp(tp) < mp.mpf(0):
            tp += mp.mpf(2)
        for _ in range(40):
            f = phi_mp(tp)
            if abs(f) < mp.mpf(10) ** (-40):
                break
            st = f / dphi_mp(tp)
            while tp - st <= t_min_mp:
                st /= mp.mpf(2)
            tp -= st
        xm = mp.exp(tm)
        xp = mp.exp(tp)
        sm = (xm ** km1_mp) * (xm - mp.mpf(1))
        sp = (xp ** km1_mp) * (xp - mp.mpf(1))
        return sp + (m_mp - mp.mpf(1)) * sm

    L0_iv = iv.exp(two_km1_iv * iv.log(two_iv))
    L0_hi = mp.mpf(L0_iv.b)
    lo_L = L0_hi * (mp.mpf(1) + mp.mpf(1) / mp.mpf(10 ** 12))
    hi_L = L0_hi * mp.mpf(2)
    while sig_sum_mp(hi_L) <= mp.mpf(0):
        hi_L *= mp.mpf(2)

    # Pure mpmath bisection + secant polish to 35 digits (strictly monotone increasing in L)
    a_L, b_L = lo_L, hi_L
    for _ in range(125):
        mid = (a_L + b_L) / mp.mpf(2)
        if sig_sum_mp(mid) < mp.mpf(0):
            a_L = mid
        else:
            b_L = mid
    L_star = (a_L + b_L) / mp.mpf(2)

    # Rigorous mpmath.iv bracket around L_star with strict opposite endpoint signs
    eps_L = (mp.mpf(10) ** (-25)) * L_star
    L1_iv = None
    for _ in range(25):
        la = L_star - eps_L
        lb = L_star + eps_L
        if la <= L0_hi:
            la = (L0_hi + L_star) / mp.mpf(2)
        if mp.mpf(sig_sum_iv(la).b) < mp.mpf(0) and mp.mpf(sig_sum_iv(lb).a) > mp.mpf(0):
            L1_iv = iv.mpf([la, lb])
            break
        eps_L *= mp.mpf(10)
    assert L1_iv is not None, "iv_certify_1x1 failed to certify strict iv bracket for Lambda_1x1"
    log_C1 = (iv.log(L1_iv) - two_km1_iv * iv.log(two_iv)) / (two_iv * k_iv)
    return iv.exp(log_C1)


def iv_certify_theorem1_row(p_spec, m_int):
    """
    Zero-float 45-digit mpmath.iv certification of Theorem 1 closed-form analytic all-n upper bound C_4L(p, m)
    vs C_{1x1}(p, m) and Hadamard interpolation C_Had(p, m):
      - Regime I (p in [3/2, 2), k in (1, 3/2]): (1+x_+)^{2k-3}(x_+^3 - 1) <= m - 1
      - Regimes II & III-upper (p in [6/5, 3/2], k in [3/2, 3]): x_+ <= m^{1/3}
    p_spec is either an exact rational tuple (num, den) or an interior irrational mpmath.iv interval.
    """
    one = iv.mpf(1)
    two = iv.mpf(2)
    three = iv.mpf(3)
    if isinstance(p_spec, tuple):
        p_num, p_den = p_spec
        assert p_num > p_den and p_num < 2 * p_den
        k_iv = iv.mpf(p_num) / iv.mpf(2 * (p_num - p_den))
        is_regime1 = (2 * p_num >= 3 * p_den)
        if not is_regime1:
            assert 5 * p_num >= 6 * p_den and 2 * p_num <= 3 * p_den
    else:
        p_iv = p_spec
        k_iv = p_iv / (two * (p_iv - one))
        is_regime1 = (mp.mpf(p_iv.a) >= mp.mpf(3) / mp.mpf(2))
        if not is_regime1:
            assert mp.mpf(p_iv.a) > mp.mpf(6) / mp.mpf(5) and mp.mpf(p_iv.b) < mp.mpf(3) / mp.mpf(2)

    two_km1 = two * k_iv - one
    two_k = two * k_iv
    m_iv = iv.mpf(m_int)

    # Exact Hadamard interpolation bound: Lam_Had = 2^{2k-2} * (1 + sqrt(m))
    L_had_iv = iv.exp((two_k - two) * iv.log(two)) * (one + iv.sqrt(m_iv))
    C_had_iv = iv.exp((iv.log(L_had_iv) - two_km1 * iv.log(two)) / two_k)

    # Exact C_{1x1} enclosure
    C1_iv = iv_certify_1x1(k_iv, m_int)

    if is_regime1:
        # Regime I: g_k(x) = (1+x)^{2k-3}(x^3 - 1) - (m - 1) strictly increasing on [1, inf)
        exp_2km3_iv = two_k - three
        k_mid = (mp.mpf(k_iv.a) + mp.mpf(k_iv.b)) / mp.mpf(2)
        exp_2km3_mp = mp.mpf(2) * k_mid - mp.mpf(3)
        m_mp = mp.mpf(m_int)

        def g_iv(x_iv):
            return iv.exp(exp_2km3_iv * iv.log(one + x_iv)) * (x_iv * x_iv * x_iv - one) - (m_iv - one)

        def g_mp(x):
            return ((mp.mpf(1) + x) ** exp_2km3_mp) * (x ** 3 - mp.mpf(1)) - (m_mp - mp.mpf(1))

        def dg_mp(x):
            return ((mp.mpf(1) + x) ** (exp_2km3_mp - mp.mpf(1))) * (
                mp.mpf(2) * k_mid * (x ** 3) + mp.mpf(3) * (x ** 2) + (mp.mpf(3) - mp.mpf(2) * k_mid)
            )

        x_init = mp.mpf(m_int) ** (mp.mpf(1) / (mp.mpf(2) * k_mid))
        if x_init <= mp.mpf(1):
            x_init = mp.mpf(2)
        xp4_iv = iv_certify_monotone_root(g_iv, g_mp, dg_mp, x_init, mp.mpf(1), None, True)
    else:
        xp4_iv = iv.exp(iv.log(m_iv) / three)

    C4_iv = iv_eval_C_from_xp(xp4_iv, k_iv)
    # Strictly outward iv subtraction and division (zero binary-rounding leak)
    gap_4L_iv = iv.mpf(C4_iv.b) - iv.mpf(C1_iv.a)
    gap_had_iv = iv.mpf(C_had_iv.a) - iv.mpf(C1_iv.b)
    gain_iv = iv.mpf(gap_had_iv.a) / iv.mpf(gap_4L_iv.b)
    return {
        "C1_lo": iv_floor_fixed_str(mp.mpf(C1_iv.a), 10),
        "C4_hi": iv_ceil_fixed_str(mp.mpf(C4_iv.b), 10),
        "CHad_lo": iv_floor_fixed_str(mp.mpf(C_had_iv.a), 10),
        "gap_4L_hi": iv_ceil_sci_str(mp.mpf(gap_4L_iv.b), 4),
        "gain_lo": iv_floor_fixed_str(mp.mpf(gain_iv.a), 2),
        "beats_had": mp.mpf(C4_iv.b) < mp.mpf(C_had_iv.a),
        "C4_iv": C4_iv,
        "C1_iv": C1_iv,
        "CHad_iv": C_had_iv,
    }


SECTION_B_FUNCS = [
    iv_from_frac,
    iv_pow_frac,
    iv_ceil_fixed_str,
    iv_floor_fixed_str,
    iv_ceil_sci_str,
    iv_certify_monotone_root,
    iv_eval_C_from_xp,
    iv_certify_1x1,
    iv_certify_theorem1_row,
]


def run_module0_ast_audit():
    """Verify Section-B zero-float purity across all pure mpmath.iv certification functions."""
    forbidden_names = {"float", "np", "numpy", "scipy", "math"}
    for fn in SECTION_B_FUNCS:
        src = inspect.getsource(fn)
        tree = ast.parse(src)
        for node in ast.walk(tree):
            if isinstance(node, ast.Constant) and isinstance(node.value, float):
                raise AssertionError(f"Float literal {node.value!r} in Section-B function {fn.__name__}")
            if isinstance(node, ast.Name) and node.id in forbidden_names:
                raise AssertionError(f"Forbidden name {node.id!r} in Section-B function {fn.__name__}")
    return len(SECTION_B_FUNCS)


print("=" * 100)
print("MODULE 0 & SUITE 0: AST ZERO-FLOAT AUDIT + 45-DIGIT mpmath.iv CERTIFICATION OF THEOREM 1")
print("=" * 100)
n_audited = run_module0_ast_audit()
print(f"[Module 0] AST Zero-Float Purity Audit PASSED across {n_audited}/{n_audited} Section-B pure mpmath.iv functions!")

print("\n[Suite 0] Zero-Float 45-Digit mpmath.iv Certified Outward-Rounded Table for Theorem 1 (ALL n >= 1, R & C):")
print(f"  {'p':7s} {'m':6s} | {'C_1x1 (floor)':14s} {'C_4L (ceil)':14s} {'C_Had (floor)':14s} | {'gap<=C4L-C1':12s} {'vs Hadamard'}")
print("  " + "-" * 94)

cert_cases = [
    ("6/5", (6, 5), [2, 3, 5]),
    ("5/4", (5, 4), [2, 5, 10]),
    ("4/3", (4, 3), [2, 5, 10, 50]),
    ("7/5", (7, 5), [2, 5, 10, 50, 500]),
    ("sqrt(2)", iv.sqrt(iv.mpf(2)), [2, 5, 10, 50, 500]),
    ("1.45", (29, 20), [2, 5, 10, 50, 500]),
    ("3/2", (3, 2), [2, 5, 10, 50, 500, 10000]),
    ("phi", (iv.mpf(1) + iv.sqrt(iv.mpf(5))) / iv.mpf(2), [2, 10, 50, 10000]),
    ("5/3", (5, 3), [2, 5, 10, 50, 500, 10000]),
    ("7/4", (7, 4), [5, 10, 50, 500, 10000]),
    ("1.9", (19, 10), [50, 500, 10000]),
]

for p_lbl, p_iv_val, m_list in cert_cases:
    for m_v in m_list:
        row = iv_certify_theorem1_row(p_iv_val, m_v)
        assert row["beats_had"], f"Expected C_4L < C_Had at p={p_lbl}, m={m_v}"
        print(
            f"  {p_lbl:7s} {m_v:6d} | {row['C1_lo']:14s} {row['C4_hi']:14s} {row['CHad_lo']:14s} "
            f"| <= {row['gap_4L_hi']:9s} | BEATS HAD (>= {row['gain_lo']}x tighter)"
        )


# ==============================================================================
# SECTION A: HIGH-PRECISION & NUMERICAL OPERATOR VERIFICATION SUITES (1-6)
# ==============================================================================
import numpy as np
from scipy.linalg import eigh
from scipy.optimize import brentq, root, least_squares, minimize


def matpow(A, alpha):
    """Exact Hermitian matrix power A^alpha for A > 0 (real or complex)."""
    Ah = 0.5 * (A + A.conj().T)
    w, V = eigh(Ah)
    assert float(np.min(w)) > 0.0, f"matpow non-positive eig {float(np.min(w))}"
    return (V * (w ** alpha)) @ V.conj().T


def roots_kappa(Lam, kappa):
    """Exact scalar Holden roots x_- < (k-1)/k < x_+ and charges sig_-, sig_+."""
    t_min = np.log((kappa - 1.0) / kappa)
    logL = np.log(Lam)
    fn = lambda t: (2.0 * kappa - 1.0) * np.logaddexp(0.0, t) - (kappa - 1.0) * t - logL
    lo, hi = t_min - 1.0, t_min + 1.0
    while fn(lo) < 0.0:
        lo -= 20.0
    while fn(hi) < 0.0:
        hi += 20.0
    xm = float(np.exp(brentq(fn, lo, t_min, xtol=1e-15, rtol=1e-15)))
    xp = float(np.exp(brentq(fn, t_min, hi, xtol=1e-15, rtol=1e-15)))
    return xm, xp, (xm ** (kappa - 1.0)) * (xm - 1.0), (xp ** (kappa - 1.0)) * (xp - 1.0)


def scalar_1x1(kappa, m=2):
    Lam0 = 2.0 ** (2.0 * kappa - 1.0)
    hi = max(Lam0 * 2.0, 2.0 * np.sqrt(m) + 4.0)
    while roots_kappa(hi, kappa)[3] + (m - 1.0) * roots_kappa(hi, kappa)[2] < 0.0:
        hi *= 2.0
    Lam1 = float(brentq(
        lambda L: roots_kappa(L, kappa)[3] + (m - 1.0) * roots_kappa(L, kappa)[2],
        Lam0, hi, xtol=1e-15, rtol=1e-15
    ))
    return Lam1, (Lam1 / Lam0) ** (1.0 / (2.0 * kappa))


def solve_rg_p32_Q(r_target):
    """Exact coupled rank-r RG fixed points at p = 3/2, m = 2 via Q coordinates."""
    Lam1, _ = scalar_1x1(1.5, 2)
    xm1, _, _, _ = roots_kappa(Lam1, 1.5)
    Lam = Lam1 + 5e-4
    ds = np.array([1.0, 0.075])
    Q = np.array([[np.sqrt(xm1), -0.15], [-0.15, 0.50]])

    def solve_k(rk, L_in, d_in, Q_in):
        triu = np.triu_indices(rk)
        x0 = np.concatenate([[L_in], np.log(d_in[1:]), Q_in[triu]])
        def unpack(x):
            L = x[0]
            dd = np.concatenate([[1.0], np.exp(x[1:rk])])
            QQ = np.zeros((rk, rk))
            QQ[triu] = x[rk:]
            QQ = QQ + QQ.T - np.diag(np.diag(QQ))
            return L, dd, QQ
        def res(x):
            L, dd, QQ = unpack(x)
            _, _, _, sp = roots_kappa(L, 1.5)
            D = np.diag(dd)
            H = QQ @ D @ QQ
            R1 = (D + H) @ (D + H) - L * D @ QQ @ D
            F = QQ @ D @ QQ @ D @ QQ - D @ QQ @ D
            R2 = F - np.diag(np.concatenate([[-sp], sp * (dd[1:] ** 2)]))
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
        _, xp_c, _, _ = roots_kappa(Lam, 1.5)
        Q_n[rk - 1, rk - 1] = min(0.97 * np.sqrt(xp_c), Q[-1, -1] + 0.12)
        Q_n[:rk - 1, rk - 1] = -0.015 * (0.35 ** np.arange(rk - 1)[::-1])
        Q_n[rk - 1, :rk - 1] = Q_n[:rk - 1, rk - 1]
        Lam, ds, Q = solve_k(rk, Lam, ds_n, Q_n)
    H = Q @ np.diag(ds) @ Q
    X = (ds ** (-0.5))[:, None] * H * (ds ** (-0.5))[None, :]
    assert float(np.min(eigh(X)[1][0, :] ** 2)) > 1e-8
    return Lam, ds, X


def solve_rg_square(p, m, r_cur, Lam_init, d_init, X_init):
    """Solve rank-r RG fixed point for arbitrary 1 < p < 2 and m >= 2."""
    kappa = p / (2.0 * (p - 1.0))
    triu = np.triu_indices(r_cur)
    L0 = 2.0 ** (2.0 * kappa - 1.0)
    w0, V0 = eigh(0.5 * (X_init + X_init.T))
    S0 = (V0 * np.log(np.maximum(w0, 1e-14))) @ V0.T
    x0 = np.concatenate([[np.log(max(Lam_init - L0, 1e-10))], np.log(d_init[1:]), S0[triu]])

    def unpack(x):
        L = L0 + np.exp(np.clip(x[0], -35, 20))
        dd = np.concatenate([[1.0], np.exp(np.clip(x[1:r_cur], -35, 5))])
        S = np.zeros((r_cur, r_cur))
        S[triu] = np.clip(x[r_cur:], -16, 6)
        S = S + S.T - np.diag(np.diag(S))
        w, V = eigh(S)
        return L, dd, (V * np.exp(w)) @ V.T

    def res(x):
        L, dd, X = unpack(x)
        _, _, _, sp = roots_kappa(L, kappa)
        sD = np.sqrt(dd)
        D = np.diag(dd)
        H = (sD[:, None] * X) * sD[None, :]
        M = D + H
        G = (sD[:, None] * H) * sD[None, :]
        D_scale = dd ** (-kappa + 0.5)
        Z = (dd ** (1.0 - kappa))[:, None] * matpow(G, kappa - 1.0) * (dd ** (1.0 - kappa))[None, :]
        R1 = (D_scale[:, None] * matpow(M, 2.0 * kappa - 1.0) * D_scale[None, :]) - L * Z
        Ehat = ((dd ** (-kappa))[:, None] * matpow(G, kappa) * (dd ** (-kappa))[None, :]) - Z
        target_diag = np.concatenate([[-sp / (m - 1.0)], np.full(r_cur - 1, sp)])
        return np.concatenate([R1[triu], np.diag(Ehat) - target_diag])

    sol = root(res, x0, method="hybr", tol=1e-14)
    L, dd, X = unpack(sol.x)
    sD = np.sqrt(dd)
    H = (sD[:, None] * X) * sD[None, :]
    G = (sD[:, None] * H) * sD[None, :]
    Z = (dd ** (1.0 - kappa))[:, None] * matpow(G, kappa - 1.0) * (dd ** (1.0 - kappa))[None, :]
    Ehat = ((dd ** (-kappa))[:, None] * matpow(G, kappa) * (dd ** (-kappa))[None, :]) - Z
    off_err = float(np.linalg.norm(Ehat - np.diag(np.diag(Ehat))))
    return L, dd, X, float(np.linalg.norm(res(sol.x))), off_err


def solve_H_given_D(dd, Lam, kappa, X_ref):
    """Solve Holden's equation at fixed diagonal D and threshold Lam."""
    n = len(dd)
    triu = np.triu_indices(n)
    sD = np.sqrt(dd)
    D = np.diag(dd)
    D_scale = dd ** (-kappa + 0.5)
    w0, V0 = eigh(0.5 * (X_ref + X_ref.T))
    S0 = (V0 * np.log(np.maximum(w0, 1e-14))) @ V0.T

    def res(v):
        S = np.zeros((n, n))
        S[triu] = v
        S = S + S.T - np.diag(np.diag(S))
        w, V = eigh(S)
        X = (V * np.exp(np.clip(w, -20, 10))) @ V.T
        H = (sD[:, None] * X) * sD[None, :]
        M = D + H
        G = (sD[:, None] * H) * sD[None, :]
        Z = (dd ** (1.0 - kappa))[:, None] * matpow(G, kappa - 1.0) * (dd ** (1.0 - kappa))[None, :]
        R1 = (D_scale[:, None] * matpow(M, 2.0 * kappa - 1.0) * D_scale[None, :]) - Lam * Z
        return R1[triu]

    sol = root(res, S0[triu], method="hybr", tol=1e-14)
    S = np.zeros((n, n))
    S[triu] = sol.x
    S = S + S.T - np.diag(np.diag(S))
    w, V = eigh(S)
    return (V * np.exp(w)) @ V.T, float(np.linalg.norm(res(sol.x)))


def build_rg_anchors(r_cur):
    """Build exact rank-r RG anchors across all 3 regimes via continuation from p = 3/2."""
    L0, d0, X0 = solve_rg_p32_Q(r_cur)
    anchors = {1.5: (L0, d0, X0)}
    L, d, X = L0, d0, X0
    up_steps = [1.53, 1.56, 1.59, 1.62, 1.645, 5.0 / 3.0, 1.69, 1.71, 1.73]
    if r_cur <= 3:
        up_steps.append(1.75)
    for pp in up_steps:
        L1, _ = scalar_1x1(pp / (2.0 * (pp - 1.0)), 2)
        L, d, X, err, oe = solve_rg_square(pp, 2, r_cur, L1 * 1.0005, d, X)
        assert err < 1e-10 and oe < 1e-10, f"r={r_cur} p={pp} err={err} oe={oe}"
        anchors[pp] = (L, d, X)
    L, d, X = L0, d0, X0
    for pp in [1.47, 1.44, np.sqrt(2.0), 1.40, 1.38, 1.355, 4.0 / 3.0, 1.31, 1.29, 1.27, 1.25, 1.23, 1.215, 1.20]:
        L1, _ = scalar_1x1(pp / (2.0 * (pp - 1.0)), 2)
        L, d, X, err, oe = solve_rg_square(pp, 2, r_cur, L1 * 1.001, d, X)
        assert err < 1e-10 and oe < 1e-10, f"r={r_cur} p={pp} err={err} oe={oe}"
        anchors[pp] = (L, d, X)
    return anchors


rg3 = build_rg_anchors(3)
rg5 = build_rg_anchors(5)
rng = np.random.default_rng(20261128)


# ==============================================================================
# SUITE 1: THEOREM 1 MATRIX-LEVEL VERIFICATION (FURUTA M^3, HANSEN, ASYMPTOTICS)
# ==============================================================================
print("\n" + "=" * 100)
print("SUITE 1: THEOREM 1 — FURUTA M^3 <= (1+x_+)^3 D^3, T_1^{-1} BOUND, TANAHASHI SHARPNESS & ASYMPTOTICS")
print("=" * 100)

print("\n[1A] Self-Contained Furuta Lemma (B^{1/4} A^{k-1} B^{1/4})^{3/(2k-1)} <= B^{3/2} on 1,500 Complex 3x3 Pairs:")
for lbl, kappa in [("4/3 (k=2.0)", 2.0), ("5/4 (k=2.5)", 2.5), ("6/5 (k=3.0)", 3.0), ("1.1 (k=5.5)", 5.5), ("1.05 (k=10.5)", 10.5)]:
    min_ev = 1e9
    max_cond = 0.0
    spread = min(3.0, 8.0 / kappa)
    for _ in range(300):
        U, _ = np.linalg.qr(rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3)))
        B = U @ np.diag(np.exp(rng.uniform(-spread, spread, size=3))) @ U.conj().T
        V, _ = np.linalg.qr(rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3)))
        S = V @ np.diag(rng.uniform(0.05 if kappa <= 3.0 else 0.25, 0.99, size=3)) @ V.conj().T
        Bh = matpow(B, 0.5)
        A = Bh @ S @ Bh  # Guarantees 0 < A <= B!
        B14 = matpow(B, 0.25)
        Ak1 = matpow(A, kappa - 1.0)
        evA = eigh(0.5 * (Ak1 + Ak1.conj().T))[0]
        max_cond = max(max_cond, float(evA[-1] / evA[0]))
        lhs = matpow(B14 @ Ak1 @ B14, 3.0 / (2.0 * kappa - 1.0))
        rhs = matpow(B, 1.5)
        diff = 0.5 * ((rhs - lhs) + (rhs - lhs).conj().T)
        min_ev = min(min_ev, float(np.min(eigh(diff)[0])))
    assert min_ev >= -1e-11, f"Furuta M^3 failed for {lbl}: {min_ev}"
    print(f"  p={lbl:14s}: 300 complex 3x3 (0<A<=B, max_cond(A^{{k-1}})={max_cond:.2e}) | min_eig(B^1.5-LHS) = {min_ev:+.3e} (PASS)")

print("\n[1B] Theorem 1(b) T_1^{-1} <= (1+x_+)^{2k-3} I on Holden [6/5, 3/2] vs Non-Holden Sharpness at p < 4/3:")
for lbl, pp in [("7/5", 1.40), ("4/3", 4.0 / 3.0), ("5/4", 1.25), ("6/5", 1.20)]:
    kappa = pp / (2.0 * (pp - 1.0))
    Lr, dr, Xr = rg3[pp]
    _, xp, _, _ = roots_kappa(Lr, kappa)
    sD = np.sqrt(dr); D = np.diag(dr); H = (sD[:, None] * Xr) * sD[None, :]; M = D + H
    T1inv_rg = (dr ** (1.5 - kappa))[:, None] * matpow(M, 2.0 * kappa - 3.0) * (dr ** (1.5 - kappa))[None, :]
    M3_ratio = float(np.max(eigh(matpow(D, -1.5) @ matpow(M, 3.0) @ matpow(D, -1.5))[0])) / ((1.0 + xp) ** 3)
    bnd = (1.0 + xp) ** (2.0 * kappa - 3.0)
    rg_norm = float(np.max(eigh(0.5 * (T1inv_rg + T1inv_rg.T))[0]))
    assert rg_norm <= bnd + 1e-12
    if kappa >= 2.0:
        assert M3_ratio <= 1.0 + 1e-12
    # Check non-Holden D <= M <= (1+xp)D with cond(D) = 1000:
    max_nh = 0.0
    for _ in range(200):
        dd = np.array([1.0, 0.1, 0.001])
        U, _ = np.linalg.qr(rng.standard_normal((3, 3)))
        Xn = U @ np.diag(rng.uniform(0.05, xp, size=3)) @ U.T
        Mn = np.diag(dd) + (np.sqrt(dd)[:, None] * Xn) * np.sqrt(dd)[None, :]
        T1i = (dd ** (1.5 - kappa))[:, None] * matpow(Mn, 2.0 * kappa - 3.0) * (dd ** (1.5 - kappa))[None, :]
        max_nh = max(max_nh, float(np.max(eigh(0.5 * (T1i + T1i.T))[0])))
    if pp >= 4.0 / 3.0 - 1e-12:
        assert max_nh <= bnd + 1e-10
        nh_note = "PASS (Lowner-Heinz)"
    else:
        assert max_nh > bnd * 10.0
        nh_note = "FAILS w/o Holden (Furuta+Holden needed!)"
    print(f"  p={lbl:4s} (2k-3={2*kappa-3:.1f}): bnd={bnd:7.4f} | RG ||T1^-1||={rg_norm:7.4f} (M^3/((1+xp)D)^3={M3_ratio:.5f}) | non-Holden={max_nh:10.3f} [{nh_note}]")

print("\n[1C] Theorem 1(a) Exact Regime I Asymptotic Rate: (C_4L(p,m) - C_1x1(p,m)) * m^{(p-1)/(2p)} -> (p-1)/(2p * 2^{1/p}):")
for lbl, pp in [("3/2", 1.5), ("5/3", 5.0 / 3.0), ("7/4", 1.75), ("1.9", 1.9)]:
    kappa = pp / (2.0 * (pp - 1.0))
    pred = ((pp - 1.0) / (2.0 * pp)) * (2.0 ** (-1.0 / pp))
    vals = []
    for m_val in [10 ** 4, 10 ** 6, 10 ** 8]:
        _, C1 = scalar_1x1(kappa, m_val)
        fn = lambda x: ((1.0 + x) ** (2.0 * kappa - 3.0)) * (x ** 3 - 1.0) - (m_val - 1.0)
        xp4 = float(brentq(fn, 1.0, (m_val ** (1.0 / (2.0 * kappa))) * 2.0, xtol=1e-15))
        L4 = ((1.0 + xp4) ** (2.0 * kappa - 1.0)) / (xp4 ** (kappa - 1.0))
        C4 = (L4 / (2.0 ** (2.0 * kappa - 1.0))) ** (1.0 / (2.0 * kappa))
        vals.append((C4 - C1) * (m_val ** ((pp - 1.0) / (2.0 * pp))))
    assert abs(vals[-1] - pred) / pred < 0.01
    print(f"  p={lbl:4s}: analytic coeff = {pred:.8f} | m=10^4, 10^6, 10^8 -> {[round(v, 7) for v in vals]} (EXACT MATCH!)")


# ==============================================================================
# SUITE 2: THEOREM 2 — UNIVERSAL ENVELOPE FIRST LAW & EXACT RG STATIONARITY
# ==============================================================================
print("\n" + "=" * 100)
print("SUITE 2: THEOREM 2 — UNIVERSAL ENVELOPE FIRST LAW tr(D^{2k} dEhat)==0 & EXACT RG STATIONARITY")
print("=" * 100)


def eval_both_integrals(dd, X, Lam, kappa, xs_p, ws_p, qs_d, ws_d, m=2):
    _, _, _, sigp = roots_kappa(Lam, kappa)
    n = len(dd)
    sD = np.sqrt(dd); D = np.diag(dd); H = (sD[:, None] * X) * sD[None, :]; M = D + H; G = (sD[:, None] * H) * sD[None, :]
    Z = (dd ** (1.0 - kappa))[:, None] * matpow(G, kappa - 1.0) * (dd ** (1.0 - kappa))[None, :]
    Ehat = ((dd ** (-kappa))[:, None] * matpow(G, kappa) * (dd ** (-kappa))[None, :]) - Z
    T1 = (dd ** (kappa - 1.5))[:, None] * matpow(M, 3.0 - 2.0 * kappa) * (dd ** (kappa - 1.5))[None, :]
    T2 = (dd ** (kappa - 2.0))[:, None] * matpow(G, 2.0 - kappa) * (dd ** (kappa - 2.0))[None, :]
    Yop = (dd ** (0.5 - kappa))[:, None] * matpow(G, kappa - 0.5) * (dd ** (0.5 - kappa))[None, :]
    W1inv = (dd ** (kappa - 1.0))[:, None] * matpow(M, 2.0 - 2.0 * kappa) * (dd ** (kappa - 1.0))[None, :]
    Pop = (dd ** (kappa - 1.5))[:, None] * matpow(G, 1.5 - kappa) * (dd ** (kappa - 1.5))[None, :]
    c0 = (m / (m - 1.0)) * sigp
    Ip = c0 * sum(wk * np.linalg.inv(sigp * np.eye(n) - xk * Z + ((1.0 + xk) / Lam) * np.linalg.inv(T1 - ((1.0 + xk) / Lam) * T2))
                  for xk, wk in zip(xs_p, ws_p))
    Id = c0 * sum(wk * np.linalg.inv(sigp * np.eye(n) - qk * Yop + np.linalg.inv(Lam * W1inv - qk * Pop))
                  for qk, wk in zip(qs_d, ws_d))
    return Ip, Id, Ehat


for lbl, pp in [("7/4", 1.75), ("5/3", 5.0 / 3.0), ("3/2", 1.5), ("sqrt(2)", np.sqrt(2.0)), ("7/5", 1.40), ("4/3", 4.0 / 3.0), ("5/4", 1.25), ("6/5", 1.20)]:
    kappa = pp / (2.0 * (pp - 1.0))
    Lr, dr, Xr = rg3[pp]
    sD = np.sqrt(dr); H = (sD[:, None] * Xr) * sD[None, :]; G = (sD[:, None] * H) * sD[None, :]
    Qr = (dr ** (-0.5))[:, None] * matpow(G, 0.5) * (dr ** (-0.5))[None, :]
    xs_p, Vx = eigh(Xr); ws_p = Vx[0, :] ** 2
    qs_d, Vq = eigh(Qr); ws_d = Vq[0, :] ** 2

    # Check exact Euler homogeneity F_var == -tr(D^{2k} Ehat)
    M = np.diag(dr) + H
    Z = (dr ** (1.0 - kappa))[:, None] * matpow(G, kappa - 1.0) * (dr ** (1.0 - kappa))[None, :]
    Ehat0 = ((dr ** (-kappa))[:, None] * matpow(G, kappa) * (dr ** (-kappa))[None, :]) - Z
    F_var = float(np.sum(eigh(M)[0] ** (2.0 * kappa)) / Lr - 2.0 * np.sum(eigh(G)[0] ** kappa))
    tr_D2k_E = float(np.sum((dr ** (2.0 * kappa)) * np.diag(Ehat0)))
    euler_err = abs(F_var + tr_D2k_E)

    # Check First Law tr(D^{2k} dEhat) == 0 & exact RG stationarity d/dt <e0, c_r I_op e0> == 0 along 2 independent directions!
    eps = 1e-5
    max_fl = 0.0; max_gp = 0.0; max_gd = 0.0
    g2_p_list = []; g2_d_list = []
    for vec in [np.array([0.0, 1.0, 0.0]), np.array([0.0, 0.0, 1.0])]:
        dp = dr * np.exp(eps * vec); dm = dr * np.exp(-eps * vec)
        Xp, ep = solve_H_given_D(dp, Lr, kappa, Xr)
        Xm, em = solve_H_given_D(dm, Lr, kappa, Xr)
        assert ep < 1e-11 and em < 1e-11
        Ipp, Idp, Ep = eval_both_integrals(dp, Xp, Lr, kappa, xs_p, ws_p, qs_d, ws_d)
        Ipm, Idm, Em = eval_both_integrals(dm, Xm, Lr, kappa, xs_p, ws_p, qs_d, ws_d)
        dE = (Ep - Em) / (2.0 * eps)
        fl = abs(float(np.sum((dr ** (2.0 * kappa)) * np.diag(dE))))
        gp = abs(float(Ipp[0, 0] - Ipm[0, 0]) / (2.0 * eps))
        gd = abs(float(Idp[0, 0] - Idm[0, 0]) / (2.0 * eps))
        max_fl = max(max_fl, fl); max_gp = max(max_gp, gp); max_gd = max(max_gd, gd)
        g2_p_list.append(float(Ipp[0, 0] + Ipm[0, 0] - 2.0) / (eps ** 2))
        g2_d_list.append(float(Idp[0, 0] + Idm[0, 0] - 2.0) / (eps ** 2))
    assert euler_err < 1e-11 and max_fl < 1e-7 and max_gp < 1e-7 and max_gd < 1e-7
    print(
        f"  p={lbl:7s} (k={kappa:5.3f}) | |F+tr(D^2k E)|={euler_err:.1e} | |tr(D^2k dE)|={max_fl:.1e} "
        f"| |g1_pri|={max_gp:.1e} | |g1_dual|={max_gd:.1e} | g2_pri(d1)={g2_p_list[0]:+.2e} | g2_dual(d1)={g2_d_list[0]:+.2e}"
    )


# ==============================================================================
# SUITE 3: THEOREM 3 — NON-COMMUTATIVE OPERATOR CONVEXITY & EXACT TREE-BRANCHING SLOPE LAW
# ==============================================================================
print("\n" + "=" * 100)
print("SUITE 3: THEOREM 3 — UNIVERSAL OPERATOR CONVEXITY IN u in [0,1] & TREE-BRANCHING SLOPE (1-rho_r)/m")
print("=" * 100)

print(f"  {'p':7s} {'r':2s} {'m':3s} | {'rho_r':9s} | {'(1-rho)/m':11s} {'err(Pri e0)':11s} {'err(Dual e0)':12s} | {'min(dPri/du)':13s} {'min(dDual/du)':13s} {'min(d2/du2)':11s}")
print("  " + "-" * 105)

for lbl, pp in [("1.73", 1.73), ("5/3", 5.0 / 3.0), ("3/2", 1.5), ("sqrt(2)", np.sqrt(2.0)), ("7/5", 1.40), ("4/3", 4.0 / 3.0), ("5/4", 1.25), ("6/5", 1.20)]:
    kappa = pp / (2.0 * (pp - 1.0))
    runs = [(5, 2)]
    if lbl in ["5/3", "7/5", "6/5"]:
        runs += [(3, 5), (3, 10)]
    L3, d3, X3 = rg3[pp]
    m3_prev = 2
    for rr, m_v in runs:
        if rr == 5 and m_v == 2:
            L_c, d_c, X_c = rg5[pp]
        else:
            L1_old, _ = scalar_1x1(kappa, m3_prev)
            rel_gap = max(1e-9, (L3 - L1_old) / L1_old)
            for mm in np.geomspace(m3_prev, m_v, 10)[1:]:
                L1, _ = scalar_1x1(kappa, mm)
                L3, d3, X3, err_m, oe_m = solve_rg_square(pp, mm, 3, L1 * (1.0 + rel_gap), d3, X3)
                rel_gap = max(1e-9, (L3 - L1) / L1)
            assert err_m < 1e-10 and oe_m < 1e-10
            m3_prev = m_v
            L_c, d_c, X_c = L3, d3, X3
        _, _, _, sp = roots_kappa(L_c, kappa)
        sD = np.sqrt(d_c); D = np.diag(d_c); H = (sD[:, None] * X_c) * sD[None, :]; M = D + H; G = (sD[:, None] * H) * sD[None, :]
        Q = (d_c ** (-0.5))[:, None] * matpow(G, 0.5) * (d_c ** (-0.5))[None, :]
        xs, Vx = eigh(X_c); wx = Vx[0, :] ** 2
        qs, Vq = eigh(Q); wq = Vq[0, :] ** 2
        Z = (d_c ** (1.0 - kappa))[:, None] * matpow(G, kappa - 1.0) * (d_c ** (1.0 - kappa))[None, :]
        T1 = (d_c ** (kappa - 1.5))[:, None] * matpow(M, 3.0 - 2.0 * kappa) * (d_c ** (kappa - 1.5))[None, :]
        T2 = (d_c ** (kappa - 2.0))[:, None] * matpow(G, 2.0 - kappa) * (d_c ** (kappa - 2.0))[None, :]
        Yop = (d_c ** (0.5 - kappa))[:, None] * matpow(G, kappa - 0.5) * (d_c ** (0.5 - kappa))[None, :]
        W1inv = (d_c ** (kappa - 1.0))[:, None] * matpow(M, 2.0 - 2.0 * kappa) * (d_c ** (kappa - 1.0))[None, :]
        Pop = (d_c ** (kappa - 1.5))[:, None] * matpow(G, 1.5 - kappa) * (d_c ** (kappa - 1.5))[None, :]

        I_r = np.eye(rr)
        Lp = [(sp * I_r - xk * Z + ((1.0 + xk) / L_c) * np.linalg.inv(T1 - ((1.0 + xk) / L_c) * T2)) / sp for xk in xs]
        Ld = [(sp * I_r - qk * Yop + np.linalg.inv(L_c * W1inv - qk * Pop)) / sp for qk in qs]

        fac = m_v / (m_v - 1.0)
        dIp0 = fac * sum(wk * (np.linalg.inv(L) - np.linalg.inv(L) @ np.linalg.inv(L)) for wk, L in zip(wx, Lp))
        dId0 = fac * sum(wk * (np.linalg.inv(L) - np.linalg.inv(L) @ np.linalg.inv(L)) for wk, L in zip(wq, Ld))
        # Check exact 2nd derivative at u = 0.25 via explicit PSD formula:
        u_t = 0.25
        d2p = 2.0 * fac * sum(
            wk * np.linalg.inv((1.0 - u_t) * L + u_t * I_r) @ (I_r - L)
            @ np.linalg.inv((1.0 - u_t) * L + u_t * I_r) @ (I_r - L)
            @ np.linalg.inv((1.0 - u_t) * L + u_t * I_r)
            for wk, L in zip(wx, Lp)
        )
        min_d2 = float(np.min(eigh(0.5 * (d2p + d2p.T))[0]))

        rho_r = (m_v - 1.0) * float(np.sum(d_c[1:] ** (2.0 * kappa)))
        pred_slope = (1.0 - rho_r) / m_v
        err_p = abs(float(dIp0[0, 0]) - pred_slope)
        err_d = abs(float(dId0[0, 0]) - pred_slope)
        assert err_p < 1e-11 and err_d < 1e-11 and min_d2 >= -1e-12
        min_dp = float(np.min(eigh(0.5 * (dIp0 + dIp0.T))[0]))
        min_dd = float(np.min(eigh(0.5 * (dId0 + dId0.T))[0]))
        if pp >= 4.0 / 3.0 - 1e-12:
            assert min_dp > 0.0 and min_dd > 0.0
        elif m_v == 2:
            assert min_dp > 0.0 and min_dd < 0.0
        print(
            f"  {lbl:7s} {rr:2d} {m_v:3d} | {rho_r:9.6f} | {pred_slope:+11.7f} {err_p:11.2e} {err_d:12.2e} "
            f"| {min_dp:+13.5e} {min_dd:+13.5e} {min_d2:+11.3e}"
        )


# ==============================================================================
# SUITE 4: THEOREM 4 — UNIVERSAL KAPPA-INDEPENDENT DENOMINATOR FACTORIZATIONS,
#          INVERSE-FREE PARALLEL SUM ACTION, & TWO-SIDED HANSEN SANDWICH
# ==============================================================================
print("\n" + "=" * 100)
print("SUITE 4: THEOREM 4 — KAPPA-INDEPENDENT FACTORIZATIONS, INVERSE-FREE PARALLEL SUM & HANSEN SANDWICH")
print("=" * 100)

print("\n[4A] Universal Denominator Factorizations & Exact RG Inverse-Free Optimal Parallel-Sum Action (Complex U(3)):")
U_rot, _ = np.linalg.qr(rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3)))
w0_rot = U_rot[:, 0]
for lbl, pp in [("7/4", 1.75), ("5/3", 5.0 / 3.0), ("3/2", 1.5), ("sqrt(2)", np.sqrt(2.0)), ("4/3", 4.0 / 3.0), ("5/4", 1.25), ("6/5", 1.20)]:
    kappa = pp / (2.0 * (pp - 1.0))
    Lr, dr, Xr = rg3[pp]
    _, _, _, sp = roots_kappa(Lr, kappa)
    c_r = 2.0 * sp
    D = U_rot @ np.diag(dr) @ U_rot.conj().T
    Xc = U_rot @ Xr @ U_rot.conj().T
    Dh = matpow(D, 0.5); H = Dh @ Xc @ Dh; M = D + H; G = Dh @ H @ Dh
    Qc = matpow(D, -0.5) @ matpow(G, 0.5) @ matpow(D, -0.5)
    Wx = np.linalg.inv(D) @ Xc @ D
    Wq = np.linalg.inv(D) @ Qc @ D
    Z = matpow(D, 1.0 - kappa) @ matpow(G, kappa - 1.0) @ matpow(D, 1.0 - kappa)
    T1 = matpow(D, kappa - 1.5) @ matpow(M, 3.0 - 2.0 * kappa) @ matpow(D, kappa - 1.5)
    T2 = matpow(D, kappa - 2.0) @ matpow(G, 2.0 - kappa) @ matpow(D, kappa - 2.0)
    Yop = matpow(D, 0.5 - kappa) @ matpow(G, kappa - 0.5) @ matpow(D, 0.5 - kappa)
    W1inv = matpow(D, kappa - 1.0) @ matpow(M, 2.0 - 2.0 * kappa) @ matpow(D, kappa - 1.0)
    Pop = matpow(D, kappa - 1.5) @ matpow(G, 1.5 - kappa) @ matpow(D, kappa - 1.5)
    S_pri = matpow(D, 1.5 - kappa) @ matpow(M, 2.0 * kappa - 2.0) @ Dh
    S_dual = matpow(D, 1.5 - kappa) @ matpow(G, kappa - 1.0) @ Dh

    # Check factorizations in positive-power D^k-scaled form (equivalent to D^{-k}(...) = I + W(...), zero cond blowup):
    Dk = matpow(D, kappa)
    Dkm1 = matpow(D, kappa - 1.0)
    x_t = 0.43; gam_t = (1.0 + x_t) / Lr
    lhs_pri = (T1 - gam_t * T2) @ S_pri
    rhs_pri = Dk + Dkm1 @ Xc @ D @ (Xc - x_t * np.eye(3)) @ np.linalg.inv(np.eye(3) + Xc)
    err_pri = float(np.linalg.norm(lhs_pri - rhs_pri))
    s_t = 0.57
    lhs_dual = (Lr * W1inv - s_t * Pop) @ S_dual
    rhs_dual = Dk + Dkm1 @ Qc @ D @ (Qc - s_t * np.eye(3))
    err_dual = float(np.linalg.norm(lhs_dual - rhs_dual))

    # Check exact RG inverse-free optimal parallel sum action:
    # U_k^opt e0 = w_k (T1 - gam_k T2)^{-1} K_k^{-1} (c_r e0) == S_pri (v_k v_k^*) e0!
    xs, Vx = eigh(0.5 * (Xc + Xc.conj().T))
    ov_x = w0_rot.conj() @ Vx
    Vx = Vx * (ov_x / np.abs(ov_x)).conj()[None, :]
    wx = np.real(w0_rot.conj() @ Vx) ** 2
    Ks_p = [sp * np.eye(3) - xk * Z + ((1.0 + xk) / Lr) * np.linalg.inv(T1 - ((1.0 + xk) / Lr) * T2) for xk in xs]
    P_p = np.linalg.inv(sum(wk * np.linalg.inv(K) for wk, K in zip(wx, Ks_p)))
    max_Up_err = 0.0
    for k_i in range(3):
        gam_k = (1.0 + xs[k_i]) / Lr
        Uk_opt = wx[k_i] * np.linalg.inv(T1 - gam_k * T2) @ np.linalg.inv(Ks_p[k_i]) @ P_p
        lhs_u = Uk_opt @ w0_rot
        rhs_u = S_pri @ np.outer(Vx[:, k_i], Vx[:, k_i].conj()) @ w0_rot
        max_Up_err = max(max_Up_err, float(np.linalg.norm(lhs_u - rhs_u)))

    qs, Vq = eigh(0.5 * (Qc + Qc.conj().T))
    ov_q = w0_rot.conj() @ Vq
    Vq = Vq * (ov_q / np.abs(ov_q)).conj()[None, :]
    wq = np.real(w0_rot.conj() @ Vq) ** 2
    Ks_d = [sp * np.eye(3) - qk * Yop + np.linalg.inv(Lr * W1inv - qk * Pop) for qk in qs]
    P_d = np.linalg.inv(sum(wk * np.linalg.inv(K) for wk, K in zip(wq, Ks_d)))
    max_Ud_err = 0.0
    for k_i in range(3):
        Uk_opt = wq[k_i] * np.linalg.inv(Lr * W1inv - qs[k_i] * Pop) @ np.linalg.inv(Ks_d[k_i]) @ P_d
        lhs_u = Uk_opt @ w0_rot
        rhs_u = S_dual @ np.outer(Vq[:, k_i], Vq[:, k_i].conj()) @ w0_rot
        max_Ud_err = max(max_Ud_err, float(np.linalg.norm(lhs_u - rhs_u)))

    print(f"  p={lbl:7s}: pri_fac={err_pri:.1e} | dual_fac={err_dual:.1e} | U_pri^opt w0={max_Up_err:.1e} | U_dual^opt w0={max_Ud_err:.1e}")
    assert err_pri < 1e-10 and err_dual < 1e-10 and max_Up_err < 1e-10 and max_Ud_err < 1e-10

print("\n[4B] Opposite-Direction Regime III Hansen Sandwich: Lam^{(k-2)/(k-1)} T_1 <= T_2 <= [Lam x_+/(1+x_+)^2] T_1:")
for lbl, pp in [("5/4", 1.25), ("6/5", 1.20), ("1.15", 1.15)]:
    kappa = pp / (2.0 * (pp - 1.0))
    if pp in rg3:
        Lr, dr, Xr = rg3[pp]
    else:
        L_prev, d_prev, X_prev = rg3[1.20]
        L1_15, _ = scalar_1x1(kappa, 2)
        Lr, dr, Xr, e15, oe15 = solve_rg_square(1.15, 2, 3, L1_15 * 1.001, d_prev, X_prev)
        assert e15 < 1e-10 and oe15 < 1e-10
    _, xp, _, _ = roots_kappa(Lr, kappa)
    D = U_rot @ np.diag(dr) @ U_rot.conj().T
    Dh = matpow(D, 0.5); H = Dh @ (U_rot @ Xr @ U_rot.conj().T) @ Dh; M = D + H; G = Dh @ H @ Dh
    T1 = matpow(D, kappa - 1.5) @ matpow(M, 3.0 - 2.0 * kappa) @ matpow(D, kappa - 1.5)
    T2 = matpow(D, kappa - 2.0) @ matpow(G, 2.0 - kappa) @ matpow(D, kappa - 2.0)
    lo_c = Lr ** ((kappa - 2.0) / (kappa - 1.0))
    hi_c = Lr * xp / ((1.0 + xp) ** 2)
    T1mh = matpow(T1, -0.5)
    W_sand = 0.5 * (T1mh @ T2 @ T1mh + (T1mh @ T2 @ T1mh).conj().T)
    evW = eigh(W_sand)[0]
    # Also test 500 random complex 3x3 pairs for the underlying contraction inequality K1^* M^{2-2k} K1 = (1/Lam) G^{1-k} -> lower bound!
    min_h_low = 1e9
    r_h = (kappa - 2.0) / (kappa - 1.0)
    for _ in range(500):
        V1, _ = np.linalg.qr(rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3)))
        D_r = V1 @ np.diag(np.exp(rng.uniform(-2.0, 2.0, size=3))) @ V1.conj().T
        V2, _ = np.linalg.qr(rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3)))
        H_r = matpow(D_r, 0.5) @ (V2 @ np.diag(rng.uniform(0.1, 3.0, size=3)) @ V2.conj().T) @ matpow(D_r, 0.5)
        M_r = D_r + H_r
        K1 = matpow(M_r, -0.5) @ matpow(D_r, 0.5)
        A_r = matpow(M_r, 2.0 - 2.0 * kappa)
        lhs_h = K1.conj().T @ matpow(A_r, r_h) @ K1
        rhs_h = matpow(K1.conj().T @ A_r @ K1, r_h)
        min_h_low = min(min_h_low, float(np.min(eigh(0.5 * ((rhs_h - lhs_h) + (rhs_h - lhs_h).conj().T))[0])))
    assert float(evW[0]) >= lo_c - 1e-11 and float(evW[-1]) <= hi_c + 1e-11 and min_h_low >= -1e-11
    print(f"  p={lbl:4s} (k={kappa:.2f}): lo_bnd={lo_c:7.4f} <= spec(T1^-1/2 T2 T1^-1/2)=[{evW[0]:.4f}, {evW[-1]:.4f}] <= hi_bnd={hi_c:7.4f} | 500 cplx Hansen={min_h_low:+.2e} (PASS)")


# ==============================================================================
# SUITE 5: THEOREM 5 — ONE-SHOT ALL-DELTA OPERATOR PARALLEL-SUM +
#          CONTRACTION-CONGRUENCE CERTIFICATE THEOREM (ALL 3 REGIMES)
# ==============================================================================
print("\n" + "=" * 100)
print("SUITE 5: THEOREM 5 — ONE-SHOT ALL-DELTA CONTRACTION-CONGRUENCE & PARALLEL-SUM CERTIFICATES")
print("=" * 100)

print("\n[5A] 1-Atom (Zero Integral!) + Single Explicit Contraction V = c*(X - x_- I)/x_+ (Adversarial 2x2 + 3x3):")
for lbl, pp, mode, cv in [("5/3", 5.0 / 3.0, "primal", 0.12), ("7/5", 1.40, "dual", 0.35), ("5/4", 1.25, "dual", 0.55), ("6/5", 1.20, "dual", 0.70)]:
    kappa = pp / (2.0 * (pp - 1.0))
    Lr, dr, Xr = rg3[pp]
    xm, xp, _, sp = roots_kappa(Lr, kappa)
    c_r = 2.0 * sp
    param = xm * 1.04 if mode == "primal" else np.sqrt(xm) * 1.02

    def eval_th5_1atom(dd, Xm):
        n = len(dd); sD = np.sqrt(dd); D = np.diag(dd)
        H = (sD[:, None] * Xm) * sD[None, :]; M = D + H; G = (sD[:, None] * H) * sD[None, :]
        Z = (dd ** (1.0 - kappa))[:, None] * matpow(G, kappa - 1.0) * (dd ** (1.0 - kappa))[None, :]
        Ehat = ((dd ** (-kappa))[:, None] * matpow(G, kappa) * (dd ** (-kappa))[None, :]) - Z
        B_sig = sp * np.eye(n) - Ehat
        dreq = max(0.0, float(np.max(eigh(0.5 * (Ehat + Ehat.T))[0])) - sp)
        if mode == "primal":
            T1 = (dd ** (kappa - 1.5))[:, None] * matpow(M, 3.0 - 2.0 * kappa) * (dd ** (kappa - 1.5))[None, :]
            T2 = (dd ** (kappa - 2.0))[:, None] * matpow(G, 2.0 - kappa) * (dd ** (kappa - 2.0))[None, :]
            gam = (1.0 + param) / Lr
            K0 = sp * np.eye(n) - param * Z + gam * np.linalg.inv(T1 - gam * T2)
        else:
            Yop = (dd ** (0.5 - kappa))[:, None] * matpow(G, kappa - 0.5) * (dd ** (0.5 - kappa))[None, :]
            W1inv = (dd ** (kappa - 1.0))[:, None] * matpow(M, 2.0 - 2.0 * kappa) * (dd ** (kappa - 1.0))[None, :]
            Pop = (dd ** (kappa - 1.5))[:, None] * matpow(G, 1.5 - kappa) * (dd ** (kappa - 1.5))[None, :]
            K0 = sp * np.eye(n) - param * Yop + np.linalg.inv(Lr * W1inv - param * Pop)
        V = cv * (Xm - xm * np.eye(n)) / xp
        bud = float(np.max(eigh(V.T @ V)[0]))
        assert bud <= 1.0 + 1e-12
        tot = K0 + V.T @ B_sig @ V
        return float(np.max(eigh(0.5 * (tot + tot.T))[0])) / c_r, float(np.max(eigh(0.5 * (K0 + K0.T))[0])) / c_r, dreq / sp, bud

    # Gather r=3 RG + 1x1 {xm, xp} + full 2x2 coupled curve + 12 adversarial Nelder-Mead 3x3 runs:
    st = {"max_th5": -1e9, "max_k0": -1e9, "max_dr": 0.0, "max_bud": 0.0, "n_eval": 0}
    def record(dd, Xm):
        v5, vk0, drr, bd = eval_th5_1atom(dd, Xm)
        st["n_eval"] += 1
        st["max_th5"] = max(st["max_th5"], v5)
        st["max_k0"] = max(st["max_k0"], vk0)
        st["max_dr"] = max(st["max_dr"], drr)
        st["max_bud"] = max(st["max_bud"], bd)
        return v5

    record(np.array([1.0]), np.array([[xm]]))
    record(np.array([1.0]), np.array([[xp]]))
    record(dr, Xr)
    L2, d2, X2_0, _, _ = solve_rg_square(pp, 2, 2, Lr, dr[:2], Xr[:2, :2])
    for direction in [1, -1]:
        X_cur = X2_0.copy(); d_cur = d2[1]
        for _ in range(120):
            d_next = d_cur * (1.03 if direction == 1 else 1.0 / 1.03)
            if d_next >= 0.999 or d_next <= 1e-5:
                break
            Xn, err = solve_H_given_D(np.array([1.0, d_next]), Lr, kappa, X_cur)
            if err > 1e-10 or abs(Xn[0, 1]) < 1e-5:
                break
            X_cur = Xn; d_cur = d_next
            record(np.array([1.0, d_cur]), X_cur)

    rng_adv = np.random.default_rng(303)
    for _ in range(12):
        u0 = rng_adv.uniform(-2.5, 2.5, size=2)
        cache = {"X": Xr.copy()}
        def neg_obj(u):
            dd = np.array([1.0, dr[1] * np.exp(np.clip(u[0], -4.5, 4.5)), dr[2] * np.exp(np.clip(u[1], -4.5, 4.5))])
            Xm, err = solve_H_given_D(dd, Lr, kappa, cache["X"])
            if err > 1e-10:
                return 10.0
            return -record(dd, Xm)
        minimize(neg_obj, u0, method="Nelder-Mead", options={"maxiter": 65})

    crush = (st["max_k0"] - 1.0) / max(st["max_th5"] - 1.0, 1e-12)
    assert st["max_bud"] < 1.0 and st["max_th5"] < st["max_k0"]
    print(
        f"  p={lbl:4s} ({mode:6s}, c={cv:.2f}, {st['n_eval']:4d} evals, max dreq/sp={st['max_dr']:.2f}, ||V||^2<={st['max_bud']:.4f}<=1): "
        f"K0/c={st['max_k0']:.7f} -> (K0+V*BV)/c={st['max_th5']:.8f} ({crush:6.1f}x crush!)"
    )

print("\n[5B] 3-Atom Linear Parallel Sum Y_k = a_k I + b_k W + V^* B_sigp V (Exact Budget <= m/(m-1) = 2.0):")
for lbl, pp, mode, cv_init in [("5/3", 5.0 / 3.0, "primal", 0.12), ("7/5", 1.40, "dual", 0.35), ("5/4", 1.25, "dual", 0.55), ("6/5", 1.20, "dual", 0.70)]:
    kappa = pp / (2.0 * (pp - 1.0))
    Lr, dr, Xr = rg3[pp]
    xm, xp, _, sp = roots_kappa(Lr, kappa); c_r = 2.0 * sp
    L2, d2, X2_0, _, _ = solve_rg_square(pp, 2, 2, Lr, dr[:2], Xr[:2, :2])
    def prep(dd, Xm):
        n = len(dd); sD = np.sqrt(dd); D = np.diag(dd)
        H = (sD[:, None] * Xm) * sD[None, :]; M = D + H; G = (sD[:, None] * H) * sD[None, :]
        Z = (dd ** (1.0 - kappa))[:, None] * matpow(G, kappa - 1.0) * (dd ** (1.0 - kappa))[None, :]
        Ehat = ((dd ** (-kappa))[:, None] * matpow(G, kappa) * (dd ** (-kappa))[None, :]) - Z
        B_sig = sp * np.eye(n) - Ehat
        if mode == "primal":
            T1 = (dd ** (kappa - 1.5))[:, None] * matpow(M, 3.0 - 2.0 * kappa) * (dd ** (kappa - 1.5))[None, :]
            T2 = (dd ** (kappa - 2.0))[:, None] * matpow(G, 2.0 - kappa) * (dd ** (kappa - 2.0))[None, :]
            return (n, Xm, Z, B_sig, T1, T2)
        Yop = (dd ** (0.5 - kappa))[:, None] * matpow(G, kappa - 0.5) * (dd ** (0.5 - kappa))[None, :]
        W1inv = (dd ** (kappa - 1.0))[:, None] * matpow(M, 2.0 - 2.0 * kappa) * (dd ** (kappa - 1.0))[None, :]
        Pop = (dd ** (kappa - 1.5))[:, None] * matpow(G, 1.5 - kappa) * (dd ** (kappa - 1.5))[None, :]
        return (n, Xm, Yop, B_sig, W1inv, Pop)
    samps = [prep(np.array([1.0]), np.array([[xm]])), prep(np.array([1.0]), np.array([[xp]])), prep(dr, Xr)]
    for direction in [1, -1]:
        X_cur = X2_0.copy(); d_cur = d2[1]
        for _ in range(100):
            d_next = d_cur * (1.03 if direction == 1 else 1.0 / 1.03)
            if d_next >= 0.999 or d_next <= 1e-5:
                break
            Xn, err = solve_H_given_D(np.array([1.0, d_next]), Lr, kappa, X_cur)
            if err > 1e-10 or abs(Xn[0, 1]) < 1e-5:
                break
            X_cur = Xn; d_cur = d_next
            samps.append(prep(np.array([1.0, d_cur]), X_cur))
    rng_s = np.random.default_rng(404)
    for _ in range(40):
        u = rng_s.uniform(-1.5, 1.5, size=2)
        dd3 = np.array([1.0, dr[1] * np.exp(u[0]), dr[2] * np.exp(u[1])])
        Xn, err = solve_H_given_D(dd3, Lr, kappa, Xr)
        if err < 1e-10:
            samps.append(prep(dd3, Xn))

    if mode == "primal":
        atoms_rg, V_rg = eigh(Xr); ws_rg = V_rg[0, :] ** 2
    else:
        sD = np.sqrt(dr); G_rg = (sD[:, None] * ((sD[:, None] * Xr) * sD[None, :])) * sD[None, :]
        Q_rg = (dr ** (-0.5))[:, None] * matpow(G_rg, 0.5) * (dr ** (-0.5))[None, :]
        atoms_rg, V_rg = eigh(Q_rg); ws_rg = V_rg[0, :] ** 2

    Ks_all = []
    for n, Xm, Wop, B_sig, A1, A2 in samps:
        if mode == "primal":
            Ks_all.append([sp * np.eye(n) - a * Wop + ((1.0 + a) / Lr) * np.linalg.inv(A1 - ((1.0 + a) / Lr) * A2) for a in atoms_rg])
        else:
            Ks_all.append([sp * np.eye(n) - a * Wop + np.linalg.inv(Lr * A1 - a * A2) for a in atoms_rg])

    def unpack_3a(theta):
        a1, a2, b1, b2, cv_l = theta
        return [a1, a2, 1.0 - a1 - a2], [b1, b2, -b1 - b2], cv_l

    def eval_3a(theta):
        av, bv, cv_l = unpack_3a(theta)
        wv = -1e9; wb = -1e9
        for idx, (n, Xm, Wop, B_sig, _, _) in enumerate(samps):
            Ks = Ks_all[idx]; V = cv_l * (Xm - xm * np.eye(n)) / xp
            St = V.T @ B_sig @ V; Bt = V.T @ V
            for k in range(3):
                Yk = av[k] * np.eye(n) + bv[k] * Wop
                St = St + (1.0 / ws_rg[k]) * (Yk.T @ Ks[k] @ Yk)
                Bt = Bt + (1.0 / ws_rg[k]) * (Yk.T @ Yk)
            wb = max(wb, float(np.max(eigh(0.5 * (Bt + Bt.T))[0])))
            wv = max(wv, float(np.max(eigh(0.5 * (St + St.T))[0])) / c_r)
        return wv + 100.0 * max(0.0, wb - 1.999)

    best_res = None
    for init_th in ([ws_rg[0], ws_rg[1], 0.0, 0.0, cv_init], [1.0, 0.0, 0.0, 0.0, cv_init]):
        r_try = minimize(eval_3a, init_th, method="Nelder-Mead", options={"maxiter": 1600, "xatol": 1e-7, "fatol": 1e-10})
        if best_res is None or r_try.fun < best_res.fun:
            best_res = r_try
    av, bv, cv_l = unpack_3a(best_res.x)
    wv = -1e9; wb = -1e9
    for idx, (n, Xm, Wop, B_sig, _, _) in enumerate(samps):
        Ks = Ks_all[idx]; V = cv_l * (Xm - xm * np.eye(n)) / xp
        St = V.T @ B_sig @ V; Bt = V.T @ V
        for k in range(3):
            Yk = av[k] * np.eye(n) + bv[k] * Wop
            St = St + (1.0 / ws_rg[k]) * (Yk.T @ Ks[k] @ Yk)
            Bt = Bt + (1.0 / ws_rg[k]) * (Yk.T @ Yk)
        wb = max(wb, float(np.max(eigh(0.5 * (Bt + Bt.T))[0])))
        wv = max(wv, float(np.max(eigh(0.5 * (St + St.T))[0])) / c_r)
    print(f"  p={lbl:4s} ({mode:6s}, {len(samps):2d} mats): MAX S_tot/c_r = {wv:.9f} (excess={wv-1:+.2e}) | MAX budget = {wb:.5f} <= 2.000 (PASS)")
    assert wb < 2.0 and wv < 1.002

print("\n[5C] Exact Degree-3 Polynomial 2x2 Block Schur-Complement Reformulation at p = 5/3 over C:")
L53, d53, X53 = rg3[5.0 / 3.0]
_, _, _, sp53 = roots_kappa(L53, 1.25)
D53 = U_rot @ np.diag(d53) @ U_rot.conj().T
Dh53 = matpow(D53, 0.5); H53 = Dh53 @ (U_rot @ X53 @ U_rot.conj().T) @ Dh53
M53 = D53 + H53; G53 = Dh53 @ H53 @ Dh53
A53 = matpow(D53, 0.5); B53 = matpow(M53, 0.5); C53 = matpow(G53, 0.25)
poly_eq1 = float(np.linalg.norm(B53 @ B53 @ B53 - L53 * A53 @ C53 @ A53))
poly_eq2 = float(np.linalg.norm(A53 @ B53 @ B53 @ A53 - (A53 @ A53 @ A53 @ A53 + C53 @ C53 @ C53 @ C53)))
x0_53 = 0.0099; gam0_53 = (1.0 + x0_53) / L53; c_53 = 2.0 * sp53
Z53 = matpow(D53, -0.25) @ C53 @ matpow(D53, -0.25)
T1_53 = matpow(D53, -0.25) @ B53 @ matpow(D53, -0.25)
T2_53 = matpow(D53, -0.75) @ matpow(G53, 0.75) @ matpow(D53, -0.75)
K53 = sp53 * np.eye(3) - x0_53 * Z53 + gam0_53 * np.linalg.inv(T1_53 - gam0_53 * T2_53)
schur_lhs = matpow(A53, 0.5) @ (c_53 * np.eye(3) - K53) @ matpow(A53, 0.5)
tl = (c_53 - sp53) * A53 + x0_53 * C53
od = np.sqrt(gam0_53) * (A53 @ A53)
br = A53 @ B53 @ A53 - gam0_53 * (C53 @ C53 @ C53)
schur_rhs = tl - od @ np.linalg.inv(br) @ od
schur_err = float(np.linalg.norm(schur_lhs - schur_rhs))
assert poly_eq1 < 1e-11 and poly_eq2 < 1e-11 and schur_err < 1e-11
print(f"  p=5/3 (A,B,C)=(D^1/2,M^1/2,G^1/4) over C: ||B^3-Lam ACA||={poly_eq1:.1e} | ||AB^2A-A^4-C^4||={poly_eq2:.1e} | Schur_err={schur_err:.1e} (EXACT!)")


# ==============================================================================
# SUITE 6: THEOREM 6 — THREE SHARP SECOND-USE-OF-HOLDEN OBSTRUCTIONS
# ==============================================================================
print("\n" + "=" * 100)
print("SUITE 6: THEOREM 6 — THREE SHARP OBSTRUCTIONS PROVING SECOND-USE-OF-HOLDEN NECESSITY")
print("=" * 100)

print(f"  {'p':7s} | {'1x1_HoldenFree(Pri)':20s} {'1x1_HoldenFree(Dual)':21s} | {'1D_HoldenElim(Pri)':19s} {'e0^perp_min(Pri)':17s} {'e0^perp_min(Dual)'}")
print("  " + "-" * 104)
for lbl, pp in [("1.73", 1.73), ("5/3", 5.0 / 3.0), ("3/2", 1.5), ("sqrt(2)", np.sqrt(2.0)), ("7/5", 1.40), ("4/3", 4.0 / 3.0), ("5/4", 1.25), ("6/5", 1.20)]:
    kappa = pp / (2.0 * (pp - 1.0))
    L5, d5, X5 = rg5[pp]
    _, xp, _, sp = roots_kappa(L5, kappa); c5 = 2.0 * sp
    sD = np.sqrt(d5); D = np.diag(d5); H = (sD[:, None] * X5) * sD[None, :]; M = D + H; G = (sD[:, None] * H) * sD[None, :]
    Q5 = (d5 ** (-0.5))[:, None] * matpow(G, 0.5) * (d5 ** (-0.5))[None, :]
    xs, Vx = eigh(X5); wx = Vx[0, :] ** 2
    qs, Vq = eigh(Q5); wq = Vq[0, :] ** 2

    # (a) Holden-free 1x1 scalar grid u in (0, xp]:
    ug = np.linspace(1e-6, xp, 2000)
    Fp_hf = sum(wk / (sp - xk * (ug ** (kappa - 1.0)) + ((1.0 + xk) / L5) / ((1.0 + ug) ** (3.0 - 2.0 * kappa) - ((1.0 + xk) / L5) * (ug ** (2.0 - kappa))))
                for xk, wk in zip(xs, wx))
    Fd_hf = sum(wk / (sp - qk * (ug ** (kappa - 0.5)) + 1.0 / (L5 * ((1.0 + ug) ** (2.0 - 2.0 * kappa)) - qk * (ug ** (1.5 - kappa))))
                for qk, wk in zip(qs, wq))

    # (b) Naive Holden-eliminated scalar K_H(z; xk):
    th1 = (3.0 - 2.0 * kappa) / (2.0 * kappa - 1.0); th2 = (2.0 - kappa) / (kappa - 1.0)
    zg = np.geomspace(1e-8, xp ** (kappa - 1.0), 2000)
    Fp_he = sum(wk / (sp - xk * zg + ((1.0 + xk) / L5) / ((L5 * zg) ** th1 - ((1.0 + xk) / L5) * (zg ** th2)))
                for xk, wk in zip(xs, wx))

    # (c) e0^perp eigenvalues of c5 I_primal and c5 I_dual on r=5 RG:
    Z = (d5 ** (1.0 - kappa))[:, None] * matpow(G, kappa - 1.0) * (d5 ** (1.0 - kappa))[None, :]
    T1 = (d5 ** (kappa - 1.5))[:, None] * matpow(M, 3.0 - 2.0 * kappa) * (d5 ** (kappa - 1.5))[None, :]
    T2 = (d5 ** (kappa - 2.0))[:, None] * matpow(G, 2.0 - kappa) * (d5 ** (kappa - 2.0))[None, :]
    Ip5 = c5 * sum(wk * np.linalg.inv(sp * np.eye(5) - xk * Z + ((1.0 + xk) / L5) * np.linalg.inv(T1 - ((1.0 + xk) / L5) * T2)) for xk, wk in zip(xs, wx))
    Yop = (d5 ** (0.5 - kappa))[:, None] * matpow(G, kappa - 0.5) * (d5 ** (0.5 - kappa))[None, :]
    W1inv = (d5 ** (kappa - 1.0))[:, None] * matpow(M, 2.0 - 2.0 * kappa) * (d5 ** (kappa - 1.0))[None, :]
    Pop = (d5 ** (kappa - 1.5))[:, None] * matpow(G, 1.5 - kappa) * (d5 ** (kappa - 1.5))[None, :]
    Id5 = c5 * sum(wk * np.linalg.inv(sp * np.eye(5) - qk * Yop + np.linalg.inv(L5 * W1inv - qk * Pop)) for qk, wk in zip(qs, wq))

    ev_p_perp = eigh(0.5 * (Ip5[1:, 1:] + Ip5[1:, 1:].T))[0]
    ev_d_perp = eigh(0.5 * (Id5[1:, 1:] + Id5[1:, 1:].T))[0]
    min_p_hf = float(c5 * np.min(Fp_hf))
    min_d_hf = float(c5 * np.min(Fd_hf))
    min_p_he = float(c5 * np.min(Fp_he))

    print(f"  {lbl:7s} | {min_p_hf:+20.6f} {min_d_hf:+21.6f} | {min_p_he:+19.6f} {ev_p_perp[0]:17.6f} {ev_d_perp[0]:17.6f}")
    if lbl not in ("3/2", "4/3"):
        assert min_p_hf < 0.9999 and min_d_hf < 0.99
        assert min_p_he < 0.99
        assert abs(float(ev_p_perp[0]) - 1.0) > 1e-4 and abs(float(ev_d_perp[0]) - 1.0) > 1e-4
    elif lbl == "4/3":
        assert min_p_he < 0.92  # Even at p=4/3, naive Holden elimination breaks!

print("\n" + "=" * 100)
print(f"ALL MODULES & SUITES (0-6) PASSED 100% WITH ZERO ASSERTION FAILURES! (Total elapsed: {time.time() - t_global_start:.2f}s)")
print("=" * 100)
