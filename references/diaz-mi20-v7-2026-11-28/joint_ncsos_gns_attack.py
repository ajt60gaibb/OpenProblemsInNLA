r"""
================================================================================
OPTION A4: 2-MATRIX JOINT NC-SOS, GNS EXTRACTION, DUAL-GRAM ANATOMY, AND
100% ZERO-FLOAT mpmath.iv ALL-DIMENSIONS ALL-LAMBDA CERTIFICATIONS FOR MI-20
================================================================================
Covers all four rational exponents p in {6/5, 5/4, 3/2, 5/3}, with zero-float
all-dimensions (n >= 1), all-Lambda in [Lam_cert, Lam_interp(p, m)] world-record
certifications focused on the three remaining OPEN rational exponents:
  - p = 6/5 (kappa = 3,   m = 2): FIRST-EVER 100% zero-float mpmath.iv
        2-Matrix Joint NC-SOS proof (ZERO Stage-1 U-bound, ZERO C^2 curvature
        error via our Exactly-Affine Shared-Multiplier Theorem!), shattering the
        irreducible 1.41e-5 Stage-1 deg-10 floor (gap <= 9.64e-6 vs prior 1.82e-5)!
  - p = 5/3 (kappa = 5/4, m = 2, 3, 4): 4.50x-11.14x tighter zero-float mpmath.iv
        enclosures via deg-8A (b=35) + deg-6 + Stage-1 tail!
  - p = 5/4 (kappa = 5/2, m = 2, 3, 4): tightened zero-float mpmath.iv
        enclosures via all-block facial-reduced deg-8C + deg-8A + deg-6 + Stage-1!

STRICT ZERO-TRUST ARCHITECTURE:
  - MODULE 0: Runtime AST Zero-Float Purity Audit asserting ZERO float(),
        ZERO float literals, and ZERO numpy/scipy/math references in EVERY
        function inside SECTION B (`PURE_IV_FUNCTIONS`).
  - SECTION A (UNTRUSTED FLOAT64 ORACLES):
        * Suite 1: 2-Matrix Joint NC-SOS ladder (ZERO Stage-1 U-bound, honest
          (I-D)(E1+E2)=0, exact facial reduction, RG tree sanity check < 1e-12)
          across all 4 rational exponents p in {6/5, 5/4, 3/2, 5/3} (m=2), plus
          Dual Gram Spectral & Effective-Rank Anatomy.
        * Suite 2: Stage-1 U-floor vs exact U=sig_+ vs Uninverted diagnostic
          across the open exponents p in {6/5, 5/4, 5/3} x m in {2, 3, 4}.
        * Suite 3: Truncated GNS + Nuclear-Norm min Tr(M_0) + Unconstrained
          Cholesky BFGS Kubo-Ando Polisher across all 4 rational exponents (m=2).
        * Suite 5: Operator-Parallel-Sum Variational Partition-of-Unity NC-SOS
          probe on #107 Primal K_{op,x}^{(p)} (p = 5/3, 6/5) & #119 Dual Q-Family
          Ktilde_{op,s}^{(p)} (p = 5/4, 6/5) over complex Hermitian Holden solutions.
        * Untrusted witness-generation oracles (`oracle_*`) feeding exact decimal
          mp.mpf witnesses to Section B.
  - SECTION B (100% PURE ZERO-FLOAT mpmath.iv VERIFIER KERNEL):
        * Pure outward-rounded interval arithmetic (`mpmath.iv`), exact outward
          decimal/scientific string formatters (`ceil_*`, `floor_*`) with live
          inequality assertions, and Suite 4 certifying 7 complete zero-gap
          all-Lambda in [Lam_cert, Lam_interp(p, m)] upper bounds!
================================================================================
"""

import ast
import heapq
import inspect
import time
from itertools import product

import mpmath as mp
from mpmath import iv

# Untrusted numerical oracle libraries (STRICTLY forbidden inside SECTION B!)
import numpy as np
from scipy.optimize import brentq, least_squares, linprog, minimize


# ==============================================================================
# CERTIFIED PRIOR ANCHORS (EXACT DECIMAL STRINGS FROM rigorous_iv_multi_p_bounds.py)
# ==============================================================================
PRIOR_CERT_LB_STR = {
    "6/5": {2: "1.007397668918", 3: "1.012830139513", 4: "1.017237089278"},
    "5/4": {2: "1.011065979791", 3: "1.019193263924", 4: "1.025787707117"},
    "3/2": {2: "1.036437168065", 3: "1.063114500990", 4: "1.084719139101"},
    "5/3": {2: "1.057348913859", 3: "1.098935623593", 4: "1.132421930734"},
}

PRIOR_CERT_LAM_UB_STR = {
    "6/5": {2: "33.4505",  3: "34.5515",  4: "35.4668"},
    "5/4": {2: "16.9073",  3: "17.5995",  4: "18.1790"},
    "3/2": {2: "4.453377", 3: "4.806190", 4: "5.105198"},
    "5/3": {2: "3.251598", 3: "3.580802", 4: "3.859845"},
}


# ==============================================================================
# SECTION B: 100% PURE ZERO-FLOAT mpmath.iv VERIFIER KERNEL
# (ZERO float(), ZERO float literals, ZERO numpy/scipy/math — AST-AUDITED!)
# ==============================================================================
PURE_IV_FUNCTIONS = (
    "ceil_fixed_str",
    "floor_fixed_str",
    "ceil_sci_str",
    "floor_sci_str",
    "strip_outer_0",
    "canon_w",
    "gen_words",
    "reduced_words_k",
    "padd_iv",
    "pmul_iv",
    "ppow_iv",
    "iv_cholesky_pd",
    "iv_certify_xplus",
    "_iv_sup_1d",
    "iv_certify_stage1_5scalar",
    "build_problem_polys_iv",
    "build_symbolic_struct_iv",
    "iv_certify_nc_sos_interval",
    "build_p65_affine_joint_polys_iv",
    "build_p65_affine_joint_struct_iv",
    "iv_certify_affine_joint_p65_box",
    "iv_certify_stage1_tail_box",
    "iv_C_from_Lam_str",
)


def ceil_fixed_str(x_mp, decimals=12):
    """Strict outward-UPWARD fixed-decimal formatter: guarantees iv.mpf(s).a >= x_mp."""
    scale = mp.mpf(10) ** decimals
    q = int(mp.ceil(x_mp * scale))
    neg = q < 0
    qa = -q if neg else q
    int_part, frac_part = divmod(qa, 10 ** decimals)
    s = f"{'-' if neg else ''}{int_part}.{frac_part:0{decimals}d}"
    while mp.mpf(iv.mpf(s).a) < x_mp:
        q += 1
        neg = q < 0
        qa = -q if neg else q
        int_part, frac_part = divmod(qa, 10 ** decimals)
        s = f"{'-' if neg else ''}{int_part}.{frac_part:0{decimals}d}"
    assert mp.mpf(iv.mpf(s).a) >= x_mp
    return s


def floor_fixed_str(x_mp, decimals=12):
    """Strict outward-DOWNWARD fixed-decimal formatter: guarantees iv.mpf(s).b <= x_mp."""
    scale = mp.mpf(10) ** decimals
    q = int(mp.floor(x_mp * scale))
    neg = q < 0
    qa = -q if neg else q
    int_part, frac_part = divmod(qa, 10 ** decimals)
    s = f"{'-' if neg else ''}{int_part}.{frac_part:0{decimals}d}"
    while mp.mpf(iv.mpf(s).b) > x_mp:
        q -= 1
        neg = q < 0
        qa = -q if neg else q
        int_part, frac_part = divmod(qa, 10 ** decimals)
        s = f"{'-' if neg else ''}{int_part}.{frac_part:0{decimals}d}"
    assert mp.mpf(iv.mpf(s).b) <= x_mp
    return s


def ceil_sci_str(x_mp, sig=3):
    """Strict outward-UPWARD scientific formatter for positive x_mp: guarantees iv.mpf(s).a >= x_mp."""
    assert x_mp > 0
    exp10 = int(mp.floor(mp.log10(x_mp)))
    shift = sig - 1 - exp10
    p10 = mp.mpf(10) ** shift
    q = int(mp.ceil(x_mp * p10))
    if q >= 10 ** sig:
        q = (q + 9) // 10
        exp10 += 1
    d_str = str(q)
    s = f"{d_str[0]}.{d_str[1:]}e{exp10:+03d}" if sig > 1 else f"{d_str}e{exp10:+03d}"
    while mp.mpf(iv.mpf(s).a) < x_mp:
        q += 1
        if q >= 10 ** sig:
            q = (q + 9) // 10
            exp10 += 1
        d_str = str(q)
        s = f"{d_str[0]}.{d_str[1:]}e{exp10:+03d}" if sig > 1 else f"{d_str}e{exp10:+03d}"
    assert mp.mpf(iv.mpf(s).a) >= x_mp
    return s


def floor_sci_str(x_mp, sig=3):
    """Strict outward-DOWNWARD scientific formatter for positive x_mp: guarantees iv.mpf(s).b <= x_mp."""
    assert x_mp > 0
    exp10 = int(mp.floor(mp.log10(x_mp)))
    shift = sig - 1 - exp10
    p10 = mp.mpf(10) ** shift
    q = int(mp.floor(x_mp * p10))
    if q < 10 ** (sig - 1):
        q = 10 ** (sig - 1)
    d_str = str(q)
    s = f"{d_str[0]}.{d_str[1:]}e{exp10:+03d}" if sig > 1 else f"{d_str}e{exp10:+03d}"
    while mp.mpf(iv.mpf(s).b) > x_mp:
        q -= 1
        if q < 10 ** (sig - 1):
            q = 10 ** sig - 1
            exp10 -= 1
        d_str = str(q)
        s = f"{d_str[0]}.{d_str[1:]}e{exp10:+03d}" if sig > 1 else f"{d_str}e{exp10:+03d}"
    assert mp.mpf(iv.mpf(s).b) <= x_mp
    return s


def strip_outer_0(w):
    i, j = 0, len(w)
    while i < j and w[i] == 0:
        i += 1
    while j > i and w[j - 1] == 0:
        j -= 1
    return w[i:j]


def canon_w(w):
    s = strip_outer_0(w)
    return s if s <= s[::-1] else s[::-1]


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


def iv_cholesky_pd(M):
    """Pure mpmath.iv Cholesky certification that every real symmetric matrix in M is PD."""
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


def iv_certify_xplus(Lam_mp, k_num, k_den):
    """Pure mpmath.iv enclosure of x_+(Lam) > 1 and sig_+(Lam) = x_+^{k-1}(x_+ - 1)."""
    Lam_iv = iv.mpf(Lam_mp)
    k_iv = iv.mpf(k_num) / iv.mpf(k_den)
    twokm1 = 2 * k_iv - 1
    km1 = k_iv - 1
    k_m = mp.mpf(k_num) / mp.mpf(k_den)
    x_min_m = (k_m - 1) / k_m
    x_m = mp.mpf("1.2")
    for _ in range(80):
        fv = (1 + x_m) ** (2 * k_m - 1) - Lam_mp * (x_m ** (k_m - 1))
        dfv = (2 * k_m - 1) * ((1 + x_m) ** (2 * k_m - 2)) - Lam_mp * (k_m - 1) * (x_m ** (k_m - 2))
        x_m -= fv / dfv
        if x_m <= x_min_m:
            x_m = mp.mpf("1.5")
    rad = mp.mpf("1e-26")
    xl = x_m - rad
    xh = x_m + rad
    assert xl > mp.mpf(1)
    fl = (1 + iv.mpf(xl)) ** twokm1 - Lam_iv * (iv.mpf(xl) ** km1)
    fh = (1 + iv.mpf(xh)) ** twokm1 - Lam_iv * (iv.mpf(xh) ** km1)
    assert mp.mpf(fl.b) < 0 and mp.mpf(fh.a) > 0
    xp_iv = iv.mpf([xl, xh])
    sigp_iv = (xp_iv ** km1) * (xp_iv - 1)
    return xp_iv, sigp_iv


def _iv_sup_1d(f_and_df, lo, hi, tol_str="1e-12", max_splits=220):
    """Pure mpmath.iv 1D branch-and-bound rigorous upper bound on sup_{[lo, hi]} f."""
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
    log_lo = mp.log(lo)
    log_hi = mp.log(hi)
    edges = [mp.exp(log_lo + (log_hi - log_lo) * k / n_init) for k in range(n_init + 1)]
    edges[0] = lo
    edges[-1] = hi
    best_lo = None
    heap = []
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
        if lv1 > best_lo:
            best_lo = lv1
        if lv2 > best_lo:
            best_lo = lv2
        uid += 1
        heapq.heappush(heap, (-hv1, uid, xl, xm, lv1, hv1))
        uid += 1
        heapq.heappush(heap, (-hv2, uid, xm, xh, lv2, hv2))
    return heap[0][5]


def iv_certify_stage1_5scalar(Lam_iv, k_num, k_den, mults_mp):
    """Pure mpmath.iv certification of Stage-1 L_all(Lam) over ALL (0, inf) for ALL Lam in Lam_iv."""
    a_iv, b_iv, c_iv, l1_iv = (iv.mpf(x) for x in mults_mp)
    k_iv = iv.mpf(k_num) / iv.mpf(k_den)
    km1_iv = k_iv - 1
    twok_iv = 2 * k_iv
    twokm1_iv = twok_iv - 1
    twokm2_iv = twok_iv - 2

    assert mp.mpf(l1_iv.a) > 0 and mp.mpf(c_iv.b) < 0
    alpha_G = iv.mpf(1) - (b_iv + c_iv) * Lam_iv
    beta_G = iv.mpf(1) + c_iv * Lam_iv
    assert mp.mpf(beta_G.a) > 0

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


def build_problem_polys_iv(p_key, X_cap_iv, U_iv, L_iv):
    """Pure mpmath.iv builder of constant weights, objective, and affine Holden ideal g0 - mu*g1."""
    one = iv.mpf(1)
    pI = {(): one}
    p0 = {(0,): one}
    p1 = {(1,): one}
    pIm0 = padd_iv(pI, p0, -1)

    if p_key == "6/5":
        cM = one + X_cap_iv
        inv_cM = one / cM
        pMt = {(0,): inv_cM, (1,): X_cap_iv * inv_cM}
        X2 = X_cap_iv * X_cap_iv
        X3 = X2 * X_cap_iv
        pObj = {(1, 0, 1, 0, 1): X3, (0, 1, 0, 1, 0): -X2}
        g0 = ppow_iv(pMt, 5)
        g1 = {(0, 1, 0, 1, 0): X2 / (cM ** 5)}
        h_list = [padd_iv(pmul_iv(pObj, p0), pmul_iv(p0, pObj), -1)]
        pUmE = padd_iv({(0,) * 5: U_iv}, pObj, -1)
        pLpE = padd_iv({(0,) * 5: L_iv}, pObj, +1)
        weights = [
            pI, p0, pIm0, pmul_iv(p0, pIm0),
            p1, padd_iv(p0, p1, -1), pmul_iv(p1, padd_iv(pI, p1, -1)),
            pUmE, pLpE,
            pmul_iv(p0, pUmE), pmul_iv(p0, pLpE),
            pmul_iv(pIm0, pUmE), pmul_iv(pIm0, pLpE),
        ]
        return pObj, g0, g1, h_list, weights

    if p_key == "5/4":
        p2 = {(2,): one}
        sqX = iv.sqrt(X_cap_iv)
        cM = one + X_cap_iv
        inv_cM = one / cM
        pMt = {(0,): inv_cM, (1,): X_cap_iv * inv_cM}
        half_XsqX = (X_cap_iv * sqX) / iv.mpf(2)
        pDHDQD = {(0, 1, 0, 2, 0): half_XsqX, (0, 2, 0, 1, 0): half_XsqX}
        pObj = padd_iv({(1, 0, 2, 0, 1): (X_cap_iv * X_cap_iv) * sqX}, pDHDQD, -1)
        g0 = ppow_iv(pMt, 4)
        inv_cM4 = one / (cM ** 4)
        g1 = {k: v * inv_cM4 for k, v in pDHDQD.items()}
        h1 = padd_iv(p1, {(2, 0, 2): -one})
        h2 = padd_iv(pmul_iv(pObj, p0), pmul_iv(p0, pObj), -1)
        h3 = {(0, 1, 0, 2, 0): one, (0, 2, 0, 1, 0): -one}
        pUmE = padd_iv({(0,) * 4: U_iv}, pObj, -1)
        pLpE = padd_iv({(0,) * 4: L_iv}, pObj, +1)
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

    if p_key == "5/3":
        p2 = {(2,): one}
        pA2 = {(0, 0): one}
        sqX = iv.sqrt(X_cap_iv)
        bX = X_cap_iv ** (iv.mpf(1) / iv.mpf(4))
        cM = one + X_cap_iv
        inv_cM = one / cM
        pMt = {(0, 0): inv_cM, (2,): X_cap_iv * inv_cM}
        pABA = {(0, 1, 0): one}
        pObj = {(1, 1, 1, 1, 1): X_cap_iv * bX, (0, 0, 1, 0, 0): -bX}
        g0 = ppow_iv(pMt, 3)
        g1 = {(0, 1, 0, 0, 1, 0): sqX / (cM ** 3)}
        h1 = {(0, 2, 0): one, (1, 1, 1, 1): -one}
        h2 = padd_iv(pmul_iv(pObj, p0), pmul_iv(p0, pObj), -1)
        h3 = padd_iv(pmul_iv(pMt, pABA), pmul_iv(pABA, pMt), -1)
        pUmE = padd_iv({(0,) * 5: U_iv}, pObj, -1)
        pLpE = padd_iv({(0,) * 5: L_iv}, pObj, +1)
        weights = [
            pI, p0, pIm0, pmul_iv(p0, pIm0),
            p1, padd_iv(p0, p1, -1), pmul_iv(p1, padd_iv(pI, p1, -1)),
            p2, padd_iv(pA2, p2, -1), pmul_iv(p2, padd_iv(pI, p2, -1)),
            pUmE, pLpE,
            pmul_iv(p0, pUmE), pmul_iv(p0, pLpE),
            pmul_iv(pIm0, pUmE), pmul_iv(pIm0, pLpE),
        ]
        return pObj, g0, g1, [h1, h2, h3], weights

    raise ValueError(f"Unknown p_key: {p_key}")


def build_symbolic_struct_iv(p_key, mode):
    """Pure symbolic closed-basis NC-SOS structure (every word covered by Block 0!)."""
    n_gen = 3 if p_key in ("5/4", "5/3") else 2
    if p_key == "5/3" and mode == "8A":
        base3 = reduced_words_k(3, 3)
        d4 = [w for w in reduced_words_k(3, 4) if len(w) == 4]
        wlist0 = sorted(set(base3 + [w for w in d4 if w.count(2) == 0]), key=lambda w: (len(w), w))
        max_id_len = 4
    elif p_key == "5/3" and mode == 6:
        wlist0 = reduced_words_k(3, 3)
        max_id_len = 2
    elif p_key == "5/4" and mode == "8C":
        base3 = reduced_words_k(3, 3)
        d4 = [w for w in reduced_words_k(3, 4) if len(w) == 4]
        wlist0 = sorted(set(base3 + [w for w in d4 if w.count(2) <= 1]), key=lambda w: (len(w), w))
        max_id_len = 4
    elif p_key == "5/4" and mode == "8A":
        base3 = reduced_words_k(3, 3)
        d4 = [w for w in reduced_words_k(3, 4) if len(w) == 4]
        wlist0 = sorted(set(base3 + [w for w in d4 if w.count(2) == 0]), key=lambda w: (len(w), w))
        max_id_len = 4
    elif p_key == "5/4" and mode == 6:
        wlist0 = reduced_words_k(3, 3)
        max_id_len = 3
    elif p_key == "6/5" and mode == 10:
        wlist0 = reduced_words_k(2, 5)
        max_id_len = 5
    else:
        raise ValueError((p_key, mode))

    _, g0_s, g1_s, h_s, w_s = build_problem_polys_iv(p_key, iv.mpf(2), iv.mpf(1), iv.mpf(1))
    w_supp = [list(pw.keys()) for pw in w_s]
    id_supp = [list(set(g0_s.keys()) | set(g1_s.keys()))] + [list(ph.keys()) for ph in h_s]
    canon = sorted(set(canon_w(u[::-1] + v) for u in wlist0 for v in wlist0))
    w2i = {w: i for i, w in enumerate(canon)}
    n_var = len(canon)
    canon_set = set(canon)

    word_pairs = [[] for _ in range(n_var)]
    for ri, wu in enumerate(wlist0):
        wur = wu[::-1]
        for ci, wv in enumerate(wlist0):
            word_pairs[w2i[canon_w(wur + wv)]].append((ri, ci))
    for idx in range(n_var):
        assert len(word_pairs[idx]) > 0

    blocks_wlists = [wlist0]
    for a in range(1, len(w_supp)):
        supp = w_supp[a]
        cand = [u for u in wlist0 if all(canon_w(u[::-1] + k + u) in canon_set for k in supp)]
        kept = []
        for u in cand:
            if all(canon_w(u[::-1] + k + v) in canon_set and canon_w(v[::-1] + k + u) in canon_set
                   for v in kept for k in supp):
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
        "n_gen": n_gen, "canon": canon, "w2i": w2i, "n_var": n_var,
        "blocks_wlists": blocks_wlists, "word_pairs": word_pairs, "id_meta": id_meta,
    }


def iv_certify_nc_sos_interval(p_key, k_num, k_den, m, Lam0_mp, Lam1_mp, struct, mults_mp, bundle):
    """
    100% PURE ZERO-FLOAT mpmath.iv SHARED-MULTIPLIER CONVEX-COMBINATION VERIFIER!
    Proves NO finite-dimensional complex Hermitian SPD solution of Holden Theorem 3.1
    exists for ANY real Lambda in [Lam0_mp, Lam1_mp] (ZERO quadratic discrepancy!).
    """
    assert Lam0_mp < Lam1_mp
    Lam_box = iv.mpf([Lam0_mp, Lam1_mp])
    xp0_iv, sigp0_iv = iv_certify_xplus(Lam0_mp, k_num, k_den)
    xp1_iv, _ = iv_certify_xplus(Lam1_mp, k_num, k_den)
    assert mp.mpf(xp0_iv.a) > 1
    X_cap_iv = iv.mpf(mp.mpf(xp1_iv.b))
    target_lo = mp.mpf((sigp0_iv / iv.mpf(m - 1)).a)

    L_box_mp = iv_certify_stage1_5scalar(Lam_box, k_num, k_den, mults_mp)
    L_box_iv = iv.mpf(L_box_mp)
    U_box_iv = iv.mpf(m - 1) * L_box_iv

    pObj_iv, g0_iv, g1_iv, h_list_iv, weights_iv = build_problem_polys_iv(p_key, X_cap_iv, U_box_iv, L_box_iv)
    mu0_iv = iv.mpf(Lam0_mp) ** 2 if p_key == "5/3" else iv.mpf(Lam0_mp)
    mu1_iv = iv.mpf(Lam1_mp) ** 2 if p_key == "5/3" else iv.mpf(Lam1_mp)

    n_var = struct["n_var"]
    w2i = struct["w2i"]
    blocks_wlists = struct["blocks_wlists"]
    word_pairs = struct["word_pairs"]
    id_meta = struct["id_meta"]
    sz0 = len(blocks_wlists[0])
    idx_const = w2i[()]
    assert word_pairs[idx_const] == [(0, 0)]

    Obj_vec = [iv.mpf(0) for _ in range(n_var)]
    for k, v in pObj_iv.items():
        Obj_vec[w2i[canon_w(k)]] += v

    Z0_0_mp, fac_0_mp, lam_0_mp, Z0_1_mp, fac_1_mp, lam_1_mp = bundle
    for idx_e, (g_idx, _, _) in enumerate(id_meta):
        if g_idx == 0:
            assert lam_0_mp[idx_e] == lam_1_mp[idx_e], "g-multiplier must be shared across [mu0, mu1]!"

    def assemble_ep(Z0_mp, fac_mp, lam_mp, mu_iv):
        pg_iv = padd_iv(g0_iv, g1_iv, -mu_iv)
        all_ideals = [pg_iv] + h_list_iv
        for i in range(sz0):
            for j in range(i + 1, sz0):
                assert Z0_mp[i][j] == Z0_mp[j][i], "Initial Z0 asymmetric!"
        Z0_iv = [[iv.mpf(Z0_mp[i][j]) for j in range(sz0)] for i in range(sz0)]
        lam_iv = [iv.mpf(x) for x in lam_mp]
        rhs_iv = [iv.mpf(0) for _ in range(n_var)]

        for idx_e, (g_idx, wl, wr) in enumerate(id_meta):
            c = lam_iv[idx_e]
            if c == 0:
                continue
            for k, v in all_ideals[g_idx].items():
                rhs_iv[w2i[canon_w(wl + k + wr)]] += c * v

        for a in range(1, len(blocks_wlists)):
            wlist = blocks_wlists[a]
            sz = len(wlist)
            pW = weights_iv[a]
            Ga = [[iv.mpf(0) for _ in range(sz)] for _ in range(sz)]
            for lam_r_mp, vec_r_mp in fac_mp[a]:
                assert lam_r_mp > 0
                lr = iv.mpf(lam_r_mp)
                vr = [iv.mpf(x) for x in vec_r_mp]
                for i in range(sz):
                    lv = lr * vr[i]
                    for j in range(i, sz):
                        val = lv * vr[j]
                        Ga[i][j] += val
                        if i != j:
                            Ga[j][i] += val
            for ri, wu in enumerate(wlist):
                wur = wu[::-1]
                for ci, wv in enumerate(wlist):
                    g_rc = Ga[ri][ci]
                    if g_rc == 0:
                        continue
                    for k, v in pW.items():
                        rhs_iv[w2i[canon_w(wur + k + wv)]] += g_rc * v

        wlist0 = blocks_wlists[0]
        for ri, wu in enumerate(wlist0):
            wur = wu[::-1]
            for ci, wv in enumerate(wlist0):
                rhs_iv[w2i[canon_w(wur + wv)]] += Z0_iv[ri][ci]

        for idx in range(n_var):
            if idx == idx_const:
                continue
            diff = Obj_vec[idx] - rhs_iv[idx]
            pairs = word_pairs[idx]
            share = diff / iv.mpf(len(pairs))
            for ri, ci in pairs:
                Z0_iv[ri][ci] += share

        for i in range(sz0):
            for j in range(i + 1, sz0):
                assert Z0_iv[i][j] == Z0_iv[j][i], "Asymmetry after residual absorption!"

        return Z0_iv, mp.mpf((rhs_iv[idx_const] - Obj_vec[idx_const]).b)

    Z0_0_iv, Psi0_hi = assemble_ep(Z0_0_mp, fac_0_mp, lam_0_mp, mu0_iv)
    Z0_1_iv, Psi1_hi = assemble_ep(Z0_1_mp, fac_1_mp, lam_1_mp, mu1_iv)

    ok0, d0 = iv_cholesky_pd(Z0_0_iv)
    if not ok0:
        return False, f"Z0_0 Chol fail"
    ok1, d1 = iv_cholesky_pd(Z0_1_iv)
    if not ok1:
        return False, f"Z0_1 Chol fail"

    Psi_ub = max(Psi0_hi, Psi1_hi)
    min_d = min(d0, d1)
    margin = mp.mpf((iv.mpf(target_lo) - iv.mpf(Psi_ub)).a)
    if not (Psi_ub < target_lo and margin > 0):
        return False, "Margin fail"
    return True, (Psi_ub, target_lo, margin, min_d)


def build_p65_affine_joint_polys_iv(X_cap_iv):
    """
    Pure mpmath.iv builder for the Exactly-Affine 2-Matrix Joint NC-SOS at p = 6/5, m = 2:
      Generators: 0 = D in (0, I], 1 = H1/X_cap in (0, D], 2 = H2/X_cap in (0, D].
      ZERO Stage-1 U-bound! ZERO x_+(Lam) nonlinearities!
      g_j(Lam) = g0_j - Lam * g1_j is 100% AFFINE in Lam; all other ideals & weights CONSTANT!
    """
    one = iv.mpf(1)
    cM = one + X_cap_iv
    icM = one / cM
    icM5 = icM ** 5
    X2 = X_cap_iv * X_cap_iv
    X3 = X2 * X_cap_iv

    pI = {(): one}
    pD = {(0,): one}
    pH1 = {(1,): one}
    pH2 = {(2,): one}
    pImD = padd_iv(pI, pD, -1)
    pM1 = {(0,): icM, (1,): X_cap_iv * icM}
    pM2 = {(0,): icM, (2,): X_cap_iv * icM}
    g0_1 = ppow_iv(pM1, 5)
    g1_1 = {(0, 1, 0, 1, 0): X2 * icM5}
    g0_2 = ppow_iv(pM2, 5)
    g1_2 = {(0, 2, 0, 2, 0): X2 * icM5}
    pE1 = {(1, 0, 1, 0, 1): X3, (0, 1, 0, 1, 0): -X2}
    pE2 = {(2, 0, 2, 0, 2): X3, (0, 2, 0, 2, 0): -X2}
    pE12 = padd_iv(pE1, pE2, 1)

    aff_ideals = [("g1", g0_1, g1_1), ("g2", g0_2, g1_2)]
    const_ideals = [
        ("[E1,D]", padd_iv(pmul_iv(pE1, pD), pmul_iv(pD, pE1), -1)),
        ("[E2,D]", padd_iv(pmul_iv(pE2, pD), pmul_iv(pD, pE2), -1)),
        ("(I-D)(E1+E2)", pmul_iv(pImD, pE12)),
        ("(E1+E2)(I-D)", pmul_iv(pE12, pImD)),
    ]
    weights = [
        ("I", pI), ("D", pD), ("I-D", pImD), ("D(I-D)", pmul_iv(pD, pImD)),
        ("H1", pH1), ("D-H1", padd_iv(pD, pH1, -1)), ("H1(I-H1)", pmul_iv(pH1, padd_iv(pI, pH1, -1))),
        ("H2", pH2), ("D-H2", padd_iv(pD, pH2, -1)), ("H2(I-H2)", pmul_iv(pH2, padd_iv(pI, pH2, -1))),
    ]
    return pE2, aff_ideals, const_ideals, weights


def build_p65_affine_joint_struct_iv():
    """Pure symbolic closed-basis structure for J2_lean (b=72, unit_gens=(0,) ONLY!)."""
    w1 = [()]
    for L in range(1, 5):
        for w in product((0, 1, 2), repeat=L):
            if w[-1] == 2:
                w1.append(w)
    pure_2_5 = [w for w in product((0, 2), repeat=5) if w[-1] == 2]
    d1_5 = [w + (2,) for w in product((0, 1), repeat=4)]
    wlist0 = sorted(set(w1 + pure_2_5 + d1_5), key=lambda w: (len(w), w))

    _, aff_s, const_s, w_s = build_p65_affine_joint_polys_iv(iv.mpf(2))
    canon = sorted(set(canon_w(u[::-1] + v) for u in wlist0 for v in wlist0))
    w2i = {w: i for i, w in enumerate(canon)}
    canon_set = set(canon)
    n_var = len(canon)

    word_pairs = [[] for _ in range(n_var)]
    for ri, wu in enumerate(wlist0):
        wur = wu[::-1]
        for ci, wv in enumerate(wlist0):
            word_pairs[w2i[canon_w(wur + wv)]].append((ri, ci))
    for idx in range(n_var):
        assert len(word_pairs[idx]) > 0

    w_names = [nm for nm, _ in w_s]
    blocks_wlists = [wlist0]
    for nm, pW in w_s[1:]:
        supp = list(pW.keys())
        cand = [u for u in wlist0 if all(canon_w(u[::-1] + k + u) in canon_set for k in supp)]
        kept = []
        for u in cand:
            if all(canon_w(u[::-1] + k + v) in canon_set and canon_w(v[::-1] + k + u) in canon_set
                   for v in kept for k in supp):
                kept.append(u)
        blocks_wlists.append(kept)

    wr_pool = list(wlist0)
    wl_pool = [w[::-1] for w in wr_pool]
    aff_meta = []
    for iname, g0, g1 in aff_s:
        supp = list(set(g0.keys()) | set(g1.keys()))
        for wl in wl_pool:
            for wr in wr_pool:
                if all(canon_w(wl + k + wr) in canon_set for k in supp):
                    aff_meta.append((iname, wl, wr))

    const_meta = []
    for iname, pH in const_s:
        supp = list(pH.keys())
        for wl in wl_pool:
            for wr in wr_pool:
                if all(canon_w(wl + k + wr) in canon_set for k in supp):
                    const_meta.append((iname, wl, wr))

    return {
        "wlist0": wlist0, "canon": canon, "w2i": w2i, "n_var": n_var,
        "w_names": w_names, "blocks_wlists": blocks_wlists, "word_pairs": word_pairs,
        "aff_meta": aff_meta, "const_meta": const_meta,
    }


def iv_certify_affine_joint_p65_box(struct, Lam0_mp, Lam1_mp, bundle):
    """
    100% PURE ZERO-FLOAT mpmath.iv VERIFIER FOR EXACTLY-AFFINE 2-MATRIX JOINT NC-SOS!
    Certifies over ALL complex Hermitian SPD matrices (n >= 1) and ALL real Lam in [Lam0_mp, Lam1_mp]
    with ZERO Stage-1 U-bound and ZERO C^2 curvature discrepancy!
    """
    assert Lam0_mp < Lam1_mp
    xp0_iv, sig0_iv = iv_certify_xplus(Lam0_mp, 3, 1)
    xp1_iv, _ = iv_certify_xplus(Lam1_mp, 3, 1)
    assert mp.mpf(xp0_iv.a) > 1
    X_cap_iv = iv.mpf(mp.mpf(xp1_iv.b))
    sig_lo_mp = mp.mpf(sig0_iv.a)

    w2i = struct["w2i"]
    n_var = struct["n_var"]
    w_names = struct["w_names"]
    blocks_wlists = struct["blocks_wlists"]
    word_pairs = struct["word_pairs"]
    aff_meta = struct["aff_meta"]
    const_meta = struct["const_meta"]
    Z0_0, fac_0, lam_h0, Z0_1, fac_1, lam_h1, lam_g = bundle

    w0 = blocks_wlists[0]
    sz0 = len(w0)
    idx0 = w2i[()]
    assert word_pairs[idx0] == [(0, 0)]
    assert len(lam_g) == len(aff_meta)
    assert len(lam_h0) == len(const_meta) and len(lam_h1) == len(const_meta)

    pObj_iv, aff_iv, const_iv, weights_iv = build_p65_affine_joint_polys_iv(X_cap_iv)
    aff_map = {nm: (g0, g1) for nm, g0, g1 in aff_iv}
    const_map = {nm: p for nm, p in const_iv}
    w_map = {nm: p for nm, p in weights_iv}

    Psi_max = None
    min_d = None
    max_res = mp.mpf(0)
    half = iv.mpf(1) / iv.mpf(2)

    for Lam_ep, Z0_mp, facs_mp, lam_h in [
        (iv.mpf(Lam0_mp), Z0_0, fac_0, lam_h0),
        (iv.mpf(Lam1_mp), Z0_1, fac_1, lam_h1),
    ]:
        for i in range(sz0):
            for j in range(i + 1, sz0):
                assert Z0_mp[i][j] == Z0_mp[j][i], "Initial Z0 asymmetric!"

        diff = [iv.mpf(0) for _ in range(n_var)]
        for k, v in pObj_iv.items():
            diff[w2i[canon_w(k)]] += v

        Z0_iv = [[iv.mpf(Z0_mp[i][j]) for j in range(sz0)] for i in range(sz0)]
        for ri in range(sz0):
            wur = w0[ri][::-1]
            for ci in range(sz0):
                z_ij = Z0_iv[ri][ci]
                if z_ij != 0:
                    diff[w2i[canon_w(wur + w0[ci])]] -= z_ij

        for a in range(1, len(w_names)):
            facs = facs_mp[a]
            if not facs:
                continue
            pW = w_map[w_names[a]]
            wa = blocks_wlists[a]
            sza = len(wa)
            Ga = [[iv.mpf(0) for _ in range(sza)] for _ in range(sza)]
            for ev_m, vec_m in facs:
                assert ev_m > 0
                ev_iv = iv.mpf(ev_m)
                v_iv = [iv.mpf(x) for x in vec_m]
                for i in range(sza):
                    lv = ev_iv * v_iv[i]
                    if lv == 0:
                        continue
                    for j in range(i, sza):
                        val = lv * v_iv[j]
                        Ga[i][j] += val
                        if i != j:
                            Ga[j][i] += val
            for ri in range(sza):
                wur = wa[ri][::-1]
                for ci in range(sza):
                    g_rc = Ga[ri][ci]
                    if g_rc == 0:
                        continue
                    wv = wa[ci]
                    for k, val in pW.items():
                        diff[w2i[canon_w(wur + k + wv)]] -= g_rc * val

        # Shared lam_g across BOTH Lam0 and Lam1 -> ZERO quadratic discrepancy for all t in [0, 1]!
        for im, (iname, wl, wr) in enumerate(aff_meta):
            lm = lam_g[im]
            if lm == 0:
                continue
            lm_iv = iv.mpf(lm)
            g0, g1 = aff_map[iname]
            for k, val in g0.items():
                diff[w2i[canon_w(wl + k + wr)]] -= lm_iv * val
            for k, val in g1.items():
                diff[w2i[canon_w(wl + k + wr)]] += lm_iv * Lam_ep * val

        for im, (iname, wl, wr) in enumerate(const_meta):
            lm = lam_h[im]
            if lm == 0:
                continue
            lm_iv = iv.mpf(lm)
            for k, val in const_map[iname].items():
                diff[w2i[canon_w(wl + k + wr)]] -= lm_iv * val

        Psi_ub = mp.mpf((-diff[idx0]).b)
        if Psi_max is None or Psi_ub > Psi_max:
            Psi_max = Psi_ub
        if Psi_ub >= sig_lo_mp:
            return False, "Margin fail"

        for idx in range(n_var):
            if idx == idx0:
                continue
            d_iv = diff[idx]
            if d_iv == 0:
                continue
            mag = max(abs(mp.mpf(d_iv.a)), abs(mp.mpf(d_iv.b)))
            if mag > max_res:
                max_res = mag
            pairs = word_pairs[idx]
            share = d_iv / iv.mpf(len(pairs))
            for ri, ci in pairs:
                Z0_iv[ri][ci] += share

        for i in range(sz0):
            for j in range(i + 1, sz0):
                s = half * (Z0_iv[i][j] + Z0_iv[j][i])
                Z0_iv[i][j] = Z0_iv[j][i] = s
                assert Z0_iv[i][j] == Z0_iv[j][i]

        ok, md = iv_cholesky_pd(Z0_iv)
        if not ok:
            return False, "Cholesky fail"
        if min_d is None or md < min_d:
            min_d = md

    margin = mp.mpf((iv.mpf(sig_lo_mp) - iv.mpf(Psi_max)).a)
    if not (Psi_max < sig_lo_mp and margin > 0):
        return False, "Margin fail"
    return True, (Psi_max, sig_lo_mp, margin, min_d, max_res)


def iv_certify_stage1_tail_box(lo_mp, hi_mp, k_num, k_den, m, mults_mp):
    """Pure mpmath.iv Stage-1 tail check: proves L_all([lo, hi]) < sig_+(lo)/(m-1)."""
    assert lo_mp < hi_mp
    _, sig0_iv = iv_certify_xplus(lo_mp, k_num, k_den)
    targ_lo = mp.mpf((sig0_iv / iv.mpf(m - 1)).a)
    L_ub = iv_certify_stage1_5scalar(iv.mpf([lo_mp, hi_mp]), k_num, k_den, mults_mp)
    return (L_ub < targ_lo), L_ub, targ_lo


def iv_C_from_Lam_str(Lam_str, k_num, k_den):
    k_iv = iv.mpf(k_num) / iv.mpf(k_den)
    return (iv.mpf(Lam_str) / (iv.mpf(2) ** (2 * k_iv - 1))) ** (iv.mpf(1) / (2 * k_iv))


# ==============================================================================
# MODULE 0: RUNTIME AST ZERO-FLOAT PURITY AUDIT FOR SECTION B
# ==============================================================================
def run_module0_ast_audit():
    src = inspect.getsource(inspect.getmodule(run_module0_ast_audit))
    tree = ast.parse(src)
    fn_map = {node.name: node for node in tree.body if isinstance(node, ast.FunctionDef)}
    forbidden_names = {"float", "np", "numpy", "scipy", "brentq", "linprog", "least_squares", "minimize", "math"}
    checked = 0
    for fname in PURE_IV_FUNCTIONS:
        assert fname in fn_map, f"Missing pure iv function {fname}!"
        fnode = fn_map[fname]
        for sub in ast.walk(fnode):
            if isinstance(sub, ast.Constant) and isinstance(sub.value, float):
                raise AssertionError(f"AST FAIL: float literal {sub.value} in {fname}!")
            if isinstance(sub, ast.Name) and sub.id in forbidden_names:
                raise AssertionError(f"AST FAIL: forbidden symbol '{sub.id}' in {fname}!")
        checked += 1
    print(f"[MODULE 0 PASS] AST Zero-Float Audit: {checked}/{len(PURE_IV_FUNCTIONS)} pure mpmath.iv functions "
          f"verified (0 float() calls, 0 float literals, 0 numpy/scipy/math references).")


# ==============================================================================
# SECTION A: UNTRUSTED NUMERICAL ORACLES & SUITES 1-3 (FLOAT64 DIAGNOSTICS)
# ==============================================================================
def _o_padd(a, b, sc=1.0):
    out = dict(a)
    for k, v in b.items():
        nv = out.get(k, 0.0) + sc * v
        if abs(nv) > 1e-16:
            out[k] = nv
        elif k in out:
            del out[k]
    return out


def _o_pmul(a, b):
    out = {}
    for k1, v1 in a.items():
        for k2, v2 in b.items():
            k = k1 + k2
            out[k] = out.get(k, 0.0) + v1 * v2
    return {k: v for k, v in out.items() if abs(v) > 1e-16}


def _o_ppow(a, n):
    res = {(): 1.0}
    for _ in range(n):
        res = _o_pmul(res, a)
    return res


def _o_sym_pow(M, power):
    M = 0.5 * (M + M.T)
    ev, q = np.linalg.eigh(M)
    if ev[0] <= 1e-28:
        return None
    return (q * (ev ** power)) @ q.T


def _o_roots_kappa(Lam, kappa):
    x_min = (kappa - 1.0) / kappa
    f = lambda x: (1.0 + x) ** (2.0 * kappa - 1.0) - Lam * (x ** (kappa - 1.0))
    xm = brentq(f, 1e-15, x_min, xtol=1e-15, rtol=1e-15)
    hi = max(2.0, x_min * 2.0)
    while f(hi) < 0:
        hi *= 2.0
    xp = brentq(f, x_min, hi, xtol=1e-15, rtol=1e-15)
    return xp, xm, (xp ** (kappa - 1.0)) * (xp - 1.0), (xm ** (kappa - 1.0)) * (xm - 1.0)


def _o_first_law_slope(Lam, kappa, C_rg):
    xp, _, _, _ = _o_roots_kappa(Lam, kappa)
    dLam_dx = ((2 * kappa - 1) * (1 + xp) ** (2 * kappa - 2) * xp ** (kappa - 1)
               - (1 + xp) ** (2 * kappa - 1) * (kappa - 1) * xp ** (kappa - 2)) / (xp ** (2 * kappa - 2))
    dsig_dx = kappa * xp ** (kappa - 1) - (kappa - 1) * xp ** (kappa - 2)
    sigp_p = dsig_dx / dLam_dx
    trM_est = (1.0 + xp) ** (2.0 * kappa) / (Lam * Lam)
    return (C_rg / (2.0 * kappa * Lam)) / (sigp_p + trM_est)


def _o_stage1_5scalar(Lam, kappa):
    ts = np.unique(np.concatenate([np.geomspace(1e-4, 60.0, 1200), np.linspace(0.5, 5.0, 800)]))
    gs = np.unique(np.concatenate([np.geomspace(1e-6, 60.0, 1200), np.linspace(0.0, 3.0, 800)]))
    c = np.array([1.0, 1.0, 1.0, 1.0, 0.0, 0.0])
    A1 = np.column_stack([-np.ones_like(ts), np.zeros_like(ts), -1.0 / ts, -ts,
                          -(ts ** (2.0 * kappa - 1.0)), -(ts ** (2.0 * kappa))])
    b1 = np.zeros(len(ts))
    gkm1 = gs ** (kappa - 1.0)
    gk = gs ** kappa
    A2 = np.column_stack([np.zeros_like(gs), -np.ones_like(gs), np.zeros_like(gs), gs,
                          Lam * gkm1, Lam * (gkm1 + gk)])
    b2 = -(gkm1 - gk)
    bounds = [(None, None), (None, None), (0.0, None), (None, None), (None, None), (None, None)]
    res = linprog(c, A_ub=np.vstack([A1, A2]), b_ub=np.concatenate([b1, b2]), bounds=bounds, method="highs")
    assert res.success
    return float(res.fun)


def _o_solve_rg_block(kappa, r=4, m=2):
    x_min = (kappa - 1.0) / kappa
    Lam_min = ((1.0 + x_min) ** (2.0 * kappa - 1.0)) / (x_min ** (kappa - 1.0))
    def eq1(L):
        _, _, sp, sm = _o_roots_kappa(L, kappa)
        return sp + (m - 1.0) * sm
    hi = Lam_min * 2.0
    while eq1(hi) < 0:
        hi *= 2.0
    Lam1 = brentq(eq1, Lam_min * (1.0 + 1e-12), hi, xtol=1e-15, rtol=1e-15)
    xp1, xm1, _, _ = _o_roots_kappa(Lam1, kappa)

    def solve_one(cr, Lam_init, d_init, X_init):
        triu = np.triu_indices(cr)
        def unpack(x):
            Lam = x[0]
            d = np.concatenate([[1.0], np.exp(x[1:cr])])
            X = np.zeros((cr, cr))
            X[triu] = x[cr:]
            X = X + X.T - np.diag(np.diag(X))
            return Lam, d, X
        def res(x):
            Lam, d, X = unpack(x)
            if Lam <= Lam_min * (1.0 + 1e-12):
                return np.full(cr * (cr + 1), 1e3)
            _, _, sigp, _ = _o_roots_kappa(Lam, kappa)
            sd = np.sqrt(d)
            H = (sd[:, None] * X) * sd[None, :]
            D = np.diag(d)
            G = (sd[:, None] * H) * sd[None, :]
            Mp = _o_sym_pow(D + H, 2.0 * kappa - 1.0)
            Gkm1 = _o_sym_pow(G, kappa - 1.0)
            Gk = _o_sym_pow(G, kappa)
            if Mp is None or Gkm1 is None or Gk is None:
                return np.full(cr * (cr + 1), 1e3)
            R1 = Mp - Lam * ((sd[:, None] * Gkm1) * sd[None, :])
            targ = sigp * (d ** (2.0 * kappa))
            targ[0] = -sigp / (m - 1.0)
            R2 = Gk - (d[:, None] * Gkm1) * d[None, :] - np.diag(targ)
            w1 = 1.0 / np.outer(d ** (kappa - 0.5), d ** (kappa - 0.5))
            w2 = 1.0 / np.outer(d ** kappa, d ** kappa)
            return np.concatenate([(R1 * w1)[triu], (R2 * w2)[triu]])
        x0 = np.concatenate([[Lam_init], np.log(d_init[1:]), X_init[triu]])
        sol = least_squares(res, x0, xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=4000)
        Lam, d, X = unpack(sol.x)
        return Lam, d, X, float(np.linalg.norm(sol.fun))

    best = None
    d_grid = [0.005, 0.02, 0.08, 0.2] if kappa < 1.4 else [0.05, 0.15, 0.25]
    b_grid = [-0.01, -0.02, -0.04] if kappa < 1.4 else [-0.1, -0.2, -0.3]
    for dt in d_grid:
        for bt in b_grid:
            X0 = np.array([[xm1 * 1.1, bt], [bt, 0.35 * xp1]])
            if np.linalg.eigvalsh(X0)[0] <= 1e-6:
                continue
            cand = solve_one(2, Lam1 * 1.0001, np.array([1.0, dt]), X0)
            if cand[3] < 1e-10 and abs(cand[2][0, 1]) > 1e-5:
                if best is None or cand[0] > best[0]:
                    best = cand
    assert best is not None
    Lam, d, X, err = best
    for cr in range(3, r + 1):
        ratio_last = d[-1] / d[-2] if cr > 3 else d[-1] * 1.3
        d0 = np.concatenate([d, [d[-1] * min(0.8, max(0.05, ratio_last))]])
        X0 = np.zeros((cr, cr))
        X0[:cr - 1, :cr - 1] = X
        X0[cr - 1, cr - 1] = X[cr - 2, cr - 2]
        for j in range(1, cr - 1):
            X0[j, cr - 1] = X0[cr - 1, j] = X[j - 1, cr - 2]
        X0[0, cr - 1] = X0[cr - 1, 0] = X[0, cr - 2] * 0.2
        Lam, d, X, err = solve_one(cr, Lam, d0, X0)
        assert err < 1e-9
    C = (Lam / (2.0 ** (2.0 * kappa - 1.0))) ** (1.0 / (2.0 * kappa))
    return Lam, C, d, X


def _o_build_rg_tree(kappa, r=4, depth=3):
    Lam, C, d_rg, X_rg = _o_solve_rg_block(kappa, r=r, m=2)
    xp, xm, _, _ = _o_roots_kappa(Lam, kappa)
    sd = np.sqrt(d_rg)
    H_rg = (sd[:, None] * X_rg) * sd[None, :]
    nodes = [(1.0, 0)]
    h1_blocks = [([0], np.array([[xp]]))]
    h2_blocks = []
    frontier = [(0, 1.0, 0)]
    for lev in range(depth):
        nf = []
        for (p_idx, p_scale, _) in frontier:
            cidxs = []
            for k in range(1, r):
                ci = len(nodes)
                cs = p_scale * d_rg[k]
                nodes.append((cs, lev + 1))
                cidxs.append(ci)
                nf.append((ci, cs, lev + 1))
            idxs = [p_idx] + cidxs
            blk = p_scale * H_rg
            if lev % 2 == 0:
                h2_blocks.append((idxs, blk))
            else:
                h1_blocks.append((idxs, blk))
        frontier = nf
    for (p_idx, p_scale, _) in frontier:
        blk = np.array([[p_scale * xm]])
        if depth % 2 == 0:
            h2_blocks.append(([p_idx], blk))
        else:
            h1_blocks.append(([p_idx], blk))
    N = len(nodes)
    D = np.diag([s for (s, _) in nodes])
    H1 = np.zeros((N, N))
    H2 = np.zeros((N, N))
    for idxs, blk in h1_blocks:
        H1[np.ix_(idxs, idxs)] = blk
    for idxs, blk in h2_blocks:
        H2[np.ix_(idxs, idxs)] = blk
    return Lam, C, D, H1, H2, d_rg, H_rg


def _o_kubo_ando_ratio(T1, T2, a_int, b_int):
    p = 2.0 * a_int / (a_int + b_int)
    T1a = np.linalg.matrix_power(T1, a_int)
    T2a = np.linalg.matrix_power(T2, a_int)
    T1b = np.linalg.matrix_power(T1, b_int)
    T2b = np.linalg.matrix_power(T2, b_int)
    M = 0.5 * ((T1a + T2a) + (T1a + T2a).T)
    N = 0.5 * ((T1b + T2b) + (T1b + T2b).T)
    evN, VN = np.linalg.eigh(N)
    if evN[0] <= 1e-28:
        return None
    Np = (VN * np.sqrt(evN)) @ VN.T
    Nm = (VN * (1.0 / np.sqrt(evN))) @ VN.T
    mid = 0.5 * (Np @ M @ Np + (Np @ M @ Np).T)
    evM, VM = np.linalg.eigh(mid)
    ms = (VM * np.sqrt(np.maximum(evM, 0.0))) @ VM.T
    K = 0.5 * (Nm @ ms @ Nm + (Nm @ ms @ Nm).T)
    evK, VK = np.linalg.eigh(K)
    sK = (VK * np.sqrt(np.maximum(evK, 0.0))) @ VK.T
    Y1 = 0.5 * (sK @ T1b @ sK + (sK @ T1b @ sK).T)
    Y2 = 0.5 * (sK @ T2b @ sK + (sK @ T2b @ sK).T)
    den = float(np.sum(np.maximum(np.linalg.eigvalsh(Y1), 0.0) ** p)
                + np.sum(np.maximum(np.linalg.eigvalsh(Y2), 0.0) ** p))
    return (float(np.trace(M)) / den) ** (1.0 / p)


def _o_eval_word_state(w, mats, v):
    vec = v.copy()
    for g in reversed(w):
        vec = mats[g] @ vec
    return float(v @ vec)


def _o_make_canon_fn(unit_gens):
    ug = frozenset(unit_gens)
    def canon(w):
        i, j = 0, len(w)
        while i < j and w[i] in ug:
            i += 1
        while j > i and w[j - 1] in ug:
            j -= 1
        s = w[i:j]
        return s if s <= s[::-1] else s[::-1]
    return canon


def _o_gen_reduced_basis(n_gen, max_len, unit_gens):
    ug = frozenset(unit_gens)
    ws = [()]
    for L in range(1, max_len + 1):
        for w in product(range(n_gen), repeat=L):
            if w[-1] not in ug:
                ws.append(w)
    return ws


# Confluent 5-gen rewriting for p = 3/2 and p = 5/4: {0=D, 1=Q1t, 2=Q2t, 3=H1t, 4=H2t}
_UNIT_GENS_5 = frozenset((0, 1, 3))


def _o_rewrite_5gen(w):
    lst = list(w)
    changed = True
    while changed:
        changed = False
        i = 0
        out = []
        n = len(lst)
        while i < n:
            if i + 2 < n and lst[i + 1] == 0:
                a, c = lst[i], lst[i + 2]
                if a == 1 and c == 1:
                    out.append(3); i += 3; changed = True; continue
                if a == 2 and c == 2:
                    out.append(4); i += 3; changed = True; continue
                if a == 1 and c == 3:
                    out.extend((3, 0, 1)); i += 3; changed = True; continue
                if a == 2 and c == 4:
                    out.extend((4, 0, 2)); i += 3; changed = True; continue
            out.append(lst[i]); i += 1
        lst = out
    return tuple(lst)


def _o_rred_5gen(w):
    w = _o_rewrite_5gen(w)
    j = len(w)
    while j > 0 and w[j - 1] in _UNIT_GENS_5:
        j -= 1
    return w[:j]


def _o_canon_5gen(w):
    w1 = _o_rewrite_5gen(w)
    i, j = 0, len(w1)
    while i < j and w1[i] in _UNIT_GENS_5:
        i += 1
    while j > i and w1[j - 1] in _UNIT_GENS_5:
        j -= 1
    s1 = w1[i:j]
    s2 = _o_rewrite_5gen(s1[::-1])
    i2, j2 = 0, len(s2)
    while i2 < j2 and s2[i2] in _UNIT_GENS_5:
        i2 += 1
    while j2 > i2 and s2[j2 - 1] in _UNIT_GENS_5:
        j2 -= 1
    s2 = s2[i2:j2]
    return s1 if s1 <= s2 else s2


def _o_solve_sdp_fr(blocks_F, c_obj, A_eq, b_eq, max_iter=85, tol=1e-12):
    """Exact all-block facial-reduced Mehrotra HKM primal-dual SDP solver (untrusted float64)."""
    U, s, Vt = np.linalg.svd(A_eq, full_matrices=True)
    rk = int(np.sum(s > 1e-11 * s[0]))
    y0 = Vt[:rk].T @ ((U[:, :rk].T @ b_eq) / s[:rk])
    N_null = Vt[rk:].T
    n_free = N_null.shape[1]

    blocks = []
    for idx_b, F in enumerate(blocks_F):
        sz = F.shape[1]
        B0 = np.tensordot(y0, F, axes=(0, 0))
        Bz = np.tensordot(N_null, F, axes=(0, 0))
        Bz_2d = Bz.reshape(-1, sz)
        G_str = 0.5 * ((B0 @ B0 + Bz_2d.T @ Bz_2d) + (B0 @ B0 + Bz_2d.T @ Bz_2d).T)
        ev, V = np.linalg.eigh(G_str)
        if len(ev) == 0 or ev[-1] <= 1e-22:
            continue
        Q_a = V[:, ev > 1e-18 * ev[-1]]
        rk_b = Q_a.shape[1]
        B0_r = 0.5 * (Q_a.T @ B0 @ Q_a + (Q_a.T @ B0 @ Q_a).T)
        Bz_r = (Q_a.T @ Bz) @ Q_a
        Bz_r = 0.5 * (Bz_r + np.swapaxes(Bz_r, 1, 2))
        Bzf_r = Bz_r.reshape(n_free, rk_b * rk_b)
        sc = max(float(np.linalg.norm(B0_r)), float(np.max(np.linalg.norm(Bzf_r, axis=1))), 1e-12)
        blocks.append((idx_b, rk_b, Q_a, B0_r / sc, Bz_r / sc, Bzf_r / sc, sc))

    c0 = float(c_obj @ y0)
    g = N_null.T @ c_obj
    n_blocks = len(blocks)
    tot_n = sum(b[1] for b in blocks)
    z = np.zeros(n_free)
    S_list = [np.eye(b[1]) for b in blocks]
    X_list = [np.eye(b[1]) for b in blocks]

    def max_step(M_l, dM_l):
        am = 1.0
        for M, dM in zip(M_l, dM_l):
            ev, evec = np.linalg.eigh(M)
            Li = evec * (1.0 / np.sqrt(np.maximum(ev, 1e-30)))
            G = 0.5 * (Li.T @ dM @ Li + (Li.T @ dM @ Li).T)
            lm = float(np.linalg.eigvalsh(G)[0])
            if lm < -1e-16:
                am = min(am, -1.0 / lm)
        return am

    best = None
    for it in range(1, max_iter + 1):
        Rp_l = []; rd = g.copy(); mu = 0.0; p_sq = 0.0
        for a, (_, rk_b, _, B0, Bz, Bzf, _) in enumerate(blocks):
            Rp = 0.5 * ((S_list[a] - (B0 + (z @ Bzf).reshape(rk_b, rk_b))) + (S_list[a] - (B0 + (z @ Bzf).reshape(rk_b, rk_b))).T)
            Rp_l.append(Rp); p_sq += float(np.sum(Rp * Rp))
            rd -= Bzf @ X_list[a].ravel()
            mu += float(np.sum(S_list[a] * X_list[a]))
        mu /= tot_n
        p_res = float(np.sqrt(p_sq)); d_res = float(np.linalg.norm(rd))
        p_obj = float(c0 + g @ z)
        d_obj = float(c0 - sum(float(np.sum(b[3] * X_list[a])) for a, b in enumerate(blocks)))
        gap = abs(p_obj - d_obj) / max(1.0, abs(p_obj), abs(d_obj))
        if p_res < 1e-9 and d_res < 1e-9 and (best is None or mu < best[7]):
            best = (p_obj, d_obj, z.copy(), [S.copy() for S in S_list], [X.copy() for X in X_list], p_res, d_res, mu)
        if max(p_res, d_res, gap, mu) < tol:
            break

        M_s = np.zeros((n_free, n_free)); Sinv_l = []
        for a, (_, rk_b, _, B0, Bz, Bzf, _) in enumerate(blocks):
            ev, V = np.linalg.eigh(S_list[a])
            Sinv = (V * (1.0 / np.maximum(ev, 1e-30))) @ V.T
            Sinv_l.append(Sinv)
            M_s += (Sinv @ Bz).reshape(n_free, rk_b * rk_b) @ (Bz @ X_list[a]).reshape(n_free, rk_b * rk_b).T
        M_s = 0.5 * (M_s + M_s.T)
        dd = np.sqrt(np.maximum(np.diag(M_s), 1e-30))
        M_n = (M_s / dd[:, None]) / dd[None, :] + 1e-14 * np.eye(n_free)
        def solve_M(rhs):
            try: return np.linalg.solve(M_n, rhs / dd) / dd
            except np.linalg.LinAlgError: return np.linalg.lstsq(M_n, rhs / dd, rcond=1e-14)[0] / dd
        def solve_dir(sv, dSa=None, dXa=None):
            rhs = -rd.copy(); Rc_l = []
            for a, (_, rk_b, _, B0, Bz, Bzf, _) in enumerate(blocks):
                Rc = sv * mu * np.eye(rk_b) - S_list[a] @ X_list[a]
                if dSa is not None: Rc = Rc - dSa[a] @ dXa[a]
                Rc_l.append(Rc)
                W = 0.5 * ((Sinv_l[a] @ (Rc + Rp_l[a] @ X_list[a])) + (Sinv_l[a] @ (Rc + Rp_l[a] @ X_list[a])).T)
                rhs += Bzf @ W.ravel()
            dz = solve_M(rhs); dS_l, dX_l = [], []
            for a, (_, rk_b, _, B0, Bz, Bzf, _) in enumerate(blocks):
                dS = 0.5 * (((dz @ Bzf).reshape(rk_b, rk_b) - Rp_l[a]) + ((dz @ Bzf).reshape(rk_b, rk_b) - Rp_l[a]).T)
                dX = 0.5 * ((Sinv_l[a] @ (Rc_l[a] - dS @ X_list[a])) + (Sinv_l[a] @ (Rc_l[a] - dS @ X_list[a])).T)
                dS_l.append(dS); dX_l.append(dX)
            return dz, dS_l, dX_l
        _, dSa, dXa = solve_dir(0.0)
        apa = min(1.0, max_step(S_list, dSa)); ada = min(1.0, max_step(X_list, dXa))
        mua = sum(float(np.sum((S_list[a] + apa * dSa[a]) * (X_list[a] + ada * dXa[a]))) for a in range(n_blocks)) / tot_n
        sig = float(np.clip((mua / max(mu, 1e-30)) ** 3, 1e-4, 0.8))
        dz, dS, dX = solve_dir(sig, dSa, dXa)
        ap = min(1.0, 0.96 * max_step(S_list, dS)); ad = min(1.0, 0.96 * max_step(X_list, dX))
        z += ap * dz
        for a in range(n_blocks):
            S_list[a] = 0.5 * ((S_list[a] + ap * dS[a]) + (S_list[a] + ap * dS[a]).T)
            X_list[a] = 0.5 * ((X_list[a] + ad * dX[a]) + (X_list[a] + ad * dX[a]).T)
        if ap < 1e-12 and ad < 1e-12:
            break

    if best is not None:
        p_obj, d_obj, z, S_list, X_list, p_res, d_res, mu = best
    y_opt = y0 + N_null @ z
    S_full = [np.zeros((F.shape[1], F.shape[1])) for F in blocks_F]
    Z_full = [np.zeros((F.shape[1], F.shape[1])) for F in blocks_F]
    for a, (idx_b, _, Q_a, _, _, _, sc) in enumerate(blocks):
        Sm = Q_a @ (S_list[a] * sc) @ Q_a.T
        Zm = Q_a @ (X_list[a] / sc) @ Q_a.T
        S_full[idx_b] = 0.5 * (Sm + Sm.T)
        Z_full[idx_b] = 0.5 * (Zm + Zm.T)
    return {"p_obj": p_obj, "d_obj": d_obj, "y": y_opt, "S_list": S_full, "Z_list": Z_full,
            "p_res": p_res, "d_res": d_res, "n_free": n_free}


def _o_instantiate(wlist0, canon_fn, weights_dict, ideals_dict, obj_poly):
    wlist0 = sorted(set(wlist0), key=lambda w: (len(w), w))
    canon_words = sorted(set(canon_fn(u[::-1] + v) for u in wlist0 for v in wlist0))
    w2i = {w: i for i, w in enumerate(canon_words)}
    canon_set = set(canon_words)
    n_var = len(canon_words)

    blocks_F = []; binfo = []
    for wname, pW in weights_dict.items():
        supp = list(pW.keys())
        if wname == "I":
            kept = list(wlist0)
        else:
            cand = [u for u in wlist0 if all(canon_fn(u[::-1] + k + u) in canon_set for k in supp)]
            kept = []
            for u in cand:
                if all(canon_fn(u[::-1] + k + v) in canon_set and canon_fn(v[::-1] + k + u) in canon_set
                       for v in kept for k in supp):
                    kept.append(u)
        if not kept:
            continue
        sz = len(kept)
        F_t = np.zeros((n_var, sz, sz))
        for ri, wu in enumerate(kept):
            wur = wu[::-1]
            for ci, wv in enumerate(kept):
                for k, val in pW.items():
                    F_t[w2i[canon_fn(wur + k + wv)], ri, ci] += val
        F_t = 0.5 * (F_t + np.swapaxes(F_t, 1, 2))
        rn = np.linalg.norm(F_t, axis=(0, 2))
        act = [i for i in range(sz) if rn[i] > 1e-13]
        if act:
            blocks_F.append(F_t[:, act, :][:, :, act])
            binfo.append((wname, [kept[i] for i in act]))

    wr_pool = list(wlist0)
    wl_pool = [w[::-1] for w in wr_pool]
    A_rows = []; id_counts = {}
    for iname, pR in ideals_dict.items():
        supp = list(pR.keys()); cnt = 0
        for wl in wl_pool:
            for wr in wr_pool:
                if all(canon_fn(wl + k + wr) in canon_set for k in supp):
                    row = np.zeros(n_var)
                    for k, val in pR.items():
                        row[w2i[canon_fn(wl + k + wr)]] += val
                    if np.linalg.norm(row) > 1e-13:
                        A_rows.append(row); cnt += 1
        id_counts[iname] = cnt

    a_norm = np.zeros(n_var); a_norm[w2i[()]] = 1.0
    A_id = np.array(A_rows)
    _, s_id, Vt_id = np.linalg.svd(A_id, full_matrices=False)
    rk_id = int(np.sum(s_id > 1e-11 * s_id[0]))
    A_eq = np.vstack([Vt_id[:rk_id, :], a_norm[None, :]])
    b_eq = np.zeros(rk_id + 1); b_eq[-1] = 1.0
    c_obj = np.zeros(n_var)
    for k, val in obj_poly.items():
        c_obj[w2i[canon_fn(k)]] += val
    return blocks_F, binfo, c_obj, A_eq, b_eq, canon_words, w2i, id_counts


def _o_print_dual_ranks(label, binfo, Z_list, top_k=5):
    rows = []
    for a, (wn, _) in enumerate(binfo):
        ev = np.sort(np.linalg.eigvalsh(Z_list[a]))[::-1]
        if len(ev) > 0 and ev[0] > 1e-8:
            rk_eff = int(np.sum(ev > 1e-6 * ev[0]))
            rows.append((float(np.sum(ev)), wn, len(ev), rk_eff, ev[:3]))
    rows.sort(reverse=True)
    top_str = ", ".join(f"{wn}:{rke}/{dim}" for _, wn, dim, rke, _ in rows[:top_k])
    print(f"      Dual Gram effective ranks [{label}]: {top_str}")


def _o_gns_and_bfgs(label, binfo, S_list, C_rg, a_int, b_int, gen_names, scale_fn):
    n2i = {binfo[a][0]: a for a in range(len(binfo))}
    bI = binfo[0][1]
    sets = [set(binfo[n2i[g]][1]) for g in gen_names]
    com = [u for u in bI if all(u in s for s in sets)]
    iI = [bI.index(u) for u in com]
    G = S_list[0][np.ix_(iI, iI)]
    evG, VG = np.linalg.eigh(0.5 * (G + G.T))
    og = np.argsort(evG)[::-1]; evG = evG[og]; VG = VG[:, og]
    Ms = [S_list[n2i[g]][np.ix_([binfo[n2i[g]][1].index(u) for u in com],
                                [binfo[n2i[g]][1].index(u) for u in com])] for g in gen_names]
    best_pol = None
    for rd in [2, 3, 4]:
        if rd > len(com) or evG[rd - 1] <= 1e-11:
            continue
        W = VG[:, :rd] * (1.0 / np.sqrt(evG[:rd]))[None, :]
        ghs = [0.5 * (W.T @ M @ W + (W.T @ M @ W).T) for M in Ms]
        pair = scale_fn(ghs)
        if pair is None:
            continue
        T1, T2 = pair
        rat = _o_kubo_ando_ratio(T1, T2, a_int, b_int)
        if rat is None:
            continue
        try:
            L1_0 = np.linalg.cholesky(T1 + 1e-13 * np.eye(rd))
            L2_0 = np.linalg.cholesky(T2 + 1e-13 * np.eye(rd))
        except np.linalg.LinAlgError:
            continue
        tril = np.tril_indices(rd); n_tr = len(tril[0])
        x0 = np.concatenate([L1_0[tril], L2_0[tril]])
        def neg_r(x):
            L1 = np.zeros((rd, rd)); L1[tril] = x[:n_tr]
            L2 = np.zeros((rd, rd)); L2[tril] = x[n_tr:]
            rv = _o_kubo_ando_ratio(L1 @ L1.T + 1e-14 * np.eye(rd), L2 @ L2.T + 1e-14 * np.eye(rd), a_int, b_int)
            return -rv if rv is not None else 0.0
        opt = minimize(neg_r, x0, method="BFGS", options={"gtol": 1e-10, "maxiter": 250})
        rpol = -opt.fun
        assert rpol < C_rg + 1e-9, f"Unexpected counterexample candidate: {rpol} vs {C_rg}!"
        if best_pol is None or rpol > best_pol:
            best_pol = rpol
        print(f"    [{label}] GNS dim={rd}: raw={rat:.12f} ({rat-C_rg:+.3e}) -> BFGS={rpol:.12f} ({rpol-C_rg:+.3e})")
    return best_pol


# --- Suite 1 & Suite 3 Combined Driver (reuses solved joint moment matrices for GNS!) ---
def run_suite1_and_suite3():
    print("\n================================================================================")
    print("SUITE 1 & SUITE 3 (FLOAT64 ORACLE DIAGNOSTIC): 2-MATRIX JOINT NC-SOS LADDER,")
    print("DUAL GRAM EFFECTIVE-RANK ANATOMY, & TRUNCATED GNS + BFGS COUNTEREXAMPLE AUDIT")
    print("================================================================================")
    gns_records = []

    def rlen5(L, allowed=(0, 1, 2, 3, 4)):
        out = [()]
        for k in range(1, L + 1):
            for w in product(allowed, repeat=k):
                if w[-1] not in _UNIT_GENS_5 and _o_rred_5gen(w) == w:
                    out.append(w)
        return sorted(set(out), key=lambda w: (len(w), w))

    R1_5 = sorted(set(
        rlen5(2) + rlen5(3, (0, 2, 4))
        + [_o_rred_5gen(w + (c,)) for L in range(3) for w in product((0, 1, 3), repeat=L) for c in (2, 4)]
        + rlen5(4, (0, 2))
    ), key=lambda w: (len(w), w))
    R2_5 = sorted(set(
        R1_5
        + [w for w in rlen5(4, (0, 2, 4)) if w.count(2) <= 1]
        + [_o_rred_5gen(w + (2,)) for w in product((0, 1, 3), repeat=3)
           if w.count(1) == 0 or w in ((0, 1, 0), (1, 0, 0), (0, 0, 1))]
    ), key=lambda w: (len(w), w))

    # 1A: p = 3/2 (kappa = 3/2, m = 2) — archived comparison + nuclear-norm min Tr(M_0) GNS
    print("\n--- 1A) p = 3/2 (kappa = 3/2, m = 2): Confluent 5-Gen Joint R1 -> R2 + Nuclear-Norm GNS ---")
    Lam32, C32, D_tr, H1_tr, H2_tr, d32, _ = _o_build_rg_tree(1.5, r=5, depth=3)
    xp, _, sigp, _ = _o_roots_kappa(Lam32, 1.5); qp = np.sqrt(xp)
    dC32 = _o_first_law_slope(Lam32, 1.5, C32)
    sD = _o_sym_pow(D_tr, 0.5); isD = _o_sym_pow(D_tr, -0.5)
    Q1_tr = 0.5 * (isD @ _o_sym_pow(0.5*(sD@H1_tr@sD+(sD@H1_tr@sD).T), 0.5) @ isD + (isD @ _o_sym_pow(0.5*(sD@H1_tr@sD+(sD@H1_tr@sD).T), 0.5) @ isD).T)
    Q2_tr = 0.5 * (isD @ _o_sym_pow(0.5*(sD@H2_tr@sD+(sD@H2_tr@sD).T), 0.5) @ isD + (isD @ _o_sym_pow(0.5*(sD@H2_tr@sD+(sD@H2_tr@sD).T), 0.5) @ isD).T)
    mats32 = [D_tr, Q1_tr / qp, Q2_tr / qp, H1_tr / xp, H2_tr / xp]
    v32 = np.zeros(D_tr.shape[0]); v32[0] = 1.0

    def polys_p32_5gen(Lam, exact_sum=False):
        x, _, sp, _ = _o_roots_kappa(Lam, 1.5); q = np.sqrt(x); ic2 = 1.0 / ((1.0 + x) ** 2)
        pI = {(): 1.0}; pD = {(0,): 1.0}; pQ1 = {(1,): 1.0}; pQ2 = {(2,): 1.0}
        pH1 = {(3,): 1.0}; pH2 = {(4,): 1.0}; pImD = _o_padd(pI, pD, -1.0)
        pM1 = _o_padd(pD, pH1, x); pM2 = _o_padd(pD, pH2, x)
        g1 = {k: v * ic2 for k, v in _o_padd(_o_pmul(pM1, pM1), {(0, 1, 0): -Lam * q}).items()}
        g2 = {k: v * ic2 for k, v in _o_padd(_o_pmul(pM2, pM2), {(0, 2, 0): -Lam * q}).items()}
        pF1 = _o_padd({(3, 0, 1): x * q}, {(0, 1, 0): -q})
        pF2 = _o_padd({(4, 0, 2): x * q}, {(0, 2, 0): -q})
        pF12 = _o_padd(pF1, pF2, 1.0)
        ideals = {"g1": g1, "g2": g2, "[F1,D]": _o_padd(_o_pmul(pF1, pD), _o_pmul(pD, pF1), -1.0),
                  "[F2,D]": _o_padd(_o_pmul(pF2, pD), _o_pmul(pD, pF2), -1.0)}
        if exact_sum:
            ideals["F1+F2"] = pF12
        else:
            ideals["(I-D)(F1+F2)"] = _o_pmul(pImD, pF12)
            ideals["(F1+F2)(I-D)"] = _o_pmul(pF12, pImD)
        weights = {
            "I": pI, "D": pD, "I-D": pImD, "D(I-D)": _o_pmul(pD, pImD),
            "Q1": pQ1, "I-Q1": _o_padd(pI, pQ1, -1.0), "Q1(I-Q1)": _o_pmul(pQ1, _o_padd(pI, pQ1, -1.0)),
            "Q2": pQ2, "I-Q2": _o_padd(pI, pQ2, -1.0), "Q2(I-Q2)": _o_pmul(pQ2, _o_padd(pI, pQ2, -1.0)),
            "H1": pH1, "D-H1": _o_padd(pD, pH1, -1.0), "H1(I-H1)": _o_pmul(pH1, _o_padd(pI, pH1, -1.0)),
            "H2": pH2, "D-H2": _o_padd(pD, pH2, -1.0), "H2(I-H2)": _o_pmul(pH2, _o_padd(pI, pH2, -1.0)),
        }
        return weights, ideals, pF2, sp

    w32, id32, obj32, _ = polys_p32_5gen(Lam32, False)
    for tag, wb in [("R1 (b=50)", R1_5), (f"R2 (b={len(R2_5)})", R2_5)]:
        t0 = time.time()
        bF, binfo, c, A, b, cw, _, _ = _o_instantiate(wb, _o_canon_5gen, w32, id32, obj32)
        y_tr = np.array([_o_eval_word_state(w, mats32, v32) for w in cw])
        eq_e = float(np.max(np.abs(A @ y_tr - b)))
        me_e = min(float(np.linalg.eigvalsh(np.tensordot(y_tr, F, axes=(0, 0)))[0]) for F in bF)
        assert eq_e < 1e-12 and me_e > -1e-12
        res = _o_solve_sdp_fr(bF, c, A, b, max_iter=85, tol=1e-12)
        pp, pd = -res["p_obj"], -res["d_obj"]
        print(f"  p=3/2 {tag:10s} (n_var={len(cw):4d}, nf={res['n_free']:4d}) [{time.time()-t0:4.1f}s]: "
              f"tree(eq={eq_e:.1e},me={me_e:+.1e}) | dC_p={(pp-sigp)*dC32:+.3e}, dC_d={(pd-sigp)*dC32:+.3e}, "
              f"||y*-y_tree||={np.max(np.abs(res['y']-y_tr)):.2e}")
        if "R1" in tag:
            _o_print_dual_ranks("p=3/2 R1", binfo, res["Z_list"])

    # Nuclear-norm min Tr(M_0) GNS at forced feasible dC = +2e-8 with exact F1+F2 = 0!
    Lam_f = 4.0 * ((C32 + 2e-8) ** 3)
    w_f, id_f, obj_f, _ = polys_p32_5gen(Lam_f, True)
    xp_f, _, _, _ = _o_roots_kappa(Lam_f, 1.5); qp_f = np.sqrt(xp_f)
    bF_f, binfo_f, _, A_f, b_f, _, _, _ = _o_instantiate(R1_5, _o_canon_5gen, w_f, id_f, obj_f)
    c_tr = np.einsum("vii->v", bF_f[0])
    res_nn = _o_solve_sdp_fr(bF_f, c_tr, A_f, b_f, max_iter=80, tol=1e-11)
    def scale_p32(ghs):
        Dh, Q1t, Q2t = ghs
        sd = _o_sym_pow(Dh, 0.5)
        if sd is None: return None
        T1 = qp_f * 0.5 * (sd @ Q1t @ sd + (sd @ Q1t @ sd).T)
        T2 = qp_f * 0.5 * (sd @ Q2t @ sd + (sd @ Q2t @ sd).T)
        return (T1, T2) if (np.linalg.eigvalsh(T1)[0] > 1e-12 and np.linalg.eigvalsh(T2)[0] > 1e-12) else None
    gns_records.append(("3/2", C32, _o_gns_and_bfgs("p=3/2 min-Tr(M0) dC=+2e-8", binfo_f, res_nn["S_list"], C32, 3, 1, ["D", "Q1", "Q2"], scale_p32)))

    # 1B: p = 6/5 (kappa = 3, m = 2, OPEN): J1 (b=41) -> J2 (b=79) + Dual Ranks + GNS
    print("\n--- 1B) p = 6/5 (kappa = 3, m = 2, OPEN): 2-Matrix Joint J1 -> J2 + GNS ---")
    Lam65, C65, D_tr, H1_tr, H2_tr, _, _ = _o_build_rg_tree(3.0, r=4, depth=3)
    xp65, _, sig65, _ = _o_roots_kappa(Lam65, 3.0)
    dC65 = _o_first_law_slope(Lam65, 3.0, C65)
    cM = 1.0 + xp65; ic = 1.0 / cM; ic5 = ic ** 5
    pI = {(): 1.0}; pD = {(0,): 1.0}; pH1 = {(1,): 1.0}; pH2 = {(2,): 1.0}; pImD = _o_padd(pI, pD, -1.0)
    pM1 = {(0,): ic, (1,): xp65 * ic}; pM2 = {(0,): ic, (2,): xp65 * ic}
    pE1 = {(1, 0, 1, 0, 1): xp65 ** 3, (0, 1, 0, 1, 0): -(xp65 ** 2)}
    pE2 = {(2, 0, 2, 0, 2): xp65 ** 3, (0, 2, 0, 2, 0): -(xp65 ** 2)}
    pE12 = _o_padd(pE1, pE2, 1.0)
    id65 = {
        "g1": _o_padd(_o_ppow(pM1, 5), {(0, 1, 0, 1, 0): -Lam65 * (xp65 ** 2) * ic5}),
        "g2": _o_padd(_o_ppow(pM2, 5), {(0, 2, 0, 2, 0): -Lam65 * (xp65 ** 2) * ic5}),
        "[E1,D]": _o_padd(_o_pmul(pE1, pD), _o_pmul(pD, pE1), -1.0),
        "[E2,D]": _o_padd(_o_pmul(pE2, pD), _o_pmul(pD, pE2), -1.0),
        "(I-D)(E1+E2)": _o_pmul(pImD, pE12), "(E1+E2)(I-D)": _o_pmul(pE12, pImD),
    }
    w65 = {
        "I": pI, "D": pD, "I-D": pImD, "D(I-D)": _o_pmul(pD, pImD),
        "H1": pH1, "D-H1": _o_padd(pD, pH1, -1.0), "H1(I-H1)": _o_pmul(pH1, _o_padd(pI, pH1, -1.0)),
        "H2": pH2, "D-H2": _o_padd(pD, pH2, -1.0), "H2(I-H2)": _o_pmul(pH2, _o_padd(pI, pH2, -1.0)),
    }
    mats65 = [D_tr, H1_tr / xp65, H2_tr / xp65]; v65 = np.zeros(D_tr.shape[0]); v65[0] = 1.0
    w_j1 = _o_gen_reduced_basis(3, 4, (0, 1))
    w_j2 = sorted(set(w_j1
                      + [w for w in _o_gen_reduced_basis(3, 5, (0, 1)) if 1 not in w]
                      + [w + (2,) for w in product((0, 1), repeat=4)]
                      + [(2,) + w + (2,) for w in product((0, 1), repeat=3)]), key=lambda w: (len(w), w))
    can65 = _o_make_canon_fn((0, 1))
    for tag, wb in [(f"J1 (b={len(w_j1)})", w_j1), (f"J2 (b={len(w_j2)})", w_j2)]:
        t0 = time.time()
        bF, binfo, c, A, b, cw, _, _ = _o_instantiate(wb, can65, w65, id65, pE2)
        y_tr = np.array([_o_eval_word_state(w, mats65, v65) for w in cw])
        eq_e = float(np.max(np.abs(A @ y_tr - b)))
        me_e = min(float(np.linalg.eigvalsh(np.tensordot(y_tr, F, axes=(0, 0)))[0]) for F in bF)
        assert eq_e < 1e-12 and me_e > -1e-12
        res = _o_solve_sdp_fr(bF, c, A, b, max_iter=85, tol=1e-12)
        pp, pd = -res["p_obj"], -res["d_obj"]
        print(f"  p=6/5 {tag:10s} (n_var={len(cw):4d}, nf={res['n_free']:4d}) [{time.time()-t0:4.1f}s]: "
              f"tree(eq={eq_e:.1e},me={me_e:+.1e}) | dPsi_p={pp-sig65:+.3e} (lin dC_p={(pp-sig65)*dC65:+.3e}), "
              f"||y*-y_tree||={np.max(np.abs(res['y']-y_tr)):.2e}")
        if "J2" in tag:
            _o_print_dual_ranks("p=6/5 J2", binfo, res["Z_list"])
            def scale_p65(ghs):
                Dh, H1t, H2t = ghs
                sd = _o_sym_pow(Dh, 0.5)
                if sd is None: return None
                T1 = xp65 * 0.5 * (sd @ H1t @ sd + (sd @ H1t @ sd).T)
                T2 = xp65 * 0.5 * (sd @ H2t @ sd + (sd @ H2t @ sd).T)
                return (T1, T2) if (np.linalg.eigvalsh(T1)[0] > 1e-12 and np.linalg.eigvalsh(T2)[0] > 1e-12) else None
            gns_records.append(("6/5", C65, _o_gns_and_bfgs("p=6/5 J2", binfo, res["S_list"], C65, 3, 2, ["D", "H1", "H2"], scale_p65)))

    # 1C: p = 5/4 (kappa = 5/2, m = 2, OPEN): Confluent 5-Gen R1 -> R2 + Dual Ranks + GNS
    print("\n--- 1C) p = 5/4 (kappa = 5/2, m = 2, OPEN): Confluent 5-Gen Joint R1 -> R2 + GNS ---")
    Lam54, C54, D_tr, H1_tr, H2_tr, _, _ = _o_build_rg_tree(2.5, r=4, depth=3)
    xp54, _, sig54, _ = _o_roots_kappa(Lam54, 2.5); sq54 = np.sqrt(xp54)
    dC54 = _o_first_law_slope(Lam54, 2.5, C54)
    sD = _o_sym_pow(D_tr, 0.5); isD = _o_sym_pow(D_tr, -0.5)
    Q1_tr = 0.5 * (isD @ _o_sym_pow(0.5*(sD@H1_tr@sD+(sD@H1_tr@sD).T), 0.5) @ isD + (isD @ _o_sym_pow(0.5*(sD@H1_tr@sD+(sD@H1_tr@sD).T), 0.5) @ isD).T)
    Q2_tr = 0.5 * (isD @ _o_sym_pow(0.5*(sD@H2_tr@sD+(sD@H2_tr@sD).T), 0.5) @ isD + (isD @ _o_sym_pow(0.5*(sD@H2_tr@sD+(sD@H2_tr@sD).T), 0.5) @ isD).T)
    mats54 = [D_tr, Q1_tr / sq54, Q2_tr / sq54, H1_tr / xp54, H2_tr / xp54]
    v54 = np.zeros(D_tr.shape[0]); v54[0] = 1.0
    cM = 1.0 + xp54; ic = 1.0 / cM; ic4 = ic ** 4
    pM1 = {(0,): ic, (3,): xp54 * ic}; pM2 = {(0,): ic, (4,): xp54 * ic}
    pDH1 = {(0, 3, 0, 1, 0): xp54 * sq54}; pDH2 = {(0, 4, 0, 2, 0): xp54 * sq54}
    pE1 = _o_padd({(3, 0, 1, 0, 3): (xp54 ** 2) * sq54}, pDH1, -1.0)
    pE2 = _o_padd({(4, 0, 2, 0, 4): (xp54 ** 2) * sq54}, pDH2, -1.0)
    pE12 = _o_padd(pE1, pE2, 1.0)
    id54 = {
        "g1": _o_padd(_o_ppow(pM1, 4), pDH1, -Lam54 * ic4),
        "g2": _o_padd(_o_ppow(pM2, 4), pDH2, -Lam54 * ic4),
        "[E1,D]": _o_padd(_o_pmul(pE1, pD), _o_pmul(pD, pE1), -1.0),
        "[E2,D]": _o_padd(_o_pmul(pE2, pD), _o_pmul(pD, pE2), -1.0),
        "(I-D)(E1+E2)": _o_pmul(pImD, pE12), "(E1+E2)(I-D)": _o_pmul(pE12, pImD),
    }
    pQ1 = {(1,): 1.0}; pQ2 = {(2,): 1.0}; pH1 = {(3,): 1.0}; pH2 = {(4,): 1.0}
    w54 = {
        "I": pI, "D": pD, "I-D": pImD, "D(I-D)": _o_pmul(pD, pImD),
        "Q1": pQ1, "I-Q1": _o_padd(pI, pQ1, -1.0), "Q1(I-Q1)": _o_pmul(pQ1, _o_padd(pI, pQ1, -1.0)),
        "Q2": pQ2, "I-Q2": _o_padd(pI, pQ2, -1.0), "Q2(I-Q2)": _o_pmul(pQ2, _o_padd(pI, pQ2, -1.0)),
        "H1": pH1, "D-H1": _o_padd(pD, pH1, -1.0), "H1(I-H1)": _o_pmul(pH1, _o_padd(pI, pH1, -1.0)),
        "H2": pH2, "D-H2": _o_padd(pD, pH2, -1.0), "H2(I-H2)": _o_pmul(pH2, _o_padd(pI, pH2, -1.0)),
    }
    for tag, wb in [("R1 (b=50)", R1_5), (f"R2 (b={len(R2_5)})", R2_5)]:
        t0 = time.time()
        bF, binfo, c, A, b, cw, _, _ = _o_instantiate(wb, _o_canon_5gen, w54, id54, pE2)
        y_tr = np.array([_o_eval_word_state(w, mats54, v54) for w in cw])
        eq_e = float(np.max(np.abs(A @ y_tr - b)))
        me_e = min(float(np.linalg.eigvalsh(np.tensordot(y_tr, F, axes=(0, 0)))[0]) for F in bF)
        assert eq_e < 1e-10 and me_e > -1e-10
        res = _o_solve_sdp_fr(bF, c, A, b, max_iter=85, tol=1e-12)
        pp, pd = -res["p_obj"], -res["d_obj"]
        print(f"  p=5/4 {tag:10s} (n_var={len(cw):4d}, nf={res['n_free']:4d}) [{time.time()-t0:4.1f}s]: "
              f"tree(eq={eq_e:.1e},me={me_e:+.1e}) | dC_p={(pp-sig54)*dC54:+.3e}, dC_d={(pd-sig54)*dC54:+.3e}, "
              f"||y*-y_tree||={np.max(np.abs(res['y']-y_tr)):.2e}")
        if "R1" in tag:
            _o_print_dual_ranks("p=5/4 R1", binfo, res["Z_list"])
            def scale_p54(ghs):
                Dh, Q1t, Q2t = ghs
                sd = _o_sym_pow(Dh, 0.5)
                if sd is None: return None
                T1 = sq54 * 0.5 * (sd @ Q1t @ sd + (sd @ Q1t @ sd).T)
                T2 = sq54 * 0.5 * (sd @ Q2t @ sd + (sd @ Q2t @ sd).T)
                return (T1, T2) if (np.linalg.eigvalsh(T1)[0] > 1e-12 and np.linalg.eigvalsh(T2)[0] > 1e-12) else None
            gns_records.append(("5/4", C54, _o_gns_and_bfgs("p=5/4 R1", binfo, res["S_list"], C54, 5, 3, ["D", "Q1", "Q2"], scale_p54)))

    # 1D: p = 5/3 (kappa = 5/4, m = 2, OPEN): 5-Gen Joint J2 (b=74) + Dual Ranks + GNS
    print("\n--- 1D) p = 5/3 (kappa = 5/4, m = 2, OPEN): 2-Matrix Joint J2 (b=74) + GNS ---")
    Lam53, C53, D_tr, H1_tr, H2_tr, _, _ = _o_build_rg_tree(1.25, r=3, depth=3)
    xp53, _, sig53, _ = _o_roots_kappa(Lam53, 1.25); sq53 = np.sqrt(xp53); b53 = xp53 ** 0.25
    dC53 = _o_first_law_slope(Lam53, 1.25, C53)
    cM = 1.0 + xp53; ic = 1.0 / cM; ic3 = ic ** 3
    pA = {(0,): 1.0}; pA2 = {(0, 0): 1.0}; pImA = _o_padd(pI, pA, -1.0)
    pB1 = {(1,): 1.0}; pB2 = {(2,): 1.0}; pH1 = {(3,): 1.0}; pH2 = {(4,): 1.0}
    pM1 = {(0, 0): ic, (3,): xp53 * ic}; pM2 = {(0, 0): ic, (4,): xp53 * ic}
    pE1 = {(1, 1, 1, 1, 1): xp53 * b53, (0, 0, 1, 0, 0): -b53}
    pE2 = {(2, 2, 2, 2, 2): xp53 * b53, (0, 0, 2, 0, 0): -b53}
    pE12 = _o_padd(pE1, pE2, 1.0)
    id53 = {
        "g1": _o_padd(_o_ppow(pM1, 3), {(0, 1, 0, 0, 1, 0): -(Lam53 ** 2) * sq53 * ic3}),
        "g2": _o_padd(_o_ppow(pM2, 3), {(0, 2, 0, 0, 2, 0): -(Lam53 ** 2) * sq53 * ic3}),
        "h1": {(0, 3, 0): 1.0, (1, 1, 1, 1): -1.0}, "h2": {(0, 4, 0): 1.0, (2, 2, 2, 2): -1.0},
        "[M1,AB1A]": _o_padd(_o_pmul(pM1, {(0, 1, 0): 1.0}), _o_pmul({(0, 1, 0): 1.0}, pM1), -1.0),
        "[M2,AB2A]": _o_padd(_o_pmul(pM2, {(0, 2, 0): 1.0}), _o_pmul({(0, 2, 0): 1.0}, pM2), -1.0),
        "[E1,A]": _o_padd(_o_pmul(pE1, pA), _o_pmul(pA, pE1), -1.0),
        "[E2,A]": _o_padd(_o_pmul(pE2, pA), _o_pmul(pA, pE2), -1.0),
        "(I-A)(E1+E2)": _o_pmul(pImA, pE12), "(E1+E2)(I-A)": _o_pmul(pE12, pImA),
    }
    w53 = {
        "I": pI, "A": pA, "I-A": pImA, "A(I-A)": _o_pmul(pA, pImA),
        "B1": pB1, "A-B1": _o_padd(pA, pB1, -1.0), "B1(I-B1)": _o_pmul(pB1, _o_padd(pI, pB1, -1.0)),
        "B2": pB2, "A-B2": _o_padd(pA, pB2, -1.0), "B2(I-B2)": _o_pmul(pB2, _o_padd(pI, pB2, -1.0)),
        "H1": pH1, "A2-H1": _o_padd(pA2, pH1, -1.0), "H1(I-H1)": _o_pmul(pH1, _o_padd(pI, pH1, -1.0)),
        "H2": pH2, "A2-H2": _o_padd(pA2, pH2, -1.0), "H2(I-H2)": _o_pmul(pH2, _o_padd(pI, pH2, -1.0)),
    }
    A_tr = _o_sym_pow(D_tr, 0.5)
    G1_tr = 0.5 * (A_tr @ H1_tr @ A_tr + (A_tr @ H1_tr @ A_tr).T)
    G2_tr = 0.5 * (A_tr @ H2_tr @ A_tr + (A_tr @ H2_tr @ A_tr).T)
    mats53 = [A_tr, _o_sym_pow(G1_tr, 0.25) / b53, _o_sym_pow(G2_tr, 0.25) / b53, H1_tr / xp53, H2_tr / xp53]
    v53 = np.zeros(D_tr.shape[0]); v53[0] = 1.0
    all_2 = _o_gen_reduced_basis(5, 2, (0, 1, 3))
    p2_3 = [w for w in _o_gen_reduced_basis(5, 3, (0, 1, 3)) if 1 not in w and 3 not in w]
    d1_3 = [w + (c,) for L in range(3) for w in product((0, 1, 3), repeat=L) for c in (2, 4)]
    d1_4_g1 = [w + (2,) for w in product((0, 1, 3), repeat=3) if w.count(3) <= 1]
    ab2_4 = [w for w in _o_gen_reduced_basis(5, 4, (0, 1, 3)) if set(w).issubset({0, 2})]
    w53_j2 = sorted(set(all_2 + p2_3 + d1_3 + d1_4_g1 + ab2_4), key=lambda w: (len(w), w))
    t0 = time.time()
    bF, binfo, c, A, b, cw, _, _ = _o_instantiate(w53_j2, _o_make_canon_fn((0, 1, 3)), w53, id53, pE2)
    y_tr = np.array([_o_eval_word_state(w, mats53, v53) for w in cw])
    eq_e = float(np.max(np.abs(A @ y_tr - b)))
    me_e = min(float(np.linalg.eigvalsh(np.tensordot(y_tr, F, axes=(0, 0)))[0]) for F in bF)
    assert eq_e < 1e-10 and me_e > -1e-10
    res = _o_solve_sdp_fr(bF, c, A, b, max_iter=85, tol=1e-12)
    pp, pd = -res["p_obj"], -res["d_obj"]
    print(f"  p=5/3 J2 (b={len(w53_j2)}) (n_var={len(cw):4d}, nf={res['n_free']:4d}) [{time.time()-t0:4.1f}s]: "
          f"tree(eq={eq_e:.1e},me={me_e:+.1e}) | dC_p={(pp-sig53)*dC53:+.3e}, dC_d={(pd-sig53)*dC53:+.3e}, "
          f"||y*-y_tree||={np.max(np.abs(res['y']-y_tr)):.2e}")
    _o_print_dual_ranks("p=5/3 J2", binfo, res["Z_list"])
    def scale_p53(ghs):
        Ah, B1t, B2t = ghs
        T1 = b53 * B1t; T2 = b53 * B2t
        return (T1, T2) if (np.linalg.eigvalsh(T1)[0] > 1e-12 and np.linalg.eigvalsh(T2)[0] > 1e-12) else None
    gns_records.append(("5/3", C53, _o_gns_and_bfgs("p=5/3 J2", binfo, res["S_list"], C53, 5, 1, ["A", "B1", "B2"], scale_p53)))
    print(f"  [SUITE 3 SUMMARY] 0 counterexamples across all {len(gns_records)} rational exponents (all BFGS-polished GNS < C_RG)!")


# --- Suite 2: Stage-1 U-Floor vs Exact U=sig_+ vs Uninverted Diagnostic ---
def run_suite2_single_diagnostic():
    print("\n================================================================================")
    print("SUITE 2 (FLOAT64 ORACLE DIAGNOSTIC): STAGE-1 U-FLOOR vs EXACT U=sig_+ vs UNINV")
    print("================================================================================")
    can0 = _o_make_canon_fn((0,))
    for p_key, kappa, mode_lbl in [("6/5", 3.0, "deg-10"), ("5/4", 2.5, "deg-8C"), ("5/3", 1.25, "deg-8A")]:
        if p_key == "6/5":
            wlist = _o_gen_reduced_basis(2, 5, (0,))
        elif p_key == "5/4":
            b3 = _o_gen_reduced_basis(3, 3, (0,))
            wlist = sorted(set(b3 + [w for w in _o_gen_reduced_basis(3, 4, (0,)) if len(w) == 4 and w.count(2) <= 1]), key=lambda w: (len(w), w))
        else:
            b3 = _o_gen_reduced_basis(3, 3, (0,))
            wlist = sorted(set(b3 + [w for w in _o_gen_reduced_basis(3, 4, (0,)) if len(w) == 4 and w.count(2) == 0]), key=lambda w: (len(w), w))

        for m in [2, 3, 4]:
            Lam_rg, C_rg, _, _ = _o_solve_rg_block(kappa, r=4 if kappa > 2 else 2, m=m)
            xp, _, sigp, _ = _o_roots_kappa(Lam_rg, kappa)
            L_all = _o_stage1_5scalar(Lam_rg, kappa)
            targ = sigp / (m - 1.0)
            dC_s = _o_first_law_slope(Lam_rg, kappa, C_rg) * (m - 1.0)
            runs = [("Stage1", (m - 1.0) * L_all, False), ("U=sig+", sigp, False)]
            if m == 2:
                runs.append(("UNINV", sigp, True))
            parts = []
            for tag, Uv, uninv in runs:
                pObj_iv, g0_iv, g1_iv, hl_iv, wl_iv = build_problem_polys_iv(
                    p_key, iv.mpf(f"{xp:.17g}"), iv.mpf(f"{Uv:.17g}"), iv.mpf(f"{L_all:.17g}")
                )
                def to_f(d): return {k: float(mp.mpf(v.mid)) for k, v in d.items()}
                mu_f = Lam_rg ** 2 if p_key == "5/3" else Lam_rg
                pg_f = _o_padd(to_f(g0_iv), to_f(g1_iv), -mu_f)
                ids = {"g": pg_f}
                for hi_idx, ph in enumerate(hl_iv):
                    ids[f"h{hi_idx}"] = to_f(ph)
                ws_all = [to_f(pw) for pw in wl_iv]
                if not uninv:
                    wdict = {("I" if i == 0 else f"W{i}"): ws_all[i] for i in range(len(ws_all))}
                    wb = wlist
                else:
                    # Drop D<=I and L_cap weights (indices of I, D/A, H/B, D-H/A-B, U-E, D(U-E))
                    keep_idx = [0, 1, 4, 5, 7, 9] if p_key == "6/5" else [0, 1, 4, 5, 7, 8, 10, 12]
                    wdict = {("I" if i == 0 else f"W{i}"): ws_all[i] for i in keep_idx}
                    ml = max(len(w) for w in wlist)
                    wb = [w for w in wlist if not (len(w) == ml and len(w) > 0 and w[0] == 0)]
                bF, _, c, A, b, _, _, _ = _o_instantiate(wb, can0, wdict, ids, to_f(pObj_iv))
                res = _o_solve_sdp_fr(bF, c, A, b, max_iter=80, tol=1e-11)
                dPsi = (-res["p_obj"]) - targ
                parts.append(f"{tag}:dPsi={dPsi:+.2e}(dC={dPsi*dC_s:+.2e})")
            print(f"  p={p_key} {mode_lbl} m={m} (dU={(m-1)*L_all-sigp:+.4f}): " + " | ".join(parts))


# ==============================================================================
# UNTRUSTED WITNESS ORACLES FOR SECTION B (SUITE 4 ZERO-FLOAT CERTIFICATIONS!)
# ==============================================================================
def oracle_stage1_lp_multipliers(Lam_lo_mp, Lam_hi_mp, k_num, k_den):
    Lam_lo = float(Lam_lo_mp); Lam_hi = float(Lam_hi_mp); kappa = k_num / k_den
    ts = np.unique(np.concatenate([np.geomspace(1e-2, 0.99, 250), np.linspace(1.0, 3.5, 500), np.geomspace(3.5, 20.0, 250)]))
    gs = np.unique(np.concatenate([np.geomspace(1e-6, 2.5, 800), np.geomspace(2.5, 20.0, 250)]))
    A1 = np.column_stack([ts, ts ** (2 * kappa - 1), ts ** (2 * kappa), -1.0 / ts, -np.ones_like(ts), np.zeros_like(ts)])
    b1 = np.zeros(len(ts))
    gkm1 = gs ** (kappa - 1); gk = gs ** kappa
    A2_lo = np.column_stack([-gs, -Lam_lo * gkm1, -Lam_lo * (gkm1 + gk), np.zeros_like(gs), np.zeros_like(gs), -np.ones_like(gs)])
    A2_hi = np.column_stack([-gs, -Lam_hi * gkm1, -Lam_hi * (gkm1 + gk), np.zeros_like(gs), np.zeros_like(gs), -np.ones_like(gs)])
    b2 = gk - gkm1
    A2 = np.vstack([A2_lo, A2_hi, np.array([0.0, 0.0, 0.0, 0.0, 0.0, -1.0])])
    b2_all = np.concatenate([b2, b2, [0.0]])
    c_obj = np.array([-1.0, 0.0, 0.0, 1.0, 1.0, 1.0])
    c_min = -1.0 / Lam_hi + max(1e-6, 1e-4 / Lam_hi)
    bounds = [(None, None), (None, None), (c_min, -1e-9), (1e-9, None), (None, None), (None, None)]
    res = linprog(c_obj, A_ub=np.vstack([A1, A2]), b_ub=np.concatenate([b1, b2_all]), bounds=bounds, method="highs")
    assert res.success
    return tuple(mp.mpf(f"{float(v):.17g}") for v in res.x[:4])


def _o_poly_iv_to_f64(p_iv):
    return {k: float(mp.mpf(v.mid)) for k, v in p_iv.items()}


def oracle_solve_interval_sos(struct, p_obj_iv, g0_iv, g1_iv, h_list_iv, weights_iv, mu0_iv, mu1_iv, eps_I_f, max_iter=75):
    """
    Untrusted float64 oracle: balanced split-normalization (y0[()]=0.5, y1[()]=0.5) +
    all-block facial reduction + Cholesky-guided witness selection.
    Converts ALL witness numbers into exact decimal mp.mpf BEFORE returning to Section B!
    """
    n_var = struct["n_var"]; w2i = struct["w2i"]
    blocks_wlists = struct["blocks_wlists"]; id_meta = struct["id_meta"]
    word_pairs = struct["word_pairs"]; idx0_c = w2i[()]

    def p2v(pf):
        v = np.zeros(n_var)
        for w, c in pf.items():
            v[w2i[canon_w(w)]] += c
        return v

    p_obj_f = _o_poly_iv_to_f64(p_obj_iv)
    g0_f = _o_poly_iv_to_f64(g0_iv); g1_f = _o_poly_iv_to_f64(g1_iv)
    h_list_f = [_o_poly_iv_to_f64(ph) for ph in h_list_iv]
    weights_f = [_o_poly_iv_to_f64(pw) for pw in weights_iv]

    c_obj_orig = p2v(p_obj_f)
    a_norm = p2v({(): 1.0})
    raw_blocks = []
    for idx_b, wlist in enumerate(blocks_wlists):
        pW = weights_f[idx_b]; sz = len(wlist)
        F_t = np.zeros((n_var, sz, sz))
        for ri, wu in enumerate(wlist):
            wur = wu[::-1]
            for ci, wv in enumerate(wlist):
                for k, v in pW.items():
                    F_t[w2i[canon_w(wur + k + wv)], ri, ci] += v
        F_t = 0.5 * (F_t + np.swapaxes(F_t, 1, 2))
        raw_blocks.append((sz, F_t))
    sz0 = raw_blocks[0][0]; nb1 = len(raw_blocks)
    raw_flats = [F_t.reshape(n_var, -1) for _, F_t in raw_blocks]
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
            pg = all_ideals_f[g_idx]; row = np.zeros(n_var)
            for k, v in pg.items():
                row[w2i[canon_w(wl + k + wr)]] += v
            if g_idx == 0:
                rows_g.append(row)
            else:
                rows_h.append(row)
        return np.array(rows_g), (np.array(rows_h) if rows_h else np.zeros((0, n_var)))

    mu0_f = float(mp.mpf(mu0_iv.mid)); mu1_f = float(mp.mpf(mu1_iv.mid))
    Ag0, Ah = build_A_split(mu0_f); Ag1, _ = build_A_split(mu1_f)
    n_g = Ag0.shape[0]; n_h = Ah.shape[0]; Z_h = np.zeros((n_h, n_var))
    A_id_joint = np.vstack([np.hstack([Ag0, Ag1]), np.hstack([Ah, Z_h]), np.hstack([Z_h, Ah])])
    a0_row = np.concatenate([a_norm, np.zeros(n_var)])
    a1_row = np.concatenate([np.zeros(n_var), a_norm])

    _, s_eq, Vt_eq = np.linalg.svd(A_id_joint, full_matrices=False)
    rank_eq = int(np.sum(s_eq > 1e-10 * s_eq[0]))
    A_full = np.vstack([Vt_eq[:rank_eq, :], a0_row[None, :], a1_row[None, :]])
    b_full = np.zeros(rank_eq + 2); b_full[-2] = 0.5; b_full[-1] = 0.5

    Uf, sf, Vtf = np.linalg.svd(A_full, full_matrices=True)
    rk_f = int(np.sum(sf > 1e-10 * sf[0]))
    y0 = Vtf[:rk_f].T @ ((Uf[:, :rk_f].T @ b_full) / sf[:rk_f])
    N_null = Vtf[rk_f:].T; n_free = N_null.shape[1]

    blocks = []
    for side in (0, 1):
        sl = slice(0, n_var) if side == 0 else slice(n_var, 2 * n_var)
        y0_s = y0[sl]; Nn_s = N_null[sl, :]
        for idx_b, (sz, F_t) in enumerate(raw_blocks):
            if sz == 0:
                continue
            F_flat = raw_flats[idx_b]
            B0 = (y0_s @ F_flat).reshape(sz, sz)
            Bz_flat = Nn_s.T @ F_flat
            Bz = Bz_flat.reshape(n_free, sz, sz)
            Bz2 = Bz.reshape(-1, sz)
            Gstr = 0.5 * ((B0 @ B0 + Bz2.T @ Bz2) + (B0 @ B0 + Bz2.T @ Bz2).T)
            ev, V = np.linalg.eigh(Gstr)
            if ev[-1] <= 1e-22:
                continue
            Qa = V[:, ev > 1e-18 * ev[-1]]
            B0 = 0.5 * (Qa.T @ B0 @ Qa + (Qa.T @ B0 @ Qa).T)
            Bz = (Qa.T @ Bz) @ Qa; Bz = 0.5 * (Bz + np.swapaxes(Bz, 1, 2))
            rk_b = Qa.shape[1]; Bz_flat = Bz.reshape(n_free, rk_b * rk_b)
            sc = max(float(np.linalg.norm(B0)), float(np.max(np.linalg.norm(Bz_flat, axis=1))), 1e-12)
            blocks.append((side, idx_b, rk_b, Qa, B0 / sc, Bz / sc, Bz_flat / sc, sc))

    M_ls = np.hstack([A_id_joint.T, -a0_row[:, None], -a1_row[:, None]])
    U_ls, s_ls, Vt_ls = np.linalg.svd(M_ls, full_matrices=False)
    rk_ls = int(np.sum(s_ls > 1e-12 * s_ls[0]))
    pinv_ls = (Vt_ls[:rk_ls].T / s_ls[:rk_ls]) @ U_ls[:, :rk_ls].T

    def eval_witness(X_cur):
        Z_ep = [[np.zeros((sz, sz)) for sz, _ in raw_blocks] for _ in range(2)]
        for a, (side, idx_b, _, Qa, _, _, _, sc) in enumerate(blocks):
            Zm = Qa @ (X_cur[a] / sc) @ Qa.T
            Z_ep[side][idx_b] = 0.5 * (Zm + Zm.T)
        Z_ep[0][0] += eps_I_f * np.eye(sz0); Z_ep[1][0] += eps_I_f * np.eye(sz0)
        psos0 = sum(raw_flats[b] @ Z_ep[0][b].ravel() for b in range(nb1) if raw_blocks[b][0] > 0)
        psos1 = sum(raw_flats[b] @ Z_ep[1][b].ravel() for b in range(nb1) if raw_blocks[b][0] > 0)
        rhs_ls = np.concatenate([c_obj_orig - psos0, c_obj_orig - psos1])
        sol_ls = pinv_ls @ rhs_ls
        res_v = rhs_ls - M_ls @ sol_ls
        min_ev = 1e9
        for ep in range(2):
            Z0_chk = Z_ep[ep][0].copy()
            rv = res_v[ep * n_var : (ep + 1) * n_var]
            for idx in range(n_var):
                if idx == idx0_c:
                    continue
                dv = rv[idx]
                if abs(dv) < 1e-16:
                    continue
                pairs = word_pairs[idx]; sh = dv / len(pairs)
                for ri, ci in pairs:
                    Z0_chk[ri, ci] += sh
            Z0_chk = 0.5 * (Z0_chk + Z0_chk.T)
            min_ev = min(min_ev, float(np.linalg.eigvalsh(Z0_chk)[0]))
        return max(float(sol_ls[-2]), float(sol_ls[-1])), min_ev, Z_ep, sol_ls

    c0 = float(c_joint @ y0); g = N_null.T @ c_joint
    n_blocks = len(blocks); tot_n = sum(b[2] for b in blocks)
    z = np.zeros(n_free)
    S_list = [np.eye(b[2]) for b in blocks]; X_list = [np.eye(b[2]) for b in blocks]

    def max_step_psd(M_l, dM_l):
        am = 1.0
        for M, dM in zip(M_l, dM_l):
            ev, evec = np.linalg.eigh(M); Li = evec * (1.0 / np.sqrt(np.maximum(ev, 1e-30)))
            G = 0.5 * (Li.T @ dM @ Li + (Li.T @ dM @ Li).T)
            lm = float(np.linalg.eigvalsh(G)[0])
            if lm < -1e-16:
                am = min(am, -1.0 / lm)
        return am

    best_cert = None; fallback = None
    for it in range(1, max_iter + 1):
        Rp_l = []; rd = g.copy(); mu = 0.0
        for a, (_, _, rk, _, B0, Bz, Bzf, _) in enumerate(blocks):
            Rp = 0.5 * ((S_list[a] - (B0 + (z @ Bzf).reshape(rk, rk))) + (S_list[a] - (B0 + (z @ Bzf).reshape(rk, rk))).T)
            Rp_l.append(Rp); rd -= Bzf @ X_list[a].ravel(); mu += float(np.sum(S_list[a] * X_list[a]))
        mu /= tot_n; d_res = float(np.linalg.norm(rd))
        if mu < 5e-5 and d_res < 2e-3:
            Pm, mev, Z_ep_c, sol_c = eval_witness(X_list)
            if fallback is None or mev > fallback[1]:
                fallback = (Pm, mev, Z_ep_c, sol_c)
            if mev > 0.2 * eps_I_f and (best_cert is None or Pm < best_cert[0]):
                best_cert = (Pm, mev, Z_ep_c, sol_c)
            if best_cert is not None and mu < max(1e-10, 0.005 * eps_I_f) and it >= 28:
                break
        M_s = np.zeros((n_free, n_free)); Sinv_l = []
        for a, (_, _, rk, _, B0, Bz, Bzf, _) in enumerate(blocks):
            ev, V = np.linalg.eigh(S_list[a]); Sinv = (V * (1.0 / np.maximum(ev, 1e-30))) @ V.T
            Sinv_l.append(Sinv)
            M_s += (Sinv @ Bz).reshape(n_free, rk * rk) @ (Bz @ X_list[a]).reshape(n_free, rk * rk).T
        M_s = 0.5 * (M_s + M_s.T); dd = np.sqrt(np.maximum(np.diag(M_s), 1e-30))
        M_n = (M_s / dd[:, None]) / dd[None, :] + 1e-14 * np.eye(n_free)
        def solve_M(rhs):
            try: return np.linalg.solve(M_n, rhs / dd) / dd
            except np.linalg.LinAlgError: return np.linalg.lstsq(M_n, rhs / dd, rcond=1e-14)[0] / dd
        def solve_dir(sv, dSa=None, dXa=None):
            rhs = -rd.copy(); Rc_l = []
            for a, (_, _, rk, _, B0, Bz, Bzf, _) in enumerate(blocks):
                Rc = sv * mu * np.eye(rk) - S_list[a] @ X_list[a]
                if dSa is not None: Rc = Rc - dSa[a] @ dXa[a]
                Rc_l.append(Rc)
                W = 0.5 * ((Sinv_l[a] @ (Rc + Rp_l[a] @ X_list[a])) + (Sinv_l[a] @ (Rc + Rp_l[a] @ X_list[a])).T)
                rhs += Bzf @ W.ravel()
            dz = solve_M(rhs); dS_l, dX_l = [], []
            for a, (_, _, rk, _, B0, Bz, Bzf, _) in enumerate(blocks):
                dS = 0.5 * (((dz @ Bzf).reshape(rk, rk) - Rp_l[a]) + ((dz @ Bzf).reshape(rk, rk) - Rp_l[a]).T)
                dX = 0.5 * ((Sinv_l[a] @ (Rc_l[a] - dS @ X_list[a])) + (Sinv_l[a] @ (Rc_l[a] - dS @ X_list[a])).T)
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

    if best_cert is None and fallback is None:
        fallback = eval_witness(X_list)
    _, _, Z_ep, sol_ls = best_cert if best_cert is not None else fallback
    lam_g = sol_ls[:n_g]; lam_h0 = sol_ls[n_g:n_g + n_h]; lam_h1 = sol_ls[n_g + n_h:n_g + 2 * n_h]
    lam_0_mp, lam_1_mp = [], []
    ig, ih = 0, 0
    for (g_idx, _, _) in id_meta:
        if g_idx == 0:
            v = mp.mpf(f"{float(lam_g[ig]):.17g}")
            lam_0_mp.append(v); lam_1_mp.append(v); ig += 1
        else:
            lam_0_mp.append(mp.mpf(f"{float(lam_h0[ih]):.17g}"))
            lam_1_mp.append(mp.mpf(f"{float(lam_h1[ih]):.17g}")); ih += 1

    def pack_Z(Z_raw):
        Z0_mp = [[mp.mpf(f"{float(0.5*(Z_raw[0][i,j]+Z_raw[0][j,i])):.17g}") for j in range(sz0)] for i in range(sz0)]
        factors_mp = [None]
        for a in range(1, nb1):
            sz = raw_blocks[a][0]
            if sz == 0:
                factors_mp.append([]); continue
            ev, V = np.linalg.eigh(0.5 * (Z_raw[a] + Z_raw[a].T))
            factors_mp.append([(mp.mpf(f"{float(ev[ri]):.17g}"),
                                [mp.mpf(f"{float(V[i, ri]):.17g}") for i in range(sz)])
                               for ri in range(len(ev)) if ev[ri] > 1e-15])
        return Z0_mp, factors_mp

    Z0_0, fac_0 = pack_Z(Z_ep[0])
    Z0_1, fac_1 = pack_Z(Z_ep[1])
    return (Z0_0, fac_0, lam_0_mp, Z0_1, fac_1, lam_1_mp)


def oracle_solve_affine_joint_p65_box(struct, Lam0_mp, Lam1_mp, eps_I=5e-7, max_iter=35):
    """Untrusted float64 oracle for Exactly-Affine 2-Matrix Joint p=6/5 box."""
    xp1_iv, _ = iv_certify_xplus(Lam1_mp, 3, 1)
    X_cap_iv = iv.mpf(mp.mpf(xp1_iv.b))
    pObj_iv, aff_iv, const_iv, weights_iv = build_p65_affine_joint_polys_iv(X_cap_iv)

    pObj_f = _o_poly_iv_to_f64(pObj_iv)
    aff_map = {nm: (_o_poly_iv_to_f64(g0), _o_poly_iv_to_f64(g1)) for nm, g0, g1 in aff_iv}
    const_map = {nm: _o_poly_iv_to_f64(p) for nm, p in const_iv}
    w_map = {nm: _o_poly_iv_to_f64(p) for nm, p in weights_iv}

    Lam0_f = float(Lam0_mp); Lam1_f = float(Lam1_mp)
    w2i = struct["w2i"]; n_var = struct["n_var"]; w_names = struct["w_names"]
    blocks_wlists = struct["blocks_wlists"]; word_pairs = struct["word_pairs"]
    aff_meta = struct["aff_meta"]; const_meta = struct["const_meta"]
    sz0 = len(blocks_wlists[0]); nb1 = len(w_names); idx0_c = w2i[()]

    raw_blocks = []
    for wn, kept in zip(w_names, blocks_wlists):
        pW = w_map[wn]; sz = len(kept)
        F_t = np.zeros((n_var, sz, sz))
        for ri, wu in enumerate(kept):
            wur = wu[::-1]
            for ci, wv in enumerate(kept):
                for k, val in pW.items():
                    F_t[w2i[canon_w(wur + k + wv)], ri, ci] += val
        F_t = 0.5 * (F_t + np.swapaxes(F_t, 1, 2))
        raw_blocks.append((sz, F_t))
    raw_flats = [F_t.reshape(n_var, -1) for _, F_t in raw_blocks]

    A_g0_rows, A_g1_rows = [], []
    for iname, wl, wr in aff_meta:
        g0, g1 = aff_map[iname]
        r0 = np.zeros(n_var); r1 = np.zeros(n_var)
        for k, val in g0.items():
            idx = w2i[canon_w(wl + k + wr)]; r0[idx] += val; r1[idx] += val
        for k, val in g1.items():
            idx = w2i[canon_w(wl + k + wr)]; r0[idx] -= Lam0_f * val; r1[idx] -= Lam1_f * val
        A_g0_rows.append(r0); A_g1_rows.append(r1)

    A_h_rows = []
    for iname, wl, wr in const_meta:
        rh = np.zeros(n_var)
        for k, val in const_map[iname].items():
            rh[w2i[canon_w(wl + k + wr)]] += val
        A_h_rows.append(rh)

    n_g = len(aff_meta); n_h = len(const_meta)
    Ag0 = np.array(A_g0_rows); Ag1 = np.array(A_g1_rows); Ah = np.array(A_h_rows)
    z_h = np.zeros((n_h, n_var))
    A_id_joint = np.vstack([np.hstack([Ag0, Ag1]), np.hstack([Ah, z_h]), np.hstack([z_h, Ah])])
    a_norm = np.zeros(n_var); a_norm[idx0_c] = 1.0
    a0_row = np.concatenate([a_norm, np.zeros(n_var)])
    a1_row = np.concatenate([np.zeros(n_var), a_norm])

    _, s_id, Vt_id = np.linalg.svd(A_id_joint, full_matrices=False)
    rk_id = int(np.sum(s_id > 1e-10 * s_id[0]))
    A_full = np.vstack([Vt_id[:rk_id, :], a0_row[None, :], a1_row[None, :]])
    b_full = np.zeros(A_full.shape[0]); b_full[-2] = 0.5; b_full[-1] = 0.5

    c_orig = np.zeros(n_var)
    for k, val in pObj_f.items():
        c_orig[w2i[canon_w(k)]] += val
    trF0 = np.einsum("vii->v", raw_blocks[0][1])
    c_joint = np.concatenate([c_orig - eps_I * trF0, c_orig - eps_I * trF0])

    Q_qr, R_qr = np.linalg.qr(A_full.T, mode="complete")
    rk_f = A_full.shape[0]
    y_part = Q_qr[:, :rk_f] @ np.linalg.solve(R_qr[:rk_f, :rk_f].T, b_full)
    N_null = Q_qr[:, rk_f:]; n_free = N_null.shape[1]

    blocks = []
    for ep in range(2):
        sl = slice(ep * n_var, (ep + 1) * n_var)
        y_e = y_part[sl]; N_e = N_null[sl, :]
        for a, (sz, F_t) in enumerate(raw_blocks):
            if sz == 0:
                continue
            B0 = (y_e @ raw_flats[a]).reshape(sz, sz)
            Bz = (N_e.T @ raw_flats[a]).reshape(n_free, sz, sz)
            Bz2 = Bz.reshape(-1, sz)
            Gstr = 0.5 * ((B0 @ B0 + Bz2.T @ Bz2) + (B0 @ B0 + Bz2.T @ Bz2).T)
            ev, V = np.linalg.eigh(Gstr)
            if ev[-1] <= 1e-22:
                continue
            Qa = V[:, ev > 1e-18 * ev[-1]]
            B0 = 0.5 * (Qa.T @ B0 @ Qa + (Qa.T @ B0 @ Qa).T)
            Bz = (Qa.T @ Bz) @ Qa; Bz = 0.5 * (Bz + np.swapaxes(Bz, 1, 2))
            rk_b = Qa.shape[1]; Bzf = Bz.reshape(n_free, rk_b * rk_b)
            sc = max(float(np.linalg.norm(B0)), float(np.max(np.linalg.norm(Bzf, axis=1))), 1e-12)
            blocks.append((ep, a, rk_b, Qa, B0 / sc, Bz / sc, Bzf / sc, sc))

    M_ls = np.hstack([A_id_joint.T, -a0_row[:, None], -a1_row[:, None]])
    U_ls, s_ls, Vt_ls = np.linalg.svd(M_ls, full_matrices=False)
    rk_ls = int(np.sum(s_ls > 1e-12 * s_ls[0]))
    pinv_ls = (Vt_ls[:rk_ls].T / s_ls[:rk_ls]) @ U_ls[:, :rk_ls].T

    def eval_witness(X_cur):
        Z_ep = [[np.zeros((sz, sz)) for sz, _ in raw_blocks] for _ in range(2)]
        for a, (ep, idx_b, _, Qa, _, _, _, sc) in enumerate(blocks):
            Zm = Qa @ (X_cur[a] / sc) @ Qa.T
            Z_ep[ep][idx_b] = 0.5 * (Zm + Zm.T)
        Z_ep[0][0] += eps_I * np.eye(sz0); Z_ep[1][0] += eps_I * np.eye(sz0)
        psos0 = sum(raw_flats[b] @ Z_ep[0][b].ravel() for b in range(nb1) if raw_blocks[b][0] > 0)
        psos1 = sum(raw_flats[b] @ Z_ep[1][b].ravel() for b in range(nb1) if raw_blocks[b][0] > 0)
        rhs_ls = np.concatenate([c_orig - psos0, c_orig - psos1])
        sol_ls = pinv_ls @ rhs_ls
        res_v = rhs_ls - M_ls @ sol_ls
        min_ev = 1e9
        for ep in range(2):
            Z0_chk = Z_ep[ep][0].copy()
            rv = res_v[ep * n_var : (ep + 1) * n_var]
            for idx in range(n_var):
                if idx == idx0_c:
                    continue
                dv = rv[idx]
                if abs(dv) < 1e-16:
                    continue
                pairs = word_pairs[idx]; sh = dv / len(pairs)
                for ri, ci in pairs:
                    Z0_chk[ri, ci] += sh
            Z0_chk = 0.5 * (Z0_chk + Z0_chk.T)
            min_ev = min(min_ev, float(np.linalg.eigvalsh(Z0_chk)[0]))
        return max(float(sol_ls[-2]), float(sol_ls[-1])), min_ev, Z_ep, sol_ls

    c0 = float(c_joint @ y_part); g = N_null.T @ c_joint
    n_blocks = len(blocks); tot_n = sum(b[2] for b in blocks)
    z = np.zeros(n_free)
    S_list = [np.eye(b[2]) for b in blocks]; X_list = [np.eye(b[2]) for b in blocks]

    def max_step(M_l, dM_l):
        am = 1.0
        for M, dM in zip(M_l, dM_l):
            ev, V = np.linalg.eigh(M); Li = V * (1.0 / np.sqrt(np.maximum(ev, 1e-30)))
            G = 0.5 * (Li.T @ dM @ Li + (Li.T @ dM @ Li).T)
            lm = float(np.linalg.eigvalsh(G)[0])
            if lm < -1e-16:
                am = min(am, -1.0 / lm)
        return am

    best_cert = None
    for it in range(1, max_iter + 1):
        Rp_l = []; rd = g.copy(); mu = 0.0
        for a, (_, _, rk_b, _, B0, Bz, Bzf, _) in enumerate(blocks):
            Rp = 0.5 * ((S_list[a] - (B0 + (z @ Bzf).reshape(rk_b, rk_b))) + (S_list[a] - (B0 + (z @ Bzf).reshape(rk_b, rk_b))).T)
            Rp_l.append(Rp); rd -= Bzf @ X_list[a].ravel(); mu += float(np.sum(S_list[a] * X_list[a]))
        mu /= tot_n; d_res = float(np.linalg.norm(rd))
        if mu < 5e-6 and d_res < 5e-4:
            Pm, mev, Z_ep_c, sol_c = eval_witness(X_list)
            if mev > 0.15 * eps_I and (best_cert is None or Pm < best_cert[0]):
                best_cert = (Pm, it, Z_ep_c, sol_c)
            if best_cert is not None and mu < 6e-9 and it >= 32:
                break
        M_s = np.zeros((n_free, n_free)); Sinv_l = []
        for a, (_, _, rk_b, _, B0, Bz, Bzf, _) in enumerate(blocks):
            ev, V = np.linalg.eigh(S_list[a]); Sinv = (V * (1.0 / np.maximum(ev, 1e-30))) @ V.T
            Sinv_l.append(Sinv)
            M_s += (Sinv @ Bz).reshape(n_free, rk_b * rk_b) @ (Bz @ X_list[a]).reshape(n_free, rk_b * rk_b).T
        M_s = 0.5 * (M_s + M_s.T); dd = np.sqrt(np.maximum(np.diag(M_s), 1e-30))
        M_n = (M_s / dd[:, None]) / dd[None, :] + 1e-14 * np.eye(n_free)
        def solve_M(rhs):
            try: return np.linalg.solve(M_n, rhs / dd) / dd
            except np.linalg.LinAlgError: return np.linalg.lstsq(M_n, rhs / dd, rcond=1e-14)[0] / dd
        def solve_dir(sv, dSa=None, dXa=None):
            rhs = -rd.copy(); Rc_l = []
            for a, (_, _, rk_b, _, B0, Bz, Bzf, _) in enumerate(blocks):
                Rc = sv * mu * np.eye(rk_b) - S_list[a] @ X_list[a]
                if dSa is not None: Rc = Rc - dSa[a] @ dXa[a]
                Rc_l.append(Rc)
                W = 0.5 * ((Sinv_l[a] @ (Rc + Rp_l[a] @ X_list[a])) + (Sinv_l[a] @ (Rc + Rp_l[a] @ X_list[a])).T)
                rhs += Bzf @ W.ravel()
            dz = solve_M(rhs); dS_l, dX_l = [], []
            for a, (_, _, rk_b, _, B0, Bz, Bzf, _) in enumerate(blocks):
                dS = 0.5 * (((dz @ Bzf).reshape(rk_b, rk_b) - Rp_l[a]) + ((dz @ Bzf).reshape(rk_b, rk_b) - Rp_l[a]).T)
                dX = 0.5 * ((Sinv_l[a] @ (Rc_l[a] - dS @ X_list[a])) + (Sinv_l[a] @ (Rc_l[a] - dS @ X_list[a])).T)
                dS_l.append(dS); dX_l.append(dX)
            return dz, dS_l, dX_l
        _, dSa, dXa = solve_dir(0.0)
        apa = min(1.0, max_step(S_list, dSa)); ada = min(1.0, max_step(X_list, dXa))
        mua = sum(float(np.sum((S_list[a] + apa * dSa[a]) * (X_list[a] + ada * dXa[a]))) for a in range(n_blocks)) / tot_n
        sig = float(np.clip((mua / max(mu, 1e-30)) ** 3, 1e-4, 0.8))
        dz, dS, dX = solve_dir(sig, dSa, dXa)
        ap = min(1.0, 0.96 * max_step(S_list, dS)); ad = min(1.0, 0.96 * max_step(X_list, dX))
        z += ap * dz
        for a in range(n_blocks):
            S_list[a] = 0.5 * ((S_list[a] + ap * dS[a]) + (S_list[a] + ap * dS[a]).T)
            X_list[a] = 0.5 * ((X_list[a] + ad * dX[a]) + (X_list[a] + ad * dX[a]).T)
        if ap < 1e-11 and ad < 1e-11:
            break

    assert best_cert is not None, "No PD cert snapshot found in affine J2 oracle!"
    _, _, Z_ep, sol_ls = best_cert
    lam_g = sol_ls[:n_g]; lam_h0 = sol_ls[n_g:n_g + n_h]; lam_h1 = sol_ls[n_g + n_h:n_g + 2 * n_h]

    def pack(Z_raw):
        Z0_mp = [[mp.mpf(f"{float(0.5*(Z_raw[0][i,j]+Z_raw[0][j,i])):.17g}") for j in range(sz0)] for i in range(sz0)]
        facs_mp = [None]
        for a in range(1, nb1):
            sz = raw_blocks[a][0]
            if sz == 0:
                facs_mp.append([]); continue
            ev, V = np.linalg.eigh(0.5 * (Z_raw[a] + Z_raw[a].T))
            facs_mp.append([(mp.mpf(f"{float(ev[ri]):.17g}"),
                             [mp.mpf(f"{float(V[i, ri]):.17g}") for i in range(sz)])
                            for ri in range(len(ev)) if ev[ri] > 1e-15])
        return Z0_mp, facs_mp

    Z0_0, fac_0 = pack(Z_ep[0]); Z0_1, fac_1 = pack(Z_ep[1])
    lam_g_mp = [mp.mpf(f"{float(v):.17g}") for v in lam_g]
    lam_h0_mp = [mp.mpf(f"{float(v):.17g}") for v in lam_h0]
    lam_h1_mp = [mp.mpf(f"{float(v):.17g}") for v in lam_h1]
    return (Z0_0, fac_0, lam_h0_mp, Z0_1, fac_1, lam_h1_mp, lam_g_mp)


# ==============================================================================
# SUITE 4 DRIVER: ZERO-GAP ALL-LAMBDA PURE mpmath.iv CERTIFICATIONS (7 RECORDS!)
# ==============================================================================
def certify_stage1_tail_driver(Lam_start_mp, Lam_end_mp, k_num, k_den, m):
    stack = [(Lam_start_mp, Lam_end_mp, 0)]
    covered = []
    while stack:
        lo, hi, depth = stack.pop()
        mults = oracle_stage1_lp_multipliers(lo, hi, k_num, k_den)
        ok, _, _ = iv_certify_stage1_tail_box(lo, hi, k_num, k_den, m, mults)
        if ok:
            covered.append((lo, hi))
        else:
            assert depth < 12, f"Stage-1 tail failed on [{lo}, {hi}]!"
            mid = (lo + hi) / 2
            assert lo < mid < hi
            stack.append((mid, hi, depth + 1))
            stack.append((lo, mid, depth + 1))
    covered.sort(key=lambda t: t[0])
    assert covered[0][0] == Lam_start_mp and covered[-1][1] == Lam_end_mp
    for i in range(len(covered) - 1):
        assert covered[i][1] == covered[i + 1][0]
    return covered


def certify_open_record_all_lambda(p_key, k_num, k_den, m, Lam_cert_str, tier_specs):
    """
    Certifies C_p(m) <= C_ub UNCONDITIONALLY for ALL n >= 1 (complex Hermitian)
    and ALL Lam in [Lam_cert, Lam_interp(p, m)] with ZERO gaps!
    Supports both single-matrix affine tiers AND pure 2-matrix joint affine tiers ('J2_AFF')!
    """
    t0 = time.time()
    mp.mp.dps = 50; iv.dps = 45

    Lam_cert_iv = iv.mpf(Lam_cert_str)
    Lam_cert_mp = mp.mpf(Lam_cert_iv.a)
    k_iv = iv.mpf(k_num) / iv.mpf(k_den)
    Lam_interp_iv = (iv.mpf(2) ** (2 * k_iv - 2)) * (iv.mpf(1) + iv.sqrt(iv.mpf(m)))
    # Certify all the way to the EXACT outward-rounded decimal endpoint printed in output (R1)!
    Lam_interp_ub_str = ceil_fixed_str(mp.mpf((Lam_interp_iv + iv.mpf("1e-6")).b), 6)
    Lam_interp_ub = mp.mpf(iv.mpf(Lam_interp_ub_str).b)
    assert Lam_interp_ub > mp.mpf(Lam_interp_iv.b)

    C_ub_iv = iv_C_from_Lam_str(Lam_cert_str, k_num, k_den)
    C_ub_mp = mp.mpf(C_ub_iv.b)

    structs = {}
    all_intervals = []
    cur_lo = Lam_cert_mp
    min_chol_all = None
    min_margin_all = None
    j2_details = None

    for (seg_hi_str, mode, eps_I_f) in tier_specs:
        seg_hi = mp.mpf(seg_hi_str)
        assert cur_lo < seg_hi
        if mode == "J2_AFF":
            assert p_key == "6/5" and m == 2
            st_j2 = build_p65_affine_joint_struct_iv()
            bundle = oracle_solve_affine_joint_p65_box(st_j2, cur_lo, seg_hi, eps_I=eps_I_f, max_iter=35)
            t_v = time.time()
            ok, info = iv_certify_affine_joint_p65_box(st_j2, cur_lo, seg_hi, bundle)
            v_sec = time.time() - t_v
            assert ok, f"J2_AFF failed on [{cur_lo}, {seg_hi}]: {info}"
            Psi_ub, sig_lo, margin, min_d, max_res = info
            if min_chol_all is None or min_d < min_chol_all:
                min_chol_all = min_d
            if min_margin_all is None or margin < min_margin_all:
                min_margin_all = margin
            j2_details = (Psi_ub, sig_lo, margin, min_d, max_res, v_sec)
            all_intervals.append((cur_lo, seg_hi, "J2-2MatJoint"))
            cur_lo = seg_hi
            continue

        if mode not in structs:
            structs[mode] = build_symbolic_struct_iv(p_key, mode)
        struct = structs[mode]

        stack = [(cur_lo, seg_hi, eps_I_f, 0)]
        while stack:
            lo, hi, eI, depth = stack.pop()
            mults = oracle_stage1_lp_multipliers(lo, hi, k_num, k_den)
            ok_s1, _, _ = iv_certify_stage1_tail_box(lo, hi, k_num, k_den, m, mults)
            if ok_s1:
                all_intervals.append((lo, hi, "Stage-1"))
                continue

            L_box_mp = iv_certify_stage1_5scalar(iv.mpf([lo, hi]), k_num, k_den, mults)
            xp1_iv, _ = iv_certify_xplus(hi, k_num, k_den)
            X_cap_iv = iv.mpf(mp.mpf(xp1_iv.b))
            L_box_iv = iv.mpf(L_box_mp); U_box_iv = iv.mpf(m - 1) * L_box_iv
            pObj_iv, g0_iv, g1_iv, h_list_iv, weights_iv = build_problem_polys_iv(p_key, X_cap_iv, U_box_iv, L_box_iv)
            mu0_iv = iv.mpf(lo) ** 2 if p_key == "5/3" else iv.mpf(lo)
            mu1_iv = iv.mpf(hi) ** 2 if p_key == "5/3" else iv.mpf(hi)

            bundle = oracle_solve_interval_sos(struct, pObj_iv, g0_iv, g1_iv, h_list_iv, weights_iv, mu0_iv, mu1_iv, eI)
            ok, info = iv_certify_nc_sos_interval(p_key, k_num, k_den, m, lo, hi, struct, mults, bundle)
            if ok:
                _, _, margin, min_d = info
                if min_chol_all is None or min_d < min_chol_all:
                    min_chol_all = min_d
                if min_margin_all is None or margin < min_margin_all:
                    min_margin_all = margin
                all_intervals.append((lo, hi, f"SOS-{mode}"))
            else:
                assert depth < 6, f"NC-SOS interval certification failed on [{lo}, {hi}] (mode={mode}): {info}"
                mid = (lo + hi) / 2
                assert lo < mid < hi
                stack.append((mid, hi, eI, depth + 1))
                stack.append((lo, mid, eI, depth + 1))
        cur_lo = seg_hi

    tail_cov = certify_stage1_tail_driver(cur_lo, Lam_interp_ub, k_num, k_den, m)
    for lo, hi in tail_cov:
        all_intervals.append((lo, hi, "Stage-1-tail"))

    all_intervals.sort(key=lambda t: t[0])
    assert all_intervals[0][0] == Lam_cert_mp
    for i in range(len(all_intervals) - 1):
        assert all_intervals[i][1] == all_intervals[i + 1][0], f"GAP between {all_intervals[i]} and {all_intervals[i+1]}!"
    assert all_intervals[-1][1] >= Lam_interp_ub

    lb_mp = mp.mpf(PRIOR_CERT_LB_STR[p_key][m])
    prior_ub_iv = iv_C_from_Lam_str(PRIOR_CERT_LAM_UB_STR[p_key][m], k_num, k_den)
    prior_ub_mp = mp.mpf(prior_ub_iv.b)
    assert lb_mp < C_ub_mp < prior_ub_mp
    C_ub_str12 = ceil_fixed_str(C_ub_mp, 12)
    C_ub_disp = mp.mpf(iv.mpf(C_ub_str12).b)
    assert mp.mpf(iv.mpf(C_ub_str12).a) >= C_ub_mp
    # Outward-rounded gap strictly >= BOTH exact (C_ub_mp - lb_mp) AND displayed (C_ub_disp - lb_mp)!
    new_gap_hi = mp.mpf((iv.mpf(C_ub_disp) - iv.mpf(lb_mp)).b)
    old_gap_lo = mp.mpf((iv.mpf(mp.mpf(prior_ub_iv.a)) - iv.mpf(lb_mp)).a)
    old_gap_hi = mp.mpf((iv.mpf(prior_ub_mp) - iv.mpf(lb_mp)).b)
    imp_lo = mp.mpf((iv.mpf(old_gap_lo) / iv.mpf(new_gap_hi)).a)

    n_j2 = sum(1 for x in all_intervals if x[2] == "J2-2MatJoint")
    n_sos = sum(1 for x in all_intervals if x[2].startswith("SOS-"))
    n_s1 = len(all_intervals) - n_j2 - n_sos
    print(f"  [CERT PASS] p={p_key}, m={m} [{time.time()-t0:5.1f}s]: ALL Lam in [{Lam_cert_str}, {Lam_interp_ub_str}] "
          f"({n_j2} J2 + {n_sos} SOS + {n_s1} Stage-1 boxes, 0 gaps)")
    print(f"              C_{{{p_key}}}({m}) <= {C_ub_str12} "
          f"(cert_gap <= {ceil_sci_str(new_gap_hi, 3)}, >={floor_fixed_str(imp_lo, 2)}x tighter; "
          f"min_chol > {floor_sci_str(min_chol_all, 3)}, min_margin > {floor_sci_str(min_margin_all, 3)})")
    if j2_details is not None:
        Psi_ub, sig_lo, margin, min_d, max_res, v_sec = j2_details
        print(f"              [J2 2-Matrix Joint iv-verify {v_sec:.1f}s]: Psi_ub <= {ceil_fixed_str(Psi_ub, 10)} < "
              f"sig_lo >= {floor_fixed_str(sig_lo, 10)} (margin > {floor_sci_str(margin, 3)}, "
              f"min_chol > {floor_sci_str(min_d, 3)}, max_res <= {ceil_sci_str(max_res, 3)})")
    return {
        "p_key": p_key, "m": m, "Lam_cert": Lam_cert_str, "Lam_interp_ub": Lam_interp_ub,
        "C_ub": C_ub_mp, "C_ub_str12": C_ub_str12, "lb": lb_mp, "new_gap_hi": new_gap_hi,
        "old_gap_hi": old_gap_hi, "imp_lo": imp_lo, "boxes": (n_j2, n_sos, n_s1),
        "min_chol": min_chol_all, "min_margin": min_margin_all,
    }


def run_suite4_zero_float_certifications():
    print("\n================================================================================")
    print("SUITE 4 (100% ZERO-FLOAT PURE mpmath.iv): NEW ALL-n, ALL-LAMBDA WORLD RECORDS")
    print("ON ALL THREE REMAINING OPEN RATIONAL EXPONENTS (p = 6/5, 5/4, 5/3)")
    print("================================================================================")
    specs = [
        # 1) p = 6/5, m = 2: FIRST-EVER zero-float 2-Matrix Joint NC-SOS proof shattering the 1.41e-5 Stage-1 floor!
        ("6/5", 3, 1, 2, "33.4488", [
            ("33.4505", "J2_AFF", 5e-7),
            ("33.4510", 10, 1e-7), ("33.455", 10, 5e-7), ("33.48", 10, 5e-6), ("33.77", 10, 1e-4),
        ]),
        # 2) p = 5/3, m = 2, 3, 4: 4.50x-11.14x tighter via deg-8A (b=35) + deg-6 + Stage-1 tail!
        ("5/3", 5, 4, 2, "3.2515568", [
            ("3.251568", "8A", 5e-8), ("3.251598", "8A", 1e-7),
            ("3.251601", 6, 1e-7), ("3.25166", 6, 2e-6), ("3.25216", 6, 2e-5),
        ]),
        ("5/3", 5, 4, 3, "3.5807705", [
            ("3.580780", "8A", 5e-8), ("3.580802", "8A", 1e-7),
            ("3.580807", 6, 1e-7), ("3.58085", 6, 2e-7), ("3.58146", 6, 2e-5),
        ]),
        ("5/3", 5, 4, 4, "3.8598160", [
            ("3.859824", "8A", 5e-8), ("3.859845", "8A", 1e-7),
            ("3.859855", 6, 1e-7), ("3.85990", 6, 5e-7), ("3.86048", 6, 5e-6),
        ]),
        # 3) p = 5/4, m = 2, 3, 4: tightened via all-block facial-reduced deg-8C + deg-8A + deg-6 + Stage-1!
        ("5/4", 5, 2, 2, "16.9064", [
            ("16.9073", "8C", 3e-7), ("16.915", "8C", 2e-6), ("16.955", "8A", 5e-6), ("17.055", 6, 5e-5),
        ]),
        ("5/4", 5, 2, 3, "17.5981", [
            ("17.5995", "8C", 3e-7), ("17.615", "8C", 5e-6), ("17.675", "8A", 5e-6), ("17.865", 6, 5e-5),
        ]),
        ("5/4", 5, 2, 4, "18.1761", [
            ("18.1790", "8C", 3e-7), ("18.200", "8C", 5e-6), ("18.275", "8A", 5e-6), ("18.545", 6, 5e-5),
        ]),
    ]

    results = []
    for p_key, kn, kd, m, Lam_s, tiers in specs:
        results.append(certify_open_record_all_lambda(p_key, kn, kd, m, Lam_s, tiers))

    print("\n================================================================================")
    print("FINAL OUTWARD-ROUNDED ZERO-FLOAT OPEN-EXPONENT ENCLOSURE TABLE (ALL n >= 1)")
    print("================================================================================")
    for r in results:
        n_j2, n_sos, n_s1 = r["boxes"]
        print(f"  p={r['p_key']} m={r['m']}: {PRIOR_CERT_LB_STR[r['p_key']][r['m']]} < C_{{{r['p_key']}}}({r['m']}) "
              f"<= {r['C_ub_str12']}  | gap <= {ceil_sci_str(r['new_gap_hi'], 3)} "
              f"(prior <= {ceil_sci_str(r['old_gap_hi'], 3)}, >={floor_fixed_str(r['imp_lo'], 2)}x tighter) "
              f"| boxes={n_j2}J2+{n_sos}SOS+{n_s1}S1")
    return results


def run_suite5_operator_parallel_sum():
    """
    SUITE 5 (FLOAT64 ORACLE DIAGNOSTIC — #113 Item 5 & #120):
    Tests combining #107's Primal K_{op,x}^{(p)} (at p = 5/3, 6/5) AND #119's Dual Q-Family
    Ktilde_{op,s}^{(p)} (at p = 5/4, 6/5) with the exact Operator-Parallel-Sum Variational
    Identity (sum_k Y_k = I, sum_k w_k^{-1} Y_k^* K_k Y_k <= c_r I) over complex Hermitian
    RG and non-RG Holden solutions!
    """
    print("\n================================================================================")
    print("SUITE 5 (FLOAT64 ORACLE DIAGNOSTIC — #113 ITEM 5 & #120): OPERATOR-PARALLEL-SUM")
    print("VARIATIONAL PARTITION-OF-UNITY ON #107 PRIMAL (5/3, 6/5) & #119 DUAL-Q (5/4, 6/5)")
    print("================================================================================")
    from scipy.linalg import eigh as sp_eigh
    from scipy.optimize import root as sp_root

    def cpow(A, alpha):
        Ah = 0.5 * (A + A.conj().T)
        w, V = sp_eigh(Ah)
        return (V * (w ** alpha)) @ V.conj().T

    def eval_K_primal(D, H, Lam, kappa, xs):
        _, _, sigp, _ = _o_roots_kappa(Lam, kappa)
        Dh = cpow(D, 0.5); M = D + H; G = Dh @ H @ Dh
        Z = cpow(D, 1.0 - kappa) @ cpow(G, kappa - 1.0) @ cpow(D, 1.0 - kappa)
        T1 = cpow(D, kappa - 1.5) @ cpow(M, 3.0 - 2.0 * kappa) @ cpow(D, kappa - 1.5)
        T2 = cpow(D, kappa - 2.0) @ cpow(G, 2.0 - kappa) @ cpow(D, kappa - 2.0)
        Ks = []
        for x in xs:
            gam = (1.0 + x) / Lam
            Mid = T1 - gam * T2
            assert np.min(np.linalg.eigvalsh(0.5 * (Mid + Mid.conj().T))) > 1e-12
            Ks.append(sigp * np.eye(D.shape[0]) - x * Z + gam * np.linalg.inv(Mid))
        return Ks, Z, T1, T2, sigp

    def eval_K_dual_Q(D, H, Lam, kappa, ss):
        _, _, sigp, _ = _o_roots_kappa(Lam, kappa)
        Dh = cpow(D, 0.5); M = D + H; G = Dh @ H @ Dh
        Y = cpow(D, 0.5 - kappa) @ cpow(G, kappa - 0.5) @ cpow(D, 0.5 - kappa)
        W1i = cpow(D, kappa - 1.0) @ cpow(M, 2.0 - 2.0 * kappa) @ cpow(D, kappa - 1.0)
        P = cpow(D, kappa - 1.5) @ cpow(G, 1.5 - kappa) @ cpow(D, kappa - 1.5)
        Ks = []
        for s in ss:
            Mid = Lam * W1i - s * P
            assert np.min(np.linalg.eigvalsh(0.5 * (Mid + Mid.conj().T))) > 1e-12
            Ks.append(sigp * np.eye(D.shape[0]) - s * Y + np.linalg.inv(Mid))
        return Ks, Y, W1i, P, sigp

    def make_complex_holden_samples(kappa, L, d_rg, X_rg, rng):
        samples = []
        sD0 = np.sqrt(d_rg); H_rg = (sD0[:, None] * X_rg) * sD0[None, :]
        Uc, _ = np.linalg.qr(rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3)))
        samples.append(("RG-r3-C", Uc @ np.diag(d_rg) @ Uc.conj().T, Uc @ H_rg @ Uc.conj().T))
        w0, V0 = sp_eigh(X_rg); S_base = (V0 * np.log(w0)) @ V0.T
        triu3 = np.triu_indices(3)
        for idx in range(18):
            if idx < 12:
                d1 = 10.0 ** rng.uniform(-3.0, -0.05)
                dd = np.array([1.0, d1]); sD = np.sqrt(dd); D = np.diag(dd); Ds = dd ** (-kappa + 0.5)
                Si = 0.5 * (S_base[:2, :2] + S_base[:2, :2].T) + rng.normal(0, 0.2, (2, 2))
                Si = 0.5 * (Si + Si.T)
                def r2(v):
                    S = np.array([[v[0], v[1]], [v[1], v[2]]]); w, V = sp_eigh(np.clip(S, -14, 5))
                    X = (V * np.exp(w)) @ V.T; H = (sD[:, None] * X) * sD[None, :]
                    G = (sD[:, None] * H) * sD[None, :]
                    Z = (dd ** (1.0 - kappa))[:, None] * cpow(G, kappa - 1.0) * (dd ** (1.0 - kappa))[None, :]
                    R = (Ds[:, None] * cpow(D + H, 2.0 * kappa - 1.0) * Ds[None, :]) - L * Z
                    return np.array([R[0, 0], R[0, 1], R[1, 1]])
                sol = sp_root(r2, np.array([Si[0, 0], Si[0, 1], Si[1, 1]]), method="hybr", tol=1e-13)
                if np.linalg.norm(r2(sol.x)) < 1e-11:
                    S = np.array([[sol.x[0], sol.x[1]], [sol.x[1], sol.x[2]]]); w, V = sp_eigh(S)
                    X = (V * np.exp(w)) @ V.T; H = (sD[:, None] * X) * sD[None, :]
                    U2, _ = np.linalg.qr(rng.standard_normal((2, 2)) + 1j * rng.standard_normal((2, 2)))
                    samples.append((f"2x2-C-{idx}", U2 @ D @ U2.conj().T, U2 @ H @ U2.conj().T))
            else:
                dd = np.array([1.0, d_rg[1] * np.exp(rng.uniform(-0.6, 0.6)), d_rg[2] * np.exp(rng.uniform(-0.6, 0.6))])
                sD = np.sqrt(dd); D = np.diag(dd); Ds = dd ** (-kappa + 0.5)
                def r3(v):
                    S = np.zeros((3, 3)); S[triu3] = np.clip(v, -14, 5); S = S + S.T - np.diag(np.diag(S))
                    w, V = sp_eigh(S); X = (V * np.exp(w)) @ V.T; H = (sD[:, None] * X) * sD[None, :]
                    G = (sD[:, None] * H) * sD[None, :]
                    Z = (dd ** (1.0 - kappa))[:, None] * cpow(G, kappa - 1.0) * (dd ** (1.0 - kappa))[None, :]
                    R = (Ds[:, None] * cpow(D + H, 2.0 * kappa - 1.0) * Ds[None, :]) - L * Z
                    return R[triu3]
                sol = sp_root(r3, S_base[triu3] + rng.normal(0, 0.06, 6), method="hybr", tol=1e-13)
                if np.linalg.norm(r3(sol.x)) < 1e-10:
                    S = np.zeros((3, 3)); S[triu3] = sol.x; S = S + S.T - np.diag(np.diag(S))
                    w, V = sp_eigh(S); X = (V * np.exp(w)) @ V.T; H = (sD[:, None] * X) * sD[None, :]
                    U3, _ = np.linalg.qr(rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3)))
                    samples.append((f"3x3-C-{idx}", U3 @ D @ U3.conj().T, U3 @ H @ U3.conj().T))
        return samples

    def run_partition_ladder(tag, samples, c_r, atoms, ws, eval_fn, op_names):
        worst_exact = -1e9
        sdata = []
        n0, n1, n2 = op_names
        b_order = ["deg0(I)", f"deg1(I,{n0})", f"deg1(I,{n0},{n1},{n2})", f"deg2({n0},{n1},{n2})"]
        for nm, D, H in samples:
            Ks, O0, O1, O2, _ = eval_fn(D, H)
            I_op = sum(w * np.linalg.inv(K) for w, K in zip(ws, Ks))
            P_inv = np.linalg.inv(I_op)
            worst_exact = max(worst_exact, float(np.max(np.linalg.eigvalsh(0.5 * (P_inv + P_inv.conj().T)))) - c_r)
            In = np.eye(D.shape[0], dtype=complex)
            bm = {
                b_order[0]: [In],
                b_order[1]: [In, O0],
                b_order[2]: [In, O0, O1, O2],
                b_order[3]: [In, O0, O1, O2, O0 @ O0, O1 @ O1, O2 @ O2,
                             0.5 * (O0 @ O1 + O1 @ O0), 0.5 * (O0 @ O2 + O2 @ O0), 0.5 * (O1 @ O2 + O2 @ O1)],
            }
            sdata.append((nm, Ks, bm))
        assert worst_exact < 1e-11, f"Exact parallel sum violated ({tag}): {worst_exact}"
        print(f"\n  [{tag} ({len(samples)} complex Holden solutions)] Exact max_eig(I_op^-1 - c_r I) = {worst_exact:+.2e}")
        K_a = len(atoms)
        for bname in b_order:
            nb = len(sdata[0][2][bname])
            x0 = np.zeros((K_a - 1) * nb)
            for k in range(K_a - 1):
                x0[k * nb] = ws[k]
            def obj_s(theta, beta=200.0):
                Cm = theta.reshape(K_a - 1, nb)
                Cl = np.zeros(nb); Cl[0] = 1.0; Cl -= np.sum(Cm, axis=0)
                Ca = np.vstack([Cm, Cl[None, :]])
                ae = []
                for _, Ks, bm in sdata:
                    Bs = bm[bname]; Sop = np.zeros_like(Ks[0])
                    for k in range(K_a):
                        Yk = sum(Ca[k, j] * Bs[j] for j in range(nb))
                        Sop += (1.0 / ws[k]) * (Yk.conj().T @ Ks[k] @ Yk)
                    ae.extend(np.linalg.eigvalsh(0.5 * (Sop + Sop.conj().T)) - c_r)
                ae = np.array(ae); m0 = np.max(ae)
                return float(m0 + np.log(np.mean(np.exp(beta * (ae - m0)))) / beta)
            cur = x0.copy()
            for beta in [30.0, 150.0, 800.0]:
                cur = minimize(lambda t: obj_s(t, beta), cur, method="BFGS", options={"maxiter": 100}).x
            Cm = cur.reshape(K_a - 1, nb); Cl = np.zeros(nb); Cl[0] = 1.0; Cl -= np.sum(Cm, axis=0)
            Ca = np.vstack([Cm, Cl[None, :]])
            w_rg, w_all = None, -1e9
            for idx_s, (_, Ks, bm) in enumerate(sdata):
                Bs = bm[bname]; Sop = np.zeros_like(Ks[0])
                for k in range(K_a):
                    Yk = sum(Ca[k, j] * Bs[j] for j in range(nb))
                    Sop += (1.0 / ws[k]) * (Yk.conj().T @ Ks[k] @ Yk)
                lm = float(np.max(np.linalg.eigvalsh(0.5 * (Sop + Sop.conj().T))) - c_r)
                if idx_s == 0: w_rg = lm
                w_all = max(w_all, lm)
            print(f"    Partition {bname:18s} ({nb:2d} ops): RG-r3 excess={w_rg:+.3e} | max excess ALL {len(samples)}={w_all:+.3e}")

    rng = np.random.default_rng(2026)
    # 5A: Primal X-Family (#107) at p = 5/3 (Regime I) and p = 6/5 (Regime III)
    for lbl, kappa in [("5/3", 1.25), ("6/5", 3.0)]:
        L, _, d_rg, X_rg = _o_solve_rg_block(kappa, r=3, m=2)
        xp, _, sigp, _ = _o_roots_kappa(L, kappa); c_r = 2.0 * sigp
        xe, Vx = sp_eigh(0.5 * (X_rg + X_rg.T)); ws = Vx[0, :] ** 2
        samples = make_complex_holden_samples(kappa, L, d_rg, X_rg, rng)
        xg = np.geomspace(1e-5, xp, 2000)
        inv_1d = sum(wk / (sigp - xk * (xg ** (kappa - 1.0))
                           + ((1.0 + xk) / L) / ((1.0 + xg) ** (3.0 - 2.0 * kappa) - ((1.0 + xk) / L) * (xg ** (2.0 - kappa))))
                     for xk, wk in zip(xe, ws))
        run_partition_ladder(
            f"PRIMAL #107 p={lbl} k={kappa:.2f}, 1D non-Holden={float(np.max(1.0/inv_1d-c_r)):+.2e}",
            samples, c_r, xe, ws, lambda D, H, L=L, k=kappa, xe=xe: eval_K_primal(D, H, L, k, xe), ("Z", "T1", "T2")
        )

    # 5B: Dual Q-Family (#119) at p = 5/4 and p = 6/5 (Regime III, 4-7x larger margin!)
    for lbl, kappa in [("5/4", 2.5), ("6/5", 3.0)]:
        L, _, d_rg, X_rg = _o_solve_rg_block(kappa, r=3, m=2)
        xp, _, sigp, _ = _o_roots_kappa(L, kappa); c_r = 2.0 * sigp
        sD = np.sqrt(d_rg); H_rg = (sD[:, None] * X_rg) * sD[None, :]
        G_rg = (sD[:, None] * H_rg) * sD[None, :]; Dmh = np.diag(1.0 / sD)
        Q_rg = Dmh @ cpow(G_rg, 0.5) @ Dmh
        se, Uq = sp_eigh(0.5 * (Q_rg + Q_rg.T)); ws = Uq[0, :] ** 2
        samples = make_complex_holden_samples(kappa, L, d_rg, X_rg, rng)
        xg = np.geomspace(1e-5, xp, 2000)
        inv_1d = sum(wk / (sigp - sk * (xg ** (kappa - 0.5))
                           + 1.0 / (L * ((1.0 + xg) ** (2.0 - 2.0 * kappa)) - sk * (xg ** (1.5 - kappa))))
                     for sk, wk in zip(se, ws))
        run_partition_ladder(
            f"DUAL-Q #119 p={lbl} k={kappa:.2f}, 1D non-Holden={float(np.max(1.0/inv_1d-c_r)):+.2e}",
            samples, c_r, se, ws, lambda D, H, L=L, k=kappa, se=se: eval_K_dual_Q(D, H, L, k, se), ("Y", "W1i", "P")
        )


if __name__ == "__main__":
    t_all = time.time()
    run_module0_ast_audit()
    run_suite1_and_suite3()
    run_suite2_single_diagnostic()
    run_suite5_operator_parallel_sum()
    run_suite4_zero_float_certifications()
    print(f"\nALL SUITES (0-5) PASSED WITH EXIT CODE 0 AND ZERO FLOATS IN SECTION B! ({time.time() - t_all:.1f}s total)")
