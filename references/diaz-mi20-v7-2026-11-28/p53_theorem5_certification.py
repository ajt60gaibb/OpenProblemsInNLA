#!/usr/bin/env python3
"""
================================================================================
OPEN PROBLEM MI-20: p = 5/3 THEOREM-5 DEGREE-3 AFFINE-IN-LAMBDA (A, B, C) LIFT,
100% ZERO-FLOAT mpmath.iv ALL-DIMENSIONS WORLD RECORDS (m = 2, 3, 4),
3x3 POLYNOMIAL PARALLEL-SUM SCHUR COMPLEMENT BENCHMARK, & ANALYTIC OBSTRUCTIONS
================================================================================
Author: nc-operator-prover (deliverable for #152)
Target: 100% self-contained verification (stdlib + mpmath + numpy/scipy only;
        zero external scratch imports; zero modifications outside scratch/).

STRICT EPISTEMIC ARCHITECTURE:
  - SECTION B (PROVED — 100% Pure Zero-Float mpmath.iv, mp.dps=55, iv.dps=50):
      Module 0: Whole-Section-B AST Zero-Float Purity Audit + Outward Formatter
                Self-Tests (0 float/complex literals, 0 float() calls,
                0 numpy/scipy/math/sympy references across ALL Section-B code).
      Suite 1:  All-n >= 1, complex Hermitian C^n, ALL-Lambda zero-gap mpmath.iv
                certifications at p = 5/3 (kappa = 5/4) for m in {2, 3, 4},
                shattering the #139 / V7 world records by >=1.93x-2.71x (>=8.72x-27.13x vs V6) via:
                  * Theorem 1 (Degree-3 Exactly-Affine (A, B, C) Lift B^3 = Lam ACA
                    & Parameter-Free Degree-3 Kubo-Ando Weight A Bt A - Ct^3 >= 0)
                  * Theorem 2 (Zero-Discrepancy Shared-Multiplier Convex-Combination
                    Certification over [Lam_cert, Lam_interp,ub(5/3, m)] with 0 gaps)
  - SECTION A (UNTRUSTED FLOAT64 ORACLES & DIAGNOSTICS):
      Oracle:   Balanced split-normalization + exact all-block facial reduction
                + In-Loop X-Metric Dual Projection (dX = X (sum al_k B_k) X),
                converting all candidate witnesses to exact decimal mp.mpf strings
                BEFORE passing to Section B (zero trust placed in float64).
      Suite 2:  Theorem-5 2-Atom Parallel Sum 3x3 Degree-3 Polynomial Block Schur
                Complement Mtilde_2a(A, B, C) >= 0 (ZERO [E, A], ZERO U-E, ZERO L+E)
                across ~100 exact 1x1/2x2/3x3 Holden solutions + 3x3 Block NC-SOS
                SDP + exact ker(A) v_k-norm-inflation obstruction diagnosis.
      Suite 3:  Attack 2 — Purely Analytic Investigation of 1-Atom + Contraction V:
                  * Suite 3A: Complex U(3) verification of Theorem 3 (A Bt A >= Ct^3)
                    and Theorem 5 (2-line Universal Expectation Enclosure
                    E_v[G] in [x_-, x_+] for all p in [4/3, 2) & E_v[C] at p = 5/3).
                  * Suite 3B: Theorem 4(a) Holden-Free 1x1 Positivity Trap
                    (B_{sigma_+} >= 0 everywhere on (0, x_+] => K_0 + V^* B V >= K_0).
                  * Suite 3C: Theorem 4(b) Non-Holden 2x2 Misalignment Obstruction
                    (even obeying ALL 1st-use Holden bounds + indefinite B_{sigma_+})
                    and Theorem 4(c) True Holden Non-Commutative Eigenvector-Alignment
                    Cancellation Anatomy (cos^2 = 0.999978 onto neg eigvec of B_{sp}).
"""

import ast
import heapq
from itertools import product
from pathlib import Path
import time

import mpmath as mp
from mpmath import iv

mp.mp.dps = 55
iv.dps = 50


# ==============================================================================
# SECTION B: 100% PURE ZERO-FLOAT mpmath.iv VERIFIER & CERTIFICATION ENGINE
# (Every function listed in SECTION_B_FUNCS is AST-audited: ZERO float/complex
#  literals, ZERO float() calls, ZERO numpy/scipy/math/sympy references!)
# ==============================================================================

# Exact outward-floored lower bounds certified in rigorous_iv_multi_p_bounds.py (#49)
# and matched verbatim in #139 Table 1 and V7 (#162):
PRIOR_CERT_LB_STR = {
    2: "1.057348913859",
    3: "1.098935623593",
    4: "1.132421930734",
}

# Prior #139 / V7 certified upper bounds (Table 1 of joint_ncsos_gns_report.md, signed off #138):
PRIOR_139_UB_STR = {
    2: "1.057349442325",
    3: "1.098936497802",
    4: "1.132422900743",
}

# Exact V6 certified Lambda_cert values (rigorous_iv_multi_p_bounds.py L1442-1444):
PRIOR_V6_LAM_STR = {
    2: "3.251598",
    3: "3.580802",
    4: "3.859845",
}


def ceil_fixed_str(val_mp, digits):
    """Strict outward ceiling decimal string with `digits` fractional digits, self-asserted."""
    scale = mp.mpf(10) ** digits
    n = int(mp.ceil(val_mp * scale))
    neg = n < 0
    an = -n if neg else n
    ten_d = 10 ** digits
    s = f"{'-' if neg else ''}{an // ten_d}.{an % ten_d:0{digits}d}"
    while mp.mpf(iv.mpf(s).a) < val_mp:
        n += 1
        neg = n < 0
        an = -n if neg else n
        s = f"{'-' if neg else ''}{an // ten_d}.{an % ten_d:0{digits}d}"
    assert mp.mpf(iv.mpf(s).a) >= val_mp
    return s


def floor_fixed_str(val_mp, digits):
    """Strict outward floor decimal string with `digits` fractional digits, self-asserted."""
    scale = mp.mpf(10) ** digits
    n = int(mp.floor(val_mp * scale))
    neg = n < 0
    an = -n if neg else n
    ten_d = 10 ** digits
    s = f"{'-' if neg else ''}{an // ten_d}.{an % ten_d:0{digits}d}"
    while mp.mpf(iv.mpf(s).b) > val_mp:
        n -= 1
        neg = n < 0
        an = -n if neg else n
        s = f"{'-' if neg else ''}{an // ten_d}.{an % ten_d:0{digits}d}"
    assert mp.mpf(iv.mpf(s).b) <= val_mp
    return s


def ceil_sci_str(val_mp, sig_digits):
    """Strict outward ceiling scientific string (> 0) with `sig_digits` significant digits."""
    assert val_mp > mp.mpf(0)
    exp_i = int(mp.floor(mp.log10(val_mp)))
    shift = sig_digits - 1 - exp_i
    if shift >= 0:
        scale = mp.mpf(10) ** shift
        m_int = int(mp.ceil(val_mp * scale))
    else:
        scale = mp.mpf(10) ** (-shift)
        m_int = int(mp.ceil(val_mp / scale))
    ten_s = 10 ** sig_digits
    if m_int >= ten_s:
        m_int = (m_int + 9) // 10
        exp_i += 1
    ten_m1 = 10 ** (sig_digits - 1)
    while True:
        lead = m_int // ten_m1
        rem = m_int % ten_m1
        s = f"{lead}.{rem:0{sig_digits - 1}d}e{exp_i:+03d}" if sig_digits > 1 else f"{lead}e{exp_i:+03d}"
        if mp.mpf(iv.mpf(s).a) >= val_mp:
            return s
        m_int += 1
        if m_int >= ten_s:
            m_int = (m_int + 9) // 10
            exp_i += 1


def floor_sci_str(val_mp, sig_digits):
    """Strict outward floor scientific string (> 0) with `sig_digits` significant digits."""
    assert val_mp > mp.mpf(0)
    exp_i = int(mp.floor(mp.log10(val_mp)))
    shift = sig_digits - 1 - exp_i
    if shift >= 0:
        scale = mp.mpf(10) ** shift
        m_int = int(mp.floor(val_mp * scale))
    else:
        scale = mp.mpf(10) ** (-shift)
        m_int = int(mp.floor(val_mp / scale))
    ten_m1 = 10 ** (sig_digits - 1)
    if m_int < ten_m1:
        m_int = ten_m1 * 10 - 1
        exp_i -= 1
    while True:
        lead = m_int // ten_m1
        rem = m_int % ten_m1
        s = f"{lead}.{rem:0{sig_digits - 1}d}e{exp_i:+03d}" if sig_digits > 1 else f"{lead}e{exp_i:+03d}"
        if mp.mpf(iv.mpf(s).b) <= val_mp:
            return s
        m_int -= 1
        if m_int < ten_m1:
            m_int = ten_m1 * 10 - 1
            exp_i -= 1


def canon_w_iv(w):
    """Canonical word under A v = v (strip outer 0's) and Hermitian involution."""
    i = 0
    j = len(w)
    while i < j and w[i] == 0:
        i += 1
    while j > i and w[j - 1] == 0:
        j -= 1
    w1 = w[i:j]
    w2 = w1[::-1]
    return w1 if w1 <= w2 else w2


def reduced_words_iv(n_gen, max_d):
    """All words of length <= max_d with no trailing 0 (A v = v)."""
    out = [()]
    for d in range(1, max_d + 1):
        for w in product(range(n_gen), repeat=d):
            if w[-1] != 0:
                out.append(w)
    return out


def gen_words_iv(n_gen, max_d):
    """All words of length <= max_d on alphabet {0, ..., n_gen - 1}."""
    out = [()]
    for d in range(1, max_d + 1):
        out.extend(product(range(n_gen), repeat=d))
    return out


def pmul_iv(p, q):
    """Exact interval multiplication of non-commutative polynomials."""
    out = {}
    for w1, c1 in p.items():
        for w2, c2 in q.items():
            w = w1 + w2
            if w in out:
                out[w] = out[w] + c1 * c2
            else:
                out[w] = c1 * c2
    return out


def padd_iv(p, q, s=1):
    """Exact interval linear combination p + s * q."""
    s_iv = iv.mpf(s) if not isinstance(s, iv.mpf) else s
    out = dict(p)
    for w, c in q.items():
        if w in out:
            out[w] = out[w] + s_iv * c
        else:
            out[w] = s_iv * c
    return out


def iv_cholesky_pd(M):
    """Pure mpmath.iv interval Cholesky test: returns (True, min_diag_lo) iff M >> 0."""
    n = len(M)
    L = [[iv.mpf(0) for _ in range(n)] for _ in range(n)]
    min_diag = None
    for i in range(n):
        for j in range(i):
            s = M[i][j]
            for k in range(j):
                s = s - L[i][k] * L[j][k]
            L[i][j] = s / L[j][j]
        s = M[i][i]
        for k in range(i):
            s = s - L[i][k] * L[i][k]
        if mp.mpf(s.a) <= mp.mpf(0):
            return False, mp.mpf(s.a)
        L[i][i] = iv.sqrt(s)
        da = mp.mpf(L[i][i].a)
        if min_diag is None or da < min_diag:
            min_diag = da
    return True, min_diag


def iv_certify_xplus_53(Lam_mp):
    """
    Pure mpmath.iv enclosure of x_+(Lam) > 1 and sigma_+(Lam) = x_+^{1/4}(x_+ - 1)
    at p = 5/3 (kappa = 5/4): unique root > 1 of (1 + x)^{3/2} = Lam * x^{1/4}.
    """
    one = iv.mpf(1)
    Lam_iv = iv.mpf(Lam_mp)
    twokm1_m = mp.mpf(3) / mp.mpf(2)
    km1_m = mp.mpf(1) / mp.mpf(4)
    x_min_m = mp.mpf(1) / mp.mpf(5)

    x_m = mp.mpf("1.3")
    for _ in range(90):
        fv = (mp.mpf(1) + x_m) ** twokm1_m - Lam_mp * (x_m ** km1_m)
        dfv = twokm1_m * ((mp.mpf(1) + x_m) ** (mp.mpf(1) / mp.mpf(2))) - Lam_mp * km1_m * (x_m ** (-mp.mpf(3) / mp.mpf(4)))
        x_m -= fv / dfv
        if x_m <= x_min_m:
            x_m = mp.mpf("1.5")

    rad = mp.mpf("1e-28")
    xl = x_m - rad
    xh = x_m + rad
    assert xl > mp.mpf(1)
    # Use exact nested sqrt for (1+x)^{3/2} and x^{1/4}
    def f_iv(x_b):
        s1 = iv.sqrt(one + x_b)
        q4 = iv.sqrt(iv.sqrt(x_b))
        return (one + x_b) * s1 - Lam_iv * q4

    fl = f_iv(iv.mpf(xl))
    fh = f_iv(iv.mpf(xh))
    assert mp.mpf(fl.b) < mp.mpf(0) and mp.mpf(fh.a) > mp.mpf(0)
    xp_iv = iv.mpf([xl, xh])
    sigp_iv = iv.sqrt(iv.sqrt(xp_iv)) * (xp_iv - one)
    return xp_iv, sigp_iv


def iv_sup_1d(f_and_df, lo, hi, tol_str="1e-13", max_splits=240):
    """Pure mpmath.iv 1D branch-and-bound rigorous upper bound on sup_{[lo, hi]} f."""
    assert lo < hi
    tol = mp.mpf(tol_str)

    def eval_box(xl, xh):
        xb = iv.mpf([xl, xh])
        xm = (xl + xh) / mp.mpf(2)
        assert xl <= xm <= xh
        xm_iv = iv.mpf(xm)
        fm, _ = f_and_df(xm_iv)
        fb, dfb = f_and_df(xb)
        mv = fm + dfb * (xb - xm_iv)
        return max(mp.mpf(fm.a), mp.mpf(fb.a)), min(mp.mpf(fb.b), mp.mpf(mv.b))

    n_init = 24
    log_lo = mp.log(lo)
    log_hi = mp.log(hi)
    edges = [mp.exp(log_lo + (log_hi - log_lo) * mp.mpf(k) / mp.mpf(n_init)) for k in range(n_init + 1)]
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
        if hv - best_lo <= tol or (xh - xl) <= mp.mpf("1e-24") * max(mp.mpf(1), xh):
            break
        heapq.heappop(heap)
        xm = (xl + xh) / mp.mpf(2)
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


def iv_certify_stage1_5scalar_53(Lam_iv, mults_mp):
    """
    Pure mpmath.iv Stage-1 5-scalar certification of -Ehat_j <= L_all * I_n over ALL (0, inf)
    for ALL real Lam in Lam_iv at p = 5/3 (kappa = 5/4).
    """
    a_iv, b_iv, c_iv, l1_iv = (iv.mpf(x) for x in mults_mp)
    one = iv.mpf(1)
    k_iv = iv.mpf(5) / iv.mpf(4)
    km1_iv = iv.mpf(1) / iv.mpf(4)
    twok_iv = iv.mpf(5) / iv.mpf(2)
    twokm1_iv = iv.mpf(3) / iv.mpf(2)

    assert mp.mpf(l1_iv.a) > mp.mpf(0) and mp.mpf(c_iv.b) < mp.mpf(0)
    alpha_G = one - (b_iv + c_iv) * Lam_iv
    beta_G = one + c_iv * Lam_iv
    assert mp.mpf(beta_G.a) > mp.mpf(0)

    def fM_and_df(tb):
        st = iv.sqrt(tb)
        f = a_iv * tb + b_iv * tb * st + c_iv * tb * tb * st - l1_iv / tb
        df = a_iv + b_iv * twokm1_iv * st + c_iv * twok_iv * tb * st + l1_iv / (tb * tb)
        return f, df

    t_lo = mp.mpf("0.2")
    for _ in range(45):
        tb = iv.mpf([mp.mpf(0), t_lo])
        st = iv.sqrt(tb)
        t2df = l1_iv + a_iv * tb * tb + b_iv * twokm1_iv * tb * tb * st + c_iv * twok_iv * tb * tb * tb * st
        if mp.mpf(t2df.a) > mp.mpf(0):
            break
        t_lo /= mp.mpf(2)
    else:
        raise AssertionError("f_M small-t monotonicity failed!")

    t_hi = mp.mpf("4")
    for _ in range(45):
        u_hi = mp.mpf((one / iv.mpf(t_hi)).b)
        ub = iv.mpf([mp.mpf(0), u_hi])
        su = iv.sqrt(ub)
        sdf = c_iv * twok_iv + b_iv * twokm1_iv * ub + a_iv * ub * su + l1_iv * ub * ub * ub * su
        if mp.mpf(sdf.b) < mp.mpf(0):
            break
        t_hi *= mp.mpf(2)
    else:
        raise AssertionError("f_M large-t monotonicity failed!")
    sup_M_ub = iv_sup_1d(fM_and_df, t_lo, t_hi)

    def fG_and_df(gb):
        g4 = iv.sqrt(iv.sqrt(gb))
        f = alpha_G * g4 - beta_G * gb * g4 - a_iv * gb
        df = alpha_G * km1_iv * g4 / gb - beta_G * k_iv * g4 - a_iv
        return f, df

    g_hi = mp.mpf("4")
    for _ in range(45):
        u_hi = mp.mpf((one / iv.mpf(g_hi)).b)
        ub = iv.mpf([mp.mpf(0), u_hi])
        sdf = -beta_G * k_iv + alpha_G * km1_iv * ub - a_iv * iv.sqrt(iv.sqrt(ub))
        if mp.mpf(sdf.b) < mp.mpf(0):
            break
        g_hi *= mp.mpf(2)
    else:
        raise AssertionError("f_G large-g monotonicity failed!")

    g_lo = mp.mpf("1e-4")
    small_g_ub = None
    if mp.mpf(alpha_G.a) > mp.mpf(0):
        for _ in range(55):
            gb = iv.mpf([mp.mpf(0), g_lo])
            g34 = iv.sqrt(gb) * iv.sqrt(iv.sqrt(gb))
            s_df = alpha_G * km1_iv - beta_G * k_iv * gb - a_iv * g34
            if mp.mpf(s_df.a) > mp.mpf(0):
                small_g_ub = mp.mpf(fG_and_df(iv.mpf(g_lo))[0].b)
                break
            g_lo /= mp.mpf(4)
        assert small_g_ub is not None
    else:
        g_lo = mp.mpf("1e-24")
        gb = iv.mpf([mp.mpf(0), g_lo])
        g4 = iv.sqrt(iv.sqrt(gb))
        small_g_ub = mp.mpf((alpha_G * g4 - beta_G * gb * g4 - a_iv * gb).b)

    core_G_ub = iv_sup_1d(fG_and_df, g_lo, g_hi)
    sup_G_ub = max(mp.mpf(0), small_g_ub, core_G_ub)
    return mp.mpf((iv.mpf(sup_M_ub) + iv.mpf(sup_G_ub) + l1_iv - a_iv).b)


def build_abc_polys_iv(X_cap_iv, U_iv, L_iv):
    """
    Pure mpmath.iv builder for Theorem 1's Degree-3 Exactly-Affine (A, B, C) Lift at p = 5/3:
      Generators:
        0 = A  := D^{1/2} in (0, I]
        1 = Bt := M^{1/2} / sqrt(1 + X_cap) in (c_A A, A]   (c_A = 1/sqrt(1 + X_cap))
        2 = Ct := G^{1/4} / X_cap^{1/4}     in (0, A]
      Ideals:
        g(Lam) = g0 - Lam * g1 = Bt^3 - Lam * (C_cap / B_cap^3) * A Ct A = 0  (DEG 3, EXACTLY AFFINE IN Lam!)
        h1     = (1 + X_cap) A Bt^2 A - A^4 - X_cap Ct^4 = 0                  (DEG 4, CONSTANT!)
        h2     = [Bt, A Ct A] = 0                                             (DEG 4, CONSTANT!)
        h3     = [E, A] = 0                                                   (DEG 6, CONSTANT!)
      18 Constant Hermitian PSD Weights (including Theorem-3 Parameter-Free Degree-3 Kubo-Ando):
        A Bt A - Ct^3 >= 0  (exact parameter-free lift of T_2 <= [Lam x_+/(1+x_+)^2] T_1!)
    """
    one = iv.mpf(1)
    pI = {(): one}
    p0 = {(0,): one}
    p1 = {(1,): one}
    p2 = {(2,): one}
    pIm0 = padd_iv(pI, p0, -1)

    B_cap_iv = iv.sqrt(one + X_cap_iv)
    C_cap_iv = iv.sqrt(iv.sqrt(X_cap_iv))
    cA_iv = one / B_cap_iv

    pObj = {(2, 2, 2, 2, 2): X_cap_iv * C_cap_iv, (0, 0, 2, 0, 0): -C_cap_iv}
    g0 = {(1, 1, 1): one}
    g1 = {(0, 2, 0): C_cap_iv / (B_cap_iv * B_cap_iv * B_cap_iv)}
    h1 = {(0, 1, 1, 0): one + X_cap_iv, (0, 0, 0, 0): -one, (2, 2, 2, 2): -X_cap_iv}
    pACA = {(0, 2, 0): one}
    h2 = padd_iv(pmul_iv(p1, pACA), pmul_iv(pACA, p1), -1)
    h3 = padd_iv(pmul_iv(pObj, p0), pmul_iv(p0, pObj), -1)

    pUmE = padd_iv({(0, 0, 0, 0, 0): U_iv}, pObj, -1)
    pLpE = padd_iv({(0, 0, 0, 0, 0): L_iv}, pObj, 1)
    pKA = {(0, 1, 0): one, (2, 2, 2): -one}
    half = one / iv.mpf(2)

    def sym_prod_iv(pa, pb):
        ab = padd_iv(pmul_iv(pa, pb), pmul_iv(pb, pa), one)
        return {w: half * c for w, c in ab.items()}

    weights = [
        pI,
        p0,
        pIm0,
        pmul_iv(p0, pIm0),
        p1,
        padd_iv(p0, p1, -1),
        padd_iv(p1, {(0,): cA_iv}, -1),
        pmul_iv(p1, padd_iv(pI, p1, -1)),
        p2,
        padd_iv(p0, p2, -1),
        pmul_iv(p2, padd_iv(pI, p2, -1)),
        pUmE,
        pLpE,
        sym_prod_iv(p0, pUmE),
        sym_prod_iv(p0, pLpE),
        sym_prod_iv(pIm0, pUmE),
        sym_prod_iv(pIm0, pLpE),
        pKA,
    ]
    for pw in weights:
        for w_k, c_k in pw.items():
            w_rev = w_k[::-1]
            assert w_rev in pw and mp.mpf(pw[w_rev].a) == mp.mpf(c_k.a) and mp.mpf(pw[w_rev].b) == mp.mpf(c_k.b), (
                f"Weight not syntactically self-adjoint at word {w_k}!"
            )
    return pObj, g0, g1, [h1, h2, h3], weights


def build_abc_struct_iv(mode):
    """Pure symbolic closed-basis NC-SOS structure for (A, B, C) at p = 5/3."""
    b3 = reduced_words_iv(3, 3)
    if mode == "deg6":
        wlist0 = b3
        max_id_len = 3
    elif mode == "deg8C":
        d4 = [w for w in reduced_words_iv(3, 4) if len(w) == 4 and w.count(1) == 0]
        wlist0 = sorted(set(b3 + d4), key=lambda w: (len(w), w))
        max_id_len = 5
    elif mode == "8C5C":
        d4 = [w for w in reduced_words_iv(3, 4) if len(w) == 4 and w.count(1) == 0]
        d5 = [w for w in reduced_words_iv(3, 5) if len(w) == 5 and w.count(1) == 0]
        wlist0 = sorted(set(b3 + d4 + d5), key=lambda w: (len(w), w))
        max_id_len = 5
    else:
        raise ValueError(f"Unknown mode: {mode}")

    _, g0_s, g1_s, h_s, w_s = build_abc_polys_iv(iv.mpf(2), iv.mpf(1), iv.mpf(1))
    w_supp = [list(pw.keys()) for pw in w_s]
    id_supp = [list(set(g0_s.keys()) | set(g1_s.keys()))] + [list(ph.keys()) for ph in h_s]

    canon = sorted(set(canon_w_iv(u[::-1] + v) for u in wlist0 for v in wlist0), key=lambda w: (len(w), w))
    w2i = {w: i for i, w in enumerate(canon)}
    n_var = len(canon)
    canon_set = set(canon)

    word_pairs = [[] for _ in range(n_var)]
    for ri, wu in enumerate(wlist0):
        wur = wu[::-1]
        for ci, wv in enumerate(wlist0):
            word_pairs[w2i[canon_w_iv(wur + wv)]].append((ri, ci))
    for idx in range(n_var):
        assert len(word_pairs[idx]) > 0

    blocks_wlists = [wlist0]
    for a in range(1, len(w_supp)):
        supp = w_supp[a]
        cand = [u for u in wlist0 if all(canon_w_iv(u[::-1] + k + u) in canon_set for k in supp)]
        kept = []
        for u in cand:
            if all(
                canon_w_iv(u[::-1] + k + v) in canon_set and canon_w_iv(v[::-1] + k + u) in canon_set
                for v in kept for k in supp
            ):
                kept.append(u)
        blocks_wlists.append(kept)

    all_short = gen_words_iv(3, max_id_len)
    id_meta = []
    for gi, supp in enumerate(id_supp):
        for wl in all_short:
            for wr in all_short:
                if len(wl) + len(wr) > max_id_len:
                    continue
                if all(canon_w_iv(wl + k + wr) in canon_set for k in supp):
                    id_meta.append((gi, wl, wr))

    return {
        "mode": mode,
        "canon": canon,
        "w2i": w2i,
        "n_var": n_var,
        "blocks_wlists": blocks_wlists,
        "word_pairs": word_pairs,
        "id_meta": id_meta,
    }


def iv_certify_abc_interval(m, Lam0_mp, Lam1_mp, struct, mults_mp, bundle):
    """
    100% PURE ZERO-FLOAT mpmath.iv VERIFIER FOR THEOREM 2:
    Zero-Discrepancy Exactly-Affine Shared-Multiplier Convex-Combination Proof
    on [Lam0_mp, Lam1_mp] in (A, B, C) at p = 5/3 (kappa = 5/4).
    """
    assert Lam0_mp < Lam1_mp
    Lam_box = iv.mpf([Lam0_mp, Lam1_mp])
    xp0_iv, sigp0_iv = iv_certify_xplus_53(Lam0_mp)
    xp1_iv, _ = iv_certify_xplus_53(Lam1_mp)
    assert mp.mpf(xp0_iv.a) > mp.mpf(1)
    X_cap_iv = iv.mpf(mp.mpf(xp1_iv.b))
    target_lo = mp.mpf((sigp0_iv / iv.mpf(m - 1)).a)

    L_box_mp = iv_certify_stage1_5scalar_53(Lam_box, mults_mp)
    L_box_iv = iv.mpf(L_box_mp)
    U_box_iv = iv.mpf(m - 1) * L_box_iv

    pObj_iv, g0_iv, g1_iv, h_list_iv, weights_iv = build_abc_polys_iv(X_cap_iv, U_box_iv, L_box_iv)
    Lam0_iv = iv.mpf(Lam0_mp)
    Lam1_iv = iv.mpf(Lam1_mp)

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
        Obj_vec[w2i[canon_w_iv(k)]] = Obj_vec[w2i[canon_w_iv(k)]] + v

    Z0_0_mp, fac_0_mp, lam_0_mp, Z0_1_mp, fac_1_mp, lam_1_mp = bundle
    for idx_e, (g_idx, _, _) in enumerate(id_meta):
        if g_idx == 0:
            assert lam_0_mp[idx_e] == lam_1_mp[idx_e], "g-multiplier MUST be identical across [Lam0, Lam1]!"

    def assemble_ep(Z0_mp, fac_mp, lam_mp, Lam_ep_iv):
        pg_iv = padd_iv(g0_iv, g1_iv, -Lam_ep_iv)
        all_ideals = [pg_iv] + h_list_iv
        for i in range(sz0):
            for j in range(i + 1, sz0):
                assert Z0_mp[i][j] == Z0_mp[j][i], "Initial Z0 asymmetric!"
        Z0_iv = [[iv.mpf(Z0_mp[i][j]) for j in range(sz0)] for i in range(sz0)]
        lam_iv = [iv.mpf(x) for x in lam_mp]
        rhs_iv = [iv.mpf(0) for _ in range(n_var)]

        for idx_e, (g_idx, wl, wr) in enumerate(id_meta):
            c = lam_iv[idx_e]
            if mp.mpf(c.a) == mp.mpf(0) and mp.mpf(c.b) == mp.mpf(0):
                continue
            for k, v in all_ideals[g_idx].items():
                ii = w2i[canon_w_iv(wl + k + wr)]
                rhs_iv[ii] = rhs_iv[ii] + c * v

        for a in range(1, len(blocks_wlists)):
            wlist = blocks_wlists[a]
            sz = len(wlist)
            pW = weights_iv[a]
            Ga = [[iv.mpf(0) for _ in range(sz)] for _ in range(sz)]
            for lam_r_mp, vec_r_mp in fac_mp[a]:
                assert lam_r_mp > mp.mpf(0)
                lr = iv.mpf(lam_r_mp)
                vr = [iv.mpf(x) for x in vec_r_mp]
                for i in range(sz):
                    lv = lr * vr[i]
                    for j in range(i, sz):
                        val = lv * vr[j]
                        Ga[i][j] = Ga[i][j] + val
                        if i != j:
                            Ga[j][i] = Ga[j][i] + val
            for ri, wu in enumerate(wlist):
                wur = wu[::-1]
                for ci, wv in enumerate(wlist):
                    g_rc = Ga[ri][ci]
                    if mp.mpf(g_rc.a) == mp.mpf(0) and mp.mpf(g_rc.b) == mp.mpf(0):
                        continue
                    for k, v in pW.items():
                        ii = w2i[canon_w_iv(wur + k + wv)]
                        rhs_iv[ii] = rhs_iv[ii] + g_rc * v

        wlist0 = blocks_wlists[0]
        for ri, wu in enumerate(wlist0):
            wur = wu[::-1]
            for ci, wv in enumerate(wlist0):
                ii = w2i[canon_w_iv(wur + wv)]
                rhs_iv[ii] = rhs_iv[ii] + Z0_iv[ri][ci]

        max_res_hi = mp.mpf(0)
        for idx in range(n_var):
            if idx == idx_const:
                continue
            diff = Obj_vec[idx] - rhs_iv[idx]
            ad = max(abs(mp.mpf(diff.a)), abs(mp.mpf(diff.b)))
            if ad > max_res_hi:
                max_res_hi = ad
            pairs = word_pairs[idx]
            share = diff / iv.mpf(len(pairs))
            for ri, ci in pairs:
                Z0_iv[ri][ci] = Z0_iv[ri][ci] + share

        for i in range(sz0):
            for j in range(i + 1, sz0):
                assert Z0_iv[i][j] == Z0_iv[j][i], "Asymmetry after residual absorption!"

        return Z0_iv, mp.mpf((rhs_iv[idx_const] - Obj_vec[idx_const]).b), max_res_hi

    Z0_0_iv, Psi0_hi, res0_hi = assemble_ep(Z0_0_mp, fac_0_mp, lam_0_mp, Lam0_iv)
    Z0_1_iv, Psi1_hi, res1_hi = assemble_ep(Z0_1_mp, fac_1_mp, lam_1_mp, Lam1_iv)

    ok0, d0 = iv_cholesky_pd(Z0_0_iv)
    if not ok0:
        return False, "Z0_0 Cholesky fail"
    ok1, d1 = iv_cholesky_pd(Z0_1_iv)
    if not ok1:
        return False, "Z0_1 Cholesky fail"

    Psi_ub = max(Psi0_hi, Psi1_hi)
    min_d = min(d0, d1)
    max_res = max(res0_hi, res1_hi)
    margin = mp.mpf((iv.mpf(target_lo) - iv.mpf(Psi_ub)).a)
    if not (Psi_ub < target_lo and margin > mp.mpf(0)):
        return False, "Margin fail"
    return True, (Psi_ub, target_lo, margin, min_d, max_res)


def iv_certify_stage1_tail_box_53(m, Lam0_mp, Lam1_mp, mults_mp):
    """Pure mpmath.iv Stage-1 tail certification on [Lam0_mp, Lam1_mp] at p = 5/3."""
    assert Lam0_mp < Lam1_mp
    _, sigp0_iv = iv_certify_xplus_53(Lam0_mp)
    target_lo = mp.mpf((sigp0_iv / iv.mpf(m - 1)).a)
    L_box_mp = iv_certify_stage1_5scalar_53(iv.mpf([Lam0_mp, Lam1_mp]), mults_mp)
    margin = mp.mpf((iv.mpf(target_lo) - iv.mpf(L_box_mp)).a)
    if L_box_mp < target_lo and margin > mp.mpf(0):
        return True, (L_box_mp, target_lo, margin)
    return False, None


def iv_verify_p53_record_summary(m, Lam_cert_mp, covered_boxes):
    """
    Pure mpmath.iv contiguity + Hadamard right-endpoint verification and strict
    outward-rounded enclosure table computations for C_{5/3}(m).
    """
    # Exact Hadamard interpolation upper bound at p = 5/3 (kappa = 5/4):
    # Lam_interp(5/3, m) = 2^{2k - 2} * (1 + sqrt(m)) = sqrt(2) * (1 + sqrt(m))
    Lam_interp_iv = iv.sqrt(iv.mpf(2)) * (iv.mpf(1) + iv.sqrt(iv.mpf(m)))
    Lam_interp_ub = mp.mpf(Lam_interp_iv.b)

    assert len(covered_boxes) > 0
    assert covered_boxes[0][0] == Lam_cert_mp
    for idx in range(len(covered_boxes) - 1):
        assert covered_boxes[idx][1] == covered_boxes[idx + 1][0], "Gap in Lambda coverage!"
    Lam_end_mp = covered_boxes[-1][1]
    assert Lam_end_mp > Lam_interp_ub, "Coverage does not strictly exceed Lam_interp!"

    # Convert Lam_cert to C_{5/3}(m) <= (Lam_cert / 2^{3/2})^{2/5}
    two_iv = iv.mpf(2)
    two_32_iv = two_iv * iv.sqrt(two_iv)
    C_ub_iv = iv.exp((iv.log(iv.mpf(Lam_cert_mp)) - iv.log(two_32_iv)) * (iv.mpf(2) / iv.mpf(5)))
    C_ub_hi = mp.mpf(C_ub_iv.b)
    C_ub_str12 = ceil_fixed_str(C_ub_hi, 12)
    assert mp.mpf(iv.mpf(C_ub_str12).a) >= C_ub_hi

    C_lb_iv = iv.mpf(PRIOR_CERT_LB_STR[m])
    C_139_iv = iv.mpf(PRIOR_139_UB_STR[m])
    C_v6_iv = iv.exp((iv.log(iv.mpf(PRIOR_V6_LAM_STR[m])) - iv.log(two_32_iv)) * (iv.mpf(2) / iv.mpf(5)))

    # Displayed-column strict outward gap & gains:
    new_gap_iv = iv.mpf(C_ub_str12) - C_lb_iv
    new_gap_hi = mp.mpf(new_gap_iv.b)
    new_gap_str = ceil_sci_str(new_gap_hi, 3)
    assert mp.mpf(iv.mpf(new_gap_str).a) >= new_gap_hi
    assert mp.mpf((iv.mpf(C_ub_str12) - C_lb_iv).b) <= mp.mpf(iv.mpf(new_gap_str).a)

    old139_gap_iv = C_139_iv - C_lb_iv
    old139_gap_lo = mp.mpf(old139_gap_iv.a)
    old139_gap_hi = mp.mpf(old139_gap_iv.b)
    old139_gap_str = ceil_sci_str(old139_gap_hi, 3)

    gain_139_iv = iv.mpf(old139_gap_lo) / iv.mpf(new_gap_str)
    gain_139_lo = mp.mpf(gain_139_iv.a)
    gain_139_str = floor_fixed_str(gain_139_lo, 2)
    assert mp.mpf(iv.mpf(gain_139_str).b) <= gain_139_lo

    oldv6_gap_lo = mp.mpf((C_v6_iv - C_lb_iv).a)
    gain_v6_lo = mp.mpf((iv.mpf(oldv6_gap_lo) / iv.mpf(new_gap_str)).a)
    gain_v6_str = floor_fixed_str(gain_v6_lo, 2)
    assert mp.mpf(iv.mpf(gain_v6_str).b) <= gain_v6_lo

    return {
        "m": m,
        "Lam_cert_mp": Lam_cert_mp,
        "Lam_end_mp": Lam_end_mp,
        "Lam_interp_ub_str": ceil_fixed_str(Lam_interp_ub, 6),
        "C_lb_str": PRIOR_CERT_LB_STR[m],
        "C_ub_str12": C_ub_str12,
        "C_139_str": PRIOR_139_UB_STR[m],
        "new_gap_hi": new_gap_hi,
        "new_gap_str": new_gap_str,
        "old139_gap_str": old139_gap_str,
        "gain_139_str": gain_139_str,
        "gain_v6_str": gain_v6_str,
    }


SECTION_B_FUNCS = [
    "ceil_fixed_str",
    "floor_fixed_str",
    "ceil_sci_str",
    "floor_sci_str",
    "canon_w_iv",
    "reduced_words_iv",
    "gen_words_iv",
    "pmul_iv",
    "padd_iv",
    "iv_cholesky_pd",
    "iv_certify_xplus_53",
    "iv_sup_1d",
    "iv_certify_stage1_5scalar_53",
    "build_abc_polys_iv",
    "build_abc_struct_iv",
    "iv_certify_abc_interval",
    "iv_certify_stage1_tail_box_53",
    "iv_verify_p53_record_summary",
    "run_section_b_ast_audit",
]


def run_section_b_ast_audit():
    """Module 0: Pure AST Zero-Float Audit across ALL Section-B certification functions."""
    src = Path(__file__).read_text(encoding="utf-8")
    tree = ast.parse(src)
    fn_map = {}
    for node in tree.body:
        if isinstance(node, ast.FunctionDef):
            fn_map[node.name] = node

    banned_names = {"np", "numpy", "scipy", "math", "sympy", "eigh", "linprog", "root", "least_squares", "minimize"}
    total_nodes = 0
    for fn_name in SECTION_B_FUNCS:
        assert fn_name in fn_map, f"Missing Section-B function: {fn_name}"
        fn_node = fn_map[fn_name]
        for sub in ast.walk(fn_node):
            total_nodes += 1
            if isinstance(sub, ast.Constant) and type(sub.value).__name__ in ("float", "complex"):
                raise AssertionError(f"Float/complex literal {sub.value!r} in Section-B {fn_name}!")
            if isinstance(sub, ast.Name) and (sub.id in banned_names or sub.id in ("float", "complex")):
                raise AssertionError(f"Banned symbol {sub.id!r} in Section-B {fn_name}!")
            if isinstance(sub, ast.Attribute) and sub.attr in banned_names:
                raise AssertionError(f"Banned attribute {sub.attr!r} in Section-B {fn_name}!")

    # Self-test strict outward formatters on exact boundary rational fractions
    t_val = mp.mpf(1) / mp.mpf(3)
    assert ceil_fixed_str(t_val, 6) == "0.333334"
    assert floor_fixed_str(t_val, 6) == "0.333333"
    assert ceil_sci_str(t_val, 3) == "3.34e-01"
    assert floor_sci_str(t_val, 3) == "3.33e-01"
    return len(SECTION_B_FUNCS), total_nodes


# ==============================================================================
# SECTION A: UNTRUSTED FLOAT64 ORACLES & DIAGNOSTIC SUITES
# (NEVER trusted by Section B! Every Section-B certificate is re-verified from
#  scratch in pure zero-float 50-digit mpmath.iv!)
# ==============================================================================

import numpy as np
from scipy.linalg import eigh
from scipy.optimize import least_squares, linprog, minimize, root


def _o_matpow(M, p):
    ev, V = eigh(0.5 * (M + M.T))
    return (V * (np.maximum(ev, 1e-30) ** p)) @ V.T


def _o_matpow_herm(M, p):
    ev, V = eigh(0.5 * (M + M.conj().T))
    return (V * (np.maximum(ev, 1e-30) ** p)) @ V.conj().T


def _o_roots_kappa(Lam, kappa):
    def f(x):
        return (1.0 + x) ** (2.0 * kappa - 1.0) - Lam * (x ** (kappa - 1.0))

    def fp(x):
        return (2.0 * kappa - 1.0) * ((1.0 + x) ** (2.0 * kappa - 2.0)) - Lam * (kappa - 1.0) * (x ** (kappa - 2.0))

    xp = 2.0
    while f(xp) < 0.0:
        xp *= 2.0
    for _ in range(80):
        xp -= f(xp) / fp(xp)
    xm = 0.001
    for _ in range(80):
        st = f(xm) / fp(xm)
        while xm - st <= 0.0:
            st *= 0.5
        xm -= st
    sp = (xp ** (kappa - 1.0)) * (xp - 1.0)
    return xm, xp, sp


def oracle_stage1_lp_multipliers_53(Lam_lo_mp, Lam_hi_mp):
    """Untrusted float64 HiGHS LP oracle producing candidate 5-scalar multipliers for Section B."""
    Lam_lo = float(Lam_lo_mp)
    Lam_hi = float(Lam_hi_mp)
    kappa = 1.25
    ts = np.unique(np.concatenate([
        np.geomspace(1e-2, 0.99, 250),
        np.linspace(1.0, 3.5, 500),
        np.geomspace(3.5, 20.0, 250),
    ]))
    gs = np.unique(np.concatenate([
        np.geomspace(1e-6, 2.5, 800),
        np.geomspace(2.5, 20.0, 250),
    ]))
    A1 = np.column_stack([ts, ts ** (2 * kappa - 1), ts ** (2 * kappa), -1.0 / ts, -np.ones_like(ts), np.zeros_like(ts)])
    b1 = np.zeros(len(ts))
    gkm1 = gs ** (kappa - 1)
    gk = gs ** kappa
    A2_lo = np.column_stack([-gs, -Lam_lo * gkm1, -Lam_lo * (gkm1 + gk), np.zeros_like(gs), np.zeros_like(gs), -np.ones_like(gs)])
    A2_hi = np.column_stack([-gs, -Lam_hi * gkm1, -Lam_hi * (gkm1 + gk), np.zeros_like(gs), np.zeros_like(gs), -np.ones_like(gs)])
    b2 = gk - gkm1
    A2 = np.vstack([A2_lo, A2_hi, np.array([0.0, 0.0, 0.0, 0.0, 0.0, -1.0])])
    b2_all = np.concatenate([b2, b2, [0.0]])
    c_obj = np.array([-1.0, 0.0, 0.0, 1.0, 1.0, 1.0])
    c_min = -1.0 / Lam_hi + max(1e-6, 1e-4 / Lam_hi)
    bounds = [(None, None), (None, None), (c_min, -1e-9), (1e-9, None), (None, None), (None, None)]
    res = linprog(c_obj, A_ub=np.vstack([A1, A2]), b_ub=np.concatenate([b1, b2_all]), bounds=bounds, method="highs")
    assert res.success, "Stage-1 LP oracle failed!"
    return tuple(mp.mpf(f"{float(v):.17g}") for v in res.x[:4])


def _o_poly_iv_to_f64(p_iv):
    return {k: float(mp.mpf(v.mid)) for k, v in p_iv.items()}


def oracle_solve_abc_interval_2ep(struct, m, Lam0_mp, Lam1_mp, mults_mp, eps_I_f=1e-8, max_iter=58):
    """
    Untrusted float64 oracle for Theorem 2's Exactly-Affine Shared-Multiplier 2-Endpoint SDP:
      - Balanced split-normalization (y0[()]=0.5, y1[()]=0.5)
      - Exact all-block facial reduction (ev > 1e-11 * ev[-1] eliminates BOTH g*v=0 and h1*v=0!)
      - In-Loop X-Metric Dual Projection (dX_a = X_a (sum al_k B_{a,k}) X_a), crushing dual
        residuals from 1e-4 down to 1e-11 and preserving strict positive definiteness!
      - Packs every matrix entry and multiplier into exact decimal mp.mpf strings for Section B.
    """
    Lam_box = iv.mpf([Lam0_mp, Lam1_mp])
    _, sigp0_iv = iv_certify_xplus_53(Lam0_mp)
    xp1_iv, _ = iv_certify_xplus_53(Lam1_mp)
    target_f = float(mp.mpf((sigp0_iv / iv.mpf(m - 1)).a))
    X_cap_iv = iv.mpf(mp.mpf(xp1_iv.b))
    L_box_mp = iv_certify_stage1_5scalar_53(Lam_box, mults_mp)
    L_box_iv = iv.mpf(L_box_mp)
    U_box_iv = iv.mpf(m - 1) * L_box_iv

    pObj_iv, g0_iv, g1_iv, h_list_iv, weights_iv = build_abc_polys_iv(X_cap_iv, U_box_iv, L_box_iv)
    pObj_f = _o_poly_iv_to_f64(pObj_iv)
    g0_f = _o_poly_iv_to_f64(g0_iv)
    g1_f = _o_poly_iv_to_f64(g1_iv)
    h_list_f = [_o_poly_iv_to_f64(ph) for ph in h_list_iv]
    weights_f = [_o_poly_iv_to_f64(pw) for pw in weights_iv]

    n_var = struct["n_var"]
    w2i = struct["w2i"]
    blocks_wlists = struct["blocks_wlists"]
    word_pairs = struct["word_pairs"]
    id_meta = struct["id_meta"]
    idx0 = w2i[()]
    sz0 = len(blocks_wlists[0])
    nb1 = len(blocks_wlists)

    raw_blocks = []
    for idx_b, wlist in enumerate(blocks_wlists):
        pW = weights_f[idx_b]
        sz = len(wlist)
        F_t = np.zeros((n_var, sz, sz))
        for ri, wu in enumerate(wlist):
            wur = wu[::-1]
            for ci, wv in enumerate(wlist):
                for k, v in pW.items():
                    F_t[w2i[canon_w_iv(wur + k + wv)], ri, ci] += v
        F_t = 0.5 * (F_t + np.swapaxes(F_t, 1, 2))
        raw_blocks.append((sz, F_t))
    raw_flats = [F_t.reshape(n_var, -1) for _, F_t in raw_blocks]

    def build_A_split(Lam_f):
        pg_f = dict(g0_f)
        for k, v in g1_f.items():
            pg_f[k] = pg_f.get(k, 0.0) - Lam_f * v
        all_id = [pg_f] + h_list_f
        rows_g, rows_h = [], []
        for g_idx, wl, wr in id_meta:
            pg = all_id[g_idx]
            row = np.zeros(n_var)
            for k, v in pg.items():
                row[w2i[canon_w_iv(wl + k + wr)]] += v
            if g_idx == 0:
                rows_g.append(row)
            else:
                rows_h.append(row)
        return np.array(rows_g), np.array(rows_h)

    Ag0, Ah = build_A_split(float(Lam0_mp))
    Ag1, _ = build_A_split(float(Lam1_mp))
    n_g = Ag0.shape[0]
    n_h = Ah.shape[0]
    Zh = np.zeros((n_h, n_var))
    A_id_joint = np.vstack([np.hstack([Ag0, Ag1]), np.hstack([Ah, Zh]), np.hstack([Zh, Ah])])

    a0 = np.zeros(n_var)
    a0[idx0] = 1.0
    a0_j = np.concatenate([a0, np.zeros(n_var)])
    a1_j = np.concatenate([np.zeros(n_var), a0])
    A_eq = np.vstack([a0_j[None, :], a1_j[None, :], A_id_joint])
    b_eq = np.zeros(A_eq.shape[0])
    b_eq[0] = 0.5
    b_eq[1] = 0.5

    rn = np.linalg.norm(A_eq, axis=1)
    keep = rn > 1e-14
    A_n = A_eq[keep] / rn[keep, None]
    b_n = b_eq[keep] / rn[keep]
    U_eq, s_eq, Vt_eq = np.linalg.svd(A_n, full_matrices=True)
    rk_eq = int(np.sum(s_eq > 1e-11 * s_eq[0]))
    y_part = Vt_eq[:rk_eq].T @ ((U_eq[:, :rk_eq].T @ b_n) / s_eq[:rk_eq])
    N_null = Vt_eq[rk_eq:].T
    n_free = N_null.shape[1]

    c_orig = np.zeros(n_var)
    for k, v in pObj_f.items():
        c_orig[w2i[canon_w_iv(k)]] += v
    c_1 = c_orig - eps_I_f * np.einsum("kii->k", raw_blocks[0][1])
    c_joint = np.concatenate([c_1, c_1])

    blocks = []
    for ep in range(2):
        y_ep = y_part[ep * n_var : (ep + 1) * n_var]
        N_ep = N_null[ep * n_var : (ep + 1) * n_var, :]
        for idx_b, (sz, F_t) in enumerate(raw_blocks):
            if sz == 0:
                continue
            B0 = (y_ep @ raw_flats[idx_b]).reshape(sz, sz)
            Bz = (N_ep.T @ raw_flats[idx_b]).reshape(n_free, sz, sz)
            G_str = 0.5 * ((B0 @ B0 + Bz.reshape(-1, sz).T @ Bz.reshape(-1, sz)) + (B0 @ B0 + Bz.reshape(-1, sz).T @ Bz.reshape(-1, sz)).T)
            ev, V = np.linalg.eigh(G_str)
            if len(ev) == 0 or ev[-1] <= 1e-20:
                continue
            Qa = V[:, ev > 1e-11 * ev[-1]]
            rb = Qa.shape[1]
            if rb == 0:
                continue
            B0_r = 0.5 * (Qa.T @ B0 @ Qa + (Qa.T @ B0 @ Qa).T)
            Bz_r = (Qa.T @ Bz) @ Qa
            Bz_r = 0.5 * (Bz_r + np.swapaxes(Bz_r, 1, 2))
            Bzf_r = Bz_r.reshape(n_free, rb * rb)
            sc = max(float(np.linalg.norm(B0_r)), float(np.max(np.linalg.norm(Bzf_r, axis=1))), 1e-12)
            blocks.append((ep, idx_b, rb, Qa, B0_r / sc, Bz_r / sc, Bzf_r / sc, sc))

    # Dual witness extraction: Obj + Psi*a0 = SOS(Z) + A_id^T lam  <=>  A_id^T lam - Psi*a0 = Obj - SOS(Z)
    M_ls = np.hstack([A_id_joint.T, -a0_j[:, None], -a1_j[:, None]])
    cn = np.linalg.norm(M_ls, axis=0)
    cn[cn < 1e-15] = 1.0
    U_ls, s_ls, Vt_ls = np.linalg.svd(M_ls / cn[None, :], full_matrices=False)
    rk_ls = int(np.sum(s_ls > 1e-12 * s_ls[0]))
    pinv_ls = (Vt_ls[:rk_ls].T / s_ls[:rk_ls]) @ U_ls[:, :rk_ls].T

    gv = N_null.T @ c_joint
    tot_n = sum(b[2] for b in blocks)

    def project_dual(Xl, steps=2):
        Xc = [X.copy() for X in Xl]
        for _ in range(steps):
            rd = gv.copy()
            for a, (_, _, rb, _, _, _, Bzf, _) in enumerate(blocks):
                rd -= Bzf @ Xc[a].ravel()
            if float(np.linalg.norm(rd)) < 1e-12:
                break
            G = np.zeros((n_free, n_free))
            for a, (_, _, rb, _, _, Bz, Bzf, _) in enumerate(blocks):
                XBX = (Xc[a] @ Bz) @ Xc[a]
                G += Bzf @ XBX.reshape(n_free, rb * rb).T
            G = 0.5 * (G + G.T)
            dd = np.sqrt(np.maximum(np.diag(G), 1e-30))
            Gn = (G / dd[:, None]) / dd[None, :] + 1e-13 * np.eye(n_free)
            try:
                al = np.linalg.solve(Gn, rd / dd) / dd
            except np.linalg.LinAlgError:
                al = np.linalg.lstsq(Gn, rd / dd, rcond=1e-13)[0] / dd
            dXl = []
            lm_min = 0.0
            for a, (_, _, rb, _, _, Bz, Bzf, _) in enumerate(blocks):
                M = (al @ Bzf).reshape(rb, rb)
                dX = 0.5 * (Xc[a] @ M @ Xc[a] + (Xc[a] @ M @ Xc[a]).T)
                dXl.append(dX)
                ev, V = np.linalg.eigh(Xc[a])
                Li = V / np.sqrt(np.maximum(ev, 1e-30))
                lm_min = min(lm_min, float(np.linalg.eigvalsh(0.5 * (Li.T @ dX @ Li + (Li.T @ dX @ Li).T))[0]))
            if lm_min < -0.95:
                return None
            for a in range(len(blocks)):
                Xc[a] = 0.5 * ((Xc[a] + dXl[a]) + (Xc[a] + dXl[a]).T)
        return Xc

    def eval_w(Xl):
        Z_ep = [[np.zeros((sz, sz)) for sz, _ in raw_blocks] for _ in range(2)]
        for a, (ep, idx_b, _, Qa, _, _, _, sc) in enumerate(blocks):
            Zm = Qa @ (Xl[a] / sc) @ Qa.T
            Z_ep[ep][idx_b] = 0.5 * (Zm + Zm.T)
        Z_ep[0][0] += eps_I_f * np.eye(sz0)
        Z_ep[1][0] += eps_I_f * np.eye(sz0)
        psos0 = sum(raw_flats[b] @ Z_ep[0][b].ravel() for b in range(nb1) if raw_blocks[b][0] > 0)
        psos1 = sum(raw_flats[b] @ Z_ep[1][b].ravel() for b in range(nb1) if raw_blocks[b][0] > 0)
        rhs = np.concatenate([c_orig - psos0, c_orig - psos1])
        sol = (pinv_ls @ rhs) / cn
        res = rhs - M_ls @ sol
        mev = 1e9
        Psis = []
        for ep in range(2):
            rv = res[ep * n_var : (ep + 1) * n_var]
            Z0_chk = Z_ep[ep][0].copy()
            for idx in range(n_var):
                if idx == idx0:
                    continue
                dv = rv[idx]
                if abs(dv) < 1e-16:
                    continue
                pairs = word_pairs[idx]
                sh = dv / len(pairs)
                for ri, ci in pairs:
                    Z0_chk[ri, ci] += sh
            Z0_chk = 0.5 * (Z0_chk + Z0_chk.T)
            mev = min(mev, float(np.linalg.eigvalsh(Z0_chk)[0]))
            Psis.append(float(sol[-2 + ep]) - float(rv[idx0]))
        return max(Psis), mev, Z_ep, sol

    z = np.zeros(n_free)
    Sl = [np.eye(b[2]) for b in blocks]
    Xl = [np.eye(b[2]) for b in blocks]

    def mstep(Ml, dMl):
        am = 1.0
        for M, dM in zip(Ml, dMl):
            ev, V = np.linalg.eigh(M)
            Li = V * (1.0 / np.sqrt(np.maximum(ev, 1e-30)))
            G = 0.5 * (Li.T @ dM @ Li + (Li.T @ dM @ Li).T)
            lm = float(np.linalg.eigvalsh(G)[0])
            if lm < -1e-16:
                am = min(am, -1.0 / lm)
        return am

    best = None
    fallback = None
    for it in range(1, max_iter + 1):
        Rpl = []
        rd = gv.copy()
        mu = 0.0
        for a, (_, _, rb, _, B0, _, Bzf, _) in enumerate(blocks):
            Rp = 0.5 * ((Sl[a] - (B0 + (z @ Bzf).reshape(rb, rb))) + (Sl[a] - (B0 + (z @ Bzf).reshape(rb, rb))).T)
            Rpl.append(Rp)
            rd -= Bzf @ Xl[a].ravel()
            mu += float(np.sum(Sl[a] * Xl[a]))
        mu /= tot_n
        dres = float(np.linalg.norm(rd))
        if it >= 16 and dres > 1e-7:
            Xp = project_dual(Xl, steps=1)
            if Xp is not None:
                Xl = Xp
                rd = gv.copy()
                mu = 0.0
                for a, (_, _, _, _, _, _, Bzf, _) in enumerate(blocks):
                    rd -= Bzf @ Xl[a].ravel()
                    mu += float(np.sum(Sl[a] * Xl[a]))
                mu /= tot_n
                dres = float(np.linalg.norm(rd))
        if mu < 1e-5 and it >= 18:
            Xp = project_dual(Xl, steps=2) if dres > 1e-11 else Xl
            if Xp is not None:
                Pm, mev, Z_ep_c, sol_c = eval_w(Xp)
                if mev > 0.1 * eps_I_f and (best is None or Pm < best[0]):
                    best = (Pm, mev, Z_ep_c, sol_c)
                if fallback is None or (mev > 0.0 and Pm < fallback[0]):
                    fallback = (Pm, mev, Z_ep_c, sol_c)
                if best is not None and best[0] < target_f and mu < 4e-10:
                    break
        Ms = np.zeros((n_free, n_free))
        Sinvl = []
        for a, (_, _, rb, _, _, Bz, _, _) in enumerate(blocks):
            ev, V = np.linalg.eigh(Sl[a])
            Si = (V * (1.0 / np.maximum(ev, 1e-30))) @ V.T
            Sinvl.append(Si)
            Ms += (Si @ Bz).reshape(n_free, rb * rb) @ (Bz @ Xl[a]).reshape(n_free, rb * rb).T
        Ms = 0.5 * (Ms + Ms.T)
        dd = np.sqrt(np.maximum(np.diag(Ms), 1e-30))
        Mn = (Ms / dd[:, None]) / dd[None, :] + 1e-14 * np.eye(n_free)

        def sM(rhs):
            try:
                return np.linalg.solve(Mn, rhs / dd) / dd
            except np.linalg.LinAlgError:
                return np.linalg.lstsq(Mn, rhs / dd, rcond=1e-14)[0] / dd

        def sdir(sv, dSa=None, dXa=None):
            rhs = -rd.copy()
            Rcl = []
            for a, (_, _, rb, _, _, _, Bzf, _) in enumerate(blocks):
                Rc = sv * mu * np.eye(rb) - Sl[a] @ Xl[a]
                if dSa is not None:
                    Rc = Rc - dSa[a] @ dXa[a]
                Rcl.append(Rc)
                W = 0.5 * ((Sinvl[a] @ (Rc + Rpl[a] @ Xl[a])) + (Sinvl[a] @ (Rc + Rpl[a] @ Xl[a])).T)
                rhs += Bzf @ W.ravel()
            dz = sM(rhs)
            dSl, dXl = [], []
            for a, (_, _, rb, _, _, _, Bzf, _) in enumerate(blocks):
                dS = 0.5 * (((dz @ Bzf).reshape(rb, rb) - Rpl[a]) + ((dz @ Bzf).reshape(rb, rb) - Rpl[a]).T)
                dX = 0.5 * ((Sinvl[a] @ (Rcl[a] - dS @ Xl[a])) + (Sinvl[a] @ (Rcl[a] - dS @ Xl[a])).T)
                dSl.append(dS)
                dXl.append(dX)
            return dz, dSl, dXl

        _, dSa, dXa = sdir(0.0)
        apa = min(1.0, mstep(Sl, dSa))
        ada = min(1.0, mstep(Xl, dXa))
        mua = sum(float(np.sum((Sl[a] + apa * dSa[a]) * (Xl[a] + ada * dXa[a]))) for a in range(len(blocks))) / tot_n
        sig = float(np.clip((mua / max(mu, 1e-30)) ** 3, 1e-4, 0.8))
        dz, dS, dX = sdir(sig, dSa, dXa)
        ap = min(1.0, 0.96 * mstep(Sl, dS))
        ad = min(1.0, 0.96 * mstep(Xl, dX))
        z += ap * dz
        for a in range(len(blocks)):
            Sl[a] = 0.5 * ((Sl[a] + ap * dS[a]) + (Sl[a] + ap * dS[a]).T)
            Xl[a] = 0.5 * ((Xl[a] + ad * dX[a]) + (Xl[a] + ad * dX[a]).T)
        if ap < 1e-12 and ad < 1e-12:
            break

    pick = best if best is not None else fallback
    assert pick is not None, "Oracle failed to produce a PD witness!"
    _, _, Z_ep, sol_ls = pick
    lam_g = sol_ls[:n_g]
    lam_h0 = sol_ls[n_g : n_g + n_h]
    lam_h1 = sol_ls[n_g + n_h : n_g + 2 * n_h]

    lam_0_mp, lam_1_mp = [], []
    ig, ih = 0, 0
    for g_idx, _, _ in id_meta:
        if g_idx == 0:
            v = mp.mpf(f"{float(lam_g[ig]):.17g}")
            lam_0_mp.append(v)
            lam_1_mp.append(v)
            ig += 1
        else:
            lam_0_mp.append(mp.mpf(f"{float(lam_h0[ih]):.17g}"))
            lam_1_mp.append(mp.mpf(f"{float(lam_h1[ih]):.17g}"))
            ih += 1

    def pack_Z(Z_raw):
        Z0_mp = [[mp.mpf(f"{float(0.5 * (Z_raw[0][i, j] + Z_raw[0][j, i])):.17g}") for j in range(sz0)] for i in range(sz0)]
        factors_mp = [None]
        for a in range(1, nb1):
            sz = raw_blocks[a][0]
            if sz == 0:
                factors_mp.append([])
                continue
            ev, V = np.linalg.eigh(0.5 * (Z_raw[a] + Z_raw[a].T))
            factors_mp.append([
                (mp.mpf(f"{float(ev[ri]):.17g}"), [mp.mpf(f"{float(V[i, ri]):.17g}") for i in range(sz)])
                for ri in range(len(ev)) if ev[ri] > 1e-15
            ])
        return Z0_mp, factors_mp

    Z0_0, fac_0 = pack_Z(Z_ep[0])
    Z0_1, fac_1 = pack_Z(Z_ep[1])
    return (Z0_0, fac_0, lam_0_mp, Z0_1, fac_1, lam_1_mp)


def certify_stage1_tail_53(m, Lam_start_mp, Lam_end_mp):
    """Adaptive Stage-1 tail certification on [Lam_start_mp, Lam_end_mp] (pure Section-B verified!)."""
    stack = [(Lam_start_mp, Lam_end_mp, 0)]
    covered = []
    while stack:
        lo, hi, depth = stack.pop()
        mults = oracle_stage1_lp_multipliers_53(lo, hi)
        ok, info = iv_certify_stage1_tail_box_53(m, lo, hi, mults)
        if ok:
            covered.append((lo, hi, info))
        else:
            assert depth < 14, f"Stage-1 tail failed to bisect on [{lo}, {hi}]!"
            mid = (lo + hi) / mp.mpf(2)
            stack.append((mid, hi, depth + 1))
            stack.append((lo, mid, depth + 1))
    covered.sort(key=lambda x: x[0])
    return covered


def run_suite1_zero_float_p53_certifications():
    print("\n" + "=" * 100)
    print("SUITE 1 (SECTION B — 100% ZERO-FLOAT 50-DIGIT mpmath.iv, ALL n >= 1, C^n, ALL Lambda)")
    print("THEOREM 1 & THEOREM 2: DEGREE-3 EXACTLY-AFFINE (A, B, C) LIFT + PARAMETER-FREE KUBO-ANDO")
    print("=" * 100)

    structs = {mode: build_abc_struct_iv(mode) for mode in ("8C5C", "deg8C", "deg6")}
    for mode, st in structs.items():
        print(f"  [Struct {mode:5s}] b0={len(st['blocks_wlists'][0]):2d}, n_var={st['n_var']:4d}, n_id={len(st['id_meta']):4d}, n_weights={len(st['blocks_wlists'])}")

    specs = [
        (2, "3.2515544", [
            ("3.2515568", "8C5C", 1e-8),
            ("3.2515950", "deg8C", 5e-8),
            ("3.2517500", "deg6", 1e-7),
            ("3.2521600", "deg6", 1e-6),
        ]),
        (3, "3.5807660", [
            ("3.5807685", "8C5C", 1e-8),
            ("3.5808050", "deg8C", 2e-8),
            ("3.5810000", "deg6", 1e-7),
            ("3.5814600", "deg6", 1e-6),
        ]),
        (4, "3.8598120", [
            ("3.8598145", "8C5C", 1e-8),
            ("3.8598500", "deg8C", 2e-8),
            ("3.8600500", "deg6", 1e-7),
            ("3.8604800", "deg6", 1e-6),
        ]),
    ]

    summaries = []
    for m, Lam_start_s, tiers in specs:
        t_m0 = time.perf_counter()
        Lam_cert_mp = mp.mpf(Lam_start_s)
        Lam_interp_iv = iv.sqrt(iv.mpf(2)) * (iv.mpf(1) + iv.sqrt(iv.mpf(m)))
        Lam_end_mp = mp.mpf(Lam_interp_iv.b) + mp.mpf("1e-6")
        print(f"\n--- p = 5/3 (kappa = 5/4), m = {m}: certifying ALL Lambda in [{Lam_start_s}, {ceil_fixed_str(Lam_end_mp, 6)}] ---")

        covered = []
        min_chol = None
        min_marg = None
        cur = Lam_cert_mp
        n_sos = 0
        for hi_s, mode, eps_I in tiers:
            hi_mp = mp.mpf(hi_s)
            t_b = time.perf_counter()
            mults = oracle_stage1_lp_multipliers_53(cur, hi_mp)
            bundle = oracle_solve_abc_interval_2ep(structs[mode], m, cur, hi_mp, mults, eps_I_f=eps_I)
            ok, info = iv_certify_abc_interval(m, cur, hi_mp, structs[mode], mults, bundle)
            assert ok, f"Section-B mpmath.iv verification FAILED on m={m} [{cur}, {hi_mp}] ({mode}): {info}"
            _, _, margin, d_chol, max_res = info
            n_sos += 1
            if min_chol is None or d_chol < min_chol:
                min_chol = d_chol
            if min_marg is None or margin < min_marg:
                min_marg = margin
            covered.append((cur, hi_mp))
            print(
                f"  [SOS-{mode:5s}] [{mp.nstr(cur, 10)}, {mp.nstr(hi_mp, 10)}] "
                f"Psi_ub<target: margin>{floor_sci_str(margin, 3)} | min_chol>{floor_sci_str(d_chol, 3)} "
                f"| max_res<={ceil_sci_str(max_res, 2)} ({time.perf_counter() - t_b:.1f}s) PASS"
            )
            cur = hi_mp

        tail_boxes = certify_stage1_tail_53(m, cur, Lam_end_mp)
        for lo, hi, (_, _, tmarg) in tail_boxes:
            covered.append((lo, hi))
            if min_marg is None or tmarg < min_marg:
                min_marg = tmarg
        print(
            f"  [Stage-1 Tail] [{mp.nstr(cur, 10)}, {ceil_fixed_str(Lam_end_mp, 6)}] "
            f"certified in {len(tail_boxes)} pure mpmath.iv boxes (0 gaps) PASS"
        )

        rec = iv_verify_p53_record_summary(m, Lam_cert_mp, covered)
        rec["n_sos"] = n_sos
        rec["n_s1"] = len(tail_boxes)
        rec["min_chol_str"] = floor_sci_str(min_chol, 3)
        rec["min_marg_str"] = floor_sci_str(min_marg, 3)
        rec["elapsed_s"] = time.perf_counter() - t_m0
        summaries.append(rec)

    print("\n" + "=" * 100)
    print("CERTIFIED ZERO-FLOAT 50-DIGIT mpmath.iv WORLD-RECORD ENCLOSURES AT p = 5/3 (ALL n >= 1, C^n)")
    print("=" * 100)
    print(f"  {'m':2s} | {'Cert LB (#49)':15s} {'NEW Cert UB':15s} {'#139 UB':15s} | {'NEW Gap<=':10s} {'#139 Gap<=':10s} {'vs #139':8s} {'vs V6':8s} | {'min_chol>':9s} {'min_marg>':9s} {'Boxes':7s}")
    print("  " + "-" * 124)
    for r in summaries:
        g139 = f">={r['gain_139_str']}x"
        gv6 = f">={r['gain_v6_str']}x"
        print(
            f"  {r['m']:2d} | {r['C_lb_str']:15s} {r['C_ub_str12']:15s} {r['C_139_str']:15s} | "
            f"{r['new_gap_str']:10s} {r['old139_gap_str']:10s} {g139:8s} {gv6:8s} | "
            f"{r['min_chol_str']:9s} {r['min_marg_str']:9s} {r['n_sos']}S+{r['n_s1']}T"
        )
    return summaries


# ==============================================================================
# SUITE 2 (FLOAT64 ORACLE DIAGNOSTIC): THEOREM-5 2-ATOM PARALLEL SUM 3x3 BLOCK
# SCHUR COMPLEMENT Mtilde_2a(A, B, C) & EXACT ker(A) v_k-NORM-INFLATION DIAGNOSIS
# ==============================================================================

def _o_solve_rg2_53(m):
    L0 = 2.0 ** 1.5
    Lam0 = {2: 3.2515527, 3: 3.580754, 4: 3.859808}[m]

    def unpack(v):
        L = L0 + np.exp(v[0])
        d1 = np.exp(v[1])
        x1 = np.exp(v[2])
        x2 = np.exp(v[3])
        th = v[4]
        cs, sn = np.cos(th), np.sin(th)
        R = np.array([[cs, -sn], [sn, cs]])
        return L, np.array([1.0, d1]), R @ np.diag([x1, x2]) @ R.T

    triu = np.triu_indices(2)

    def res(v):
        L, dd, X = unpack(v)
        _, _, sp = _o_roots_kappa(L, 1.25)
        sD = np.sqrt(dd)
        D = np.diag(dd)
        H = (sD[:, None] * X) * sD[None, :]
        M = D + H
        G = (sD[:, None] * H) * sD[None, :]
        Ds = dd ** (-0.75)
        Z = (dd ** (-0.25))[:, None] * _o_matpow(G, 0.25) * (dd ** (-0.25))[None, :]
        R1 = (Ds[:, None] * _o_matpow(M, 1.5) * Ds[None, :]) - L * Z
        Ehat = ((dd ** (-1.25))[:, None] * _o_matpow(G, 1.25) * (dd ** (-1.25))[None, :]) - Z
        R2 = Ehat - np.diag([-sp / (m - 1.0), sp])
        return np.concatenate([R1[triu], R2[triu]])

    v0 = [np.log(Lam0 - L0), np.log(0.01), np.log(0.0005), np.log(0.35), 0.12]
    sol = least_squares(res, v0, bounds=([-20, -20, -20, -5, 1e-3], [10, 0, 5, 5, 1.5]), xtol=1e-15, ftol=1e-15, gtol=1e-15)
    assert float(np.linalg.norm(sol.fun)) < 1e-12
    L, dd, X = unpack(sol.x)
    evX, VX = eigh(X)
    w = VX[0, :] ** 2
    xm, xp, sp = _o_roots_kappa(L, 1.25)
    return L, dd, X, evX, w, xm, xp, sp


def run_suite2_mtilde_2a_benchmark():
    print("\n" + "=" * 100)
    print("SUITE 2 (FLOAT64 ORACLE DIAGNOSTIC): THEOREM-5 2-ATOM PARALLEL SUM 3x3 DEGREE-3 BLOCK")
    print("SCHUR COMPLEMENT Mtilde_2a(A, B, C) >= 0 (ZERO [E, A], ZERO U-E, ZERO L+E)")
    print("=" * 100)

    print("\n[2A] Empirical Tightness & Uniform ||v_k^{opt}||^2 Across ~100 Exact 1x1/2x2/3x3 Holden Solutions:")
    rg2_params = {}
    for m, dU in [(2, 5e-4), (3, 6e-4), (4, 7e-4)]:
        L, dd, X, evX, w, xm, xp, sp = _o_solve_rg2_53(m)
        x1, x2 = float(evX[0]), float(evX[1])
        w1, w2 = float(w[0]), float(w[1])
        c_rg = (m / (m - 1.0)) * sp
        U_cap = sp + dU
        sD = np.sqrt(dd)
        H_rg = (sD[:, None] * X) * sD[None, :]
        samples = [(np.array([[1.0]]), np.array([[xm]])), (np.array([[1.0]]), np.array([[xp]])), (np.diag(dd), H_rg)]
        rng = np.random.default_rng(100 + m)
        for d1 in np.concatenate([np.logspace(-6, -2, 10), np.linspace(0.015, 0.8, 10)]):
            D = np.diag([1.0, d1])
            A = np.diag([1.0, np.sqrt(d1)])
            for th in [0.05, 0.25, 0.7]:
                cs, sn = np.cos(th), np.sin(th)
                R = np.array([[cs, -sn], [sn, cs]])
                H = R @ np.diag([xm, xp * d1]) @ R.T
                for _ in range(200):
                    G = A @ H @ A
                    M = _o_matpow(L * A @ _o_matpow(G, 0.25) @ A, 2.0 / 3.0)
                    ev, V = eigh(0.5 * ((M - D) + (M - D).T))
                    H = (V * np.maximum(ev, 1e-13)) @ V.T
                if float(np.linalg.norm(_o_matpow(D + H, 1.5) - L * A @ _o_matpow(A @ H @ A, 0.25) @ A)) < 1e-9:
                    samples.append((D, H))
        for _ in range(55):
            d1 = 10.0 ** rng.uniform(-3.5, -0.05)
            d2 = 10.0 ** rng.uniform(-4.5, np.log10(d1))
            D = np.diag([1.0, d1, d2])
            A = np.diag([1.0, np.sqrt(d1), np.sqrt(d2)])
            Q = np.linalg.qr(rng.standard_normal((3, 3)))[0]
            H = Q @ np.diag(rng.uniform(0.005, 1.0, 3) * np.array([1.0, d1, d2])) @ Q.T
            for _ in range(220):
                G = A @ H @ A
                M = _o_matpow(L * A @ _o_matpow(G, 0.25) @ A, 2.0 / 3.0)
                ev, V = eigh(0.5 * ((M - D) + (M - D).T))
                H = (V * np.maximum(ev, 1e-13)) @ V.T
            if float(np.linalg.norm(_o_matpow(D + H, 1.5) - L * A @ _o_matpow(A @ H @ A, 0.25) @ A)) < 1e-9:
                samples.append((D, H))

        A_rg = np.diag(np.sqrt(dd))
        G_rg = A_rg @ H_rg @ A_rg
        B_rg = _o_matpow(np.diag(dd) + H_rg, 0.5)
        C_rg = _o_matpow(G_rg, 0.25)
        Z_rg = (dd ** (-0.25))[:, None] * C_rg * (dd ** (-0.25))[None, :]
        T1_rg = (dd ** (-0.25))[:, None] * B_rg * (dd ** (-0.25))[None, :]
        T2_rg = (dd ** (-0.75))[:, None] * (C_rg @ C_rg @ C_rg) * (dd ** (-0.75))[None, :]
        K1 = sp * np.eye(2) - x1 * Z_rg + ((1.0 + x1) / L) * np.linalg.inv(T1_rg - ((1.0 + x1) / L) * T2_rg)
        u1_rg = (dd ** (-0.25)) * (w1 * np.linalg.solve(K1, np.array([c_rg, 0.0])))

        def exact_u1(xv):
            K1s = sp - x1 * (xv ** 0.25) + ((1.0 + x1) / L) / ((1.0 + xv) ** 0.5 - ((1.0 + x1) / L) * (xv ** 0.75))
            K2s = sp - x2 * (xv ** 0.25) + ((1.0 + x2) / L) / ((1.0 + xv) ** 0.5 - ((1.0 + x2) / L) * (xv ** 0.75))
            return (w1 / K1s) / (w1 / K1s + w2 / K2s)

        M_fit = np.array([
            [1.0, C_rg[0, 0], B_rg[0, 0], (C_rg @ C_rg)[0, 0]],
            [0.0, C_rg[1, 0], B_rg[1, 0], (C_rg @ C_rg)[1, 0]],
            [1.0, xm ** 0.25, (1.0 + xm) ** 0.5, xm ** 0.5],
            [1.0, xp ** 0.25, (1.0 + xp) ** 0.5, xp ** 0.5],
        ])
        c0 = np.linalg.solve(M_fit, np.array([u1_rg[0], u1_rg[1], exact_u1(xm), exact_u1(xp)]))

        def eval_quad(D, H, coefs):
            a1, b1, e1, g1 = coefs
            n = D.shape[0]
            A = _o_matpow(D, 0.5)
            G = A @ H @ A
            B = _o_matpow(D + H, 0.5)
            C = _o_matpow(G, 0.25)
            P1 = a1 * A + b1 * C + e1 * B + g1 * (C @ C)
            P2 = A - P1
            v = np.zeros(n)
            v[0] = 1.0
            tot = -dU
            mv = 0.0
            for xk, wk, Pk in [(x1, w1, P1), (x2, w2, P2)]:
                u = Pk @ v
                quad = float(u @ ((U_cap * A - xk * C) @ u))
                S = (L / (1.0 + xk)) * (A @ B @ A) - (C @ C @ C)
                rhs = (A @ A) @ u
                vk = np.linalg.solve(S, rhs)
                # Optimal Schur auxiliary vector: v_k^{opt} = -w_k^{-1/2} S_k^{-1} A^2 P_k v
                mv = max(mv, float(vk @ vk) / wk)
                tot += (quad + float(rhs @ vk)) / wk
            return tot / c_rg, mv

        opt_q = minimize(lambda c: max(eval_quad(D, H, c)[0] for D, H in samples), c0, method="Nelder-Mead", options={"maxiter": 3500, "xatol": 1e-12, "fatol": 1e-13})
        vals_q = [eval_quad(D, H, opt_q.x) for D, H in samples]
        max_q = max(v[0] for v in vals_q)
        max_vk2 = max(v[1] for v in vals_q)
        assert max_q - 1.0 < 5e-8 and max_vk2 < 0.2
        # Linear P1 (degree 1 => entire 3x3 Mtilde_2a is degree 3!)
        c0_lin = np.linalg.solve(M_fit[:3, :3], np.array([u1_rg[0], u1_rg[1], exact_u1(xm)]))
        opt_l = minimize(lambda c: max(eval_quad(D, H, [c[0], c[1], c[2], 0.0])[0] for D, H in samples), c0_lin, method="Nelder-Mead", options={"maxiter": 3000, "xatol": 1e-12, "fatol": 1e-13})
        max_l = max(eval_quad(D, H, [opt_l.x[0], opt_l.x[1], opt_l.x[2], 0.0])[0] for D, H in samples)
        rg2_params[m] = (L, x1, x2, w1, w2, opt_l.x, dU)
        print(
            f"  m={m} (n={len(samples):2d} sols, dU={dU:.0e}): x=({x1:.5f},{x2:.5f}) w=({w1:.5f},{w2:.5f}) "
            f"| deg1_exc={max_l - 1.0:+.3e} | deg2_exc={max_q - 1.0:+.3e} | max||vk||^2={max_vk2:.4f}"
        )

    print("\n[2B] 3x3 Block NC-SOS SDP on Degree-3 Mtilde_2a(A, B, C) (sz0=53, ZERO [E,A], ZERO U-E/L+E):")
    def canon_blk(p, q, w):
        i, j = 0, len(w)
        if p == 0:
            while i < j and w[i] == 0:
                i += 1
        if q == 0:
            while j > i and w[j - 1] == 0:
                j -= 1
        w1 = w[i:j]
        k1 = (p, q, w1)
        k2 = (q, p, w1[::-1])
        return k1 if k1 <= k2 else k2

    def pmul_f(p, q):
        out = {}
        for w1, c1 in p.items():
            for w2, c2 in q.items():
                w = w1 + w2
                out[w] = out.get(w, 0.0) + c1 * c2
        return {w: c for w, c in out.items() if abs(c) > 1e-16}

    def padd_f(p, q, s=1.0):
        out = dict(p)
        for w, c in q.items():
            out[w] = out.get(w, 0.0) + s * c
        return {w: c for w, c in out.items() if abs(c) > 1e-16}

    W0 = [(0, w) for w in reduced_words_iv(3, 3)]
    W1 = [(1, w) for w in gen_words_iv(3, 2)]
    W2 = [(2, w) for w in gen_words_iv(3, 2)]
    V_main = W0 + W1 + W2
    ck_list = sorted(set(canon_blk(p, q, u[::-1] + v) for p, u in V_main for q, v in V_main), key=lambda x: (x[0], x[1], len(x[2]), x[2]))
    k2i = {k: i for i, k in enumerate(ck_list)}
    n_var = len(ck_list)
    idx0 = k2i[(0, 0, ())]

    for m in (2, 3, 4):
        t0 = time.perf_counter()
        L, x1, x2, w1, w2, clin, dU = rg2_params[m]
        xm, xp, sp = _o_roots_kappa(L, 1.25)
        c_rg = (m / (m - 1.0)) * sp
        X_cap = xp
        B_cap = np.sqrt(1.0 + X_cap)
        C_cap = X_cap ** 0.25
        cA = 1.0 / B_cap
        U_cap = sp + dU
        a1, b1, e1 = clin
        P1 = {k: v for k, v in {(0,): a1, (1,): e1 * B_cap, (2,): b1 * C_cap}.items() if abs(v) > 1e-16}
        P2 = padd_f({(0,): 1.0}, P1, -1.0)
        pI = {(): 1.0}
        p0 = {(0,): 1.0}
        p1 = {(1,): 1.0}
        p2 = {(2,): 1.0}
        pIm0 = {(): 1.0, (0,): -1.0}
        S1_p = {(0, 1, 0): (L / (1.0 + x1)) * B_cap, (2, 2, 2): -(C_cap ** 3)}
        S2_p = {(0, 1, 0): (L / (1.0 + x2)) * B_cap, (2, 2, 2): -(C_cap ** 3)}
        pKA = {(0, 1, 0): 1.0, (2, 2, 2): -1.0}
        weights = [
            pI, p0, pIm0, pmul_f(p0, pIm0),
            p1, padd_f(p0, p1, -1.0), padd_f(p1, {(0,): -cA}), pmul_f(p1, padd_f(pI, p1, -1.0)),
            p2, padd_f(p0, p2, -1.0), pmul_f(p2, padd_f(pI, p2, -1.0)), pKA,
        ]
        raw_F = []
        for pw in weights:
            cand = [b for b in V_main if all(canon_blk(b[0], b[0], b[1][::-1] + wm + b[1]) in k2i for wm in pw)]
            sub = []
            for b in cand:
                if all(canon_blk(b[0], c[0], b[1][::-1] + wm + c[1]) in k2i and canon_blk(c[0], b[0], c[1][::-1] + wm + b[1]) in k2i for c in sub for wm in pw):
                    sub.append(b)
            if not sub:
                continue
            sz = len(sub)
            F = np.zeros((n_var, sz, sz))
            for i, (p, u) in enumerate(sub):
                ur = u[::-1]
                for j, (q, v) in enumerate(sub):
                    for wm, c in pw.items():
                        idx = k2i[canon_blk(p, q, ur + wm + v)]
                        F[idx, i, j] += 0.5 * c
                        F[idx, j, i] += 0.5 * c
            raw_F.append(F)

        g = {(1, 1, 1): 1.0, (0, 2, 0): -L * C_cap / (B_cap ** 3)}
        h1 = {(0, 1, 1, 0): B_cap ** 2, (0, 0, 0, 0): -1.0, (2, 2, 2, 2): -X_cap}
        h2 = padd_f(pmul_f(p1, {(0, 2, 0): 1.0}), pmul_f({(0, 2, 0): 1.0}, p1), -1.0)
        id_rows = []
        short_w = gen_words_iv(3, 3)
        for poly in (g, h1, h2):
            for p in range(3):
                for q in range(p, 3):
                    for wL in short_w:
                        for wR in short_w:
                            if len(wL) + len(wR) > 3:
                                continue
                            ok = True
                            row = {}
                            for wm, c in poly.items():
                                ck = canon_blk(p, q, wL + wm + wR)
                                if ck not in k2i:
                                    ok = False
                                    break
                                ii = k2i[ck]
                                row[ii] = row.get(ii, 0.0) + c
                            if ok and any(abs(v) > 1e-15 for v in row.values()):
                                r = np.zeros(n_var)
                                for ii, v in row.items():
                                    r[ii] = v
                                id_rows.append(r)

        a0 = np.zeros(n_var)
        a0[idx0] = 1.0
        A_eq = np.vstack([a0[None, :], np.array(id_rows)])
        b_eq = np.zeros(A_eq.shape[0])
        b_eq[0] = 1.0
        rn = np.linalg.norm(A_eq, axis=1)
        A_n = A_eq / rn[:, None]
        b_n = b_eq / rn
        U_eq, s_eq, Vt_eq = np.linalg.svd(A_n, full_matrices=True)
        rk_eq = int(np.sum(s_eq > 1e-11 * s_eq[0]))
        y0 = Vt_eq[:rk_eq].T @ ((U_eq[:, :rk_eq].T @ b_n) / s_eq[:rk_eq])
        N_null = Vt_eq[rk_eq:].T
        n_free = N_null.shape[1]

        c_orig = np.zeros(n_var)
        for xk, wk, Pk, Sk, bidx in [(x1, w1, P1, S1_p, 1), (x2, w2, P2, S2_p, 2)]:
            Pk_s = {w[::-1]: c for w, c in Pk.items()}
            M00 = pmul_f(pmul_f(Pk_s, {(0,): U_cap, (2,): -xk * C_cap}), Pk)
            for wm, c in M00.items():
                c_orig[k2i[canon_blk(0, 0, wm)]] += -c / wk
            M0k = pmul_f(Pk_s, {(0, 0): 1.0})
            for wm, c in M0k.items():
                c_orig[k2i[canon_blk(0, bidx, wm)]] += (2.0 / np.sqrt(wk)) * c
            for wm, c in Sk.items():
                c_orig[k2i[canon_blk(bidx, bidx, wm)]] += c

        blocks = []
        for idx_b, F in enumerate(raw_F):
            sz = F.shape[1]
            B0 = np.tensordot(y0, F, axes=(0, 0))
            Bz = np.tensordot(N_null, F, axes=(0, 0))
            G_str = 0.5 * ((B0 @ B0 + Bz.reshape(-1, sz).T @ Bz.reshape(-1, sz)) + (B0 @ B0 + Bz.reshape(-1, sz).T @ Bz.reshape(-1, sz)).T)
            ev, V = np.linalg.eigh(G_str)
            if len(ev) == 0 or ev[-1] <= 1e-20:
                continue
            Qa = V[:, ev > 1e-11 * ev[-1]]
            rb = Qa.shape[1]
            if rb == 0:
                continue
            B0_r = 0.5 * (Qa.T @ B0 @ Qa + (Qa.T @ B0 @ Qa).T)
            Bz_r = 0.5 * ((Qa.T @ Bz) @ Qa + np.swapaxes((Qa.T @ Bz) @ Qa, 1, 2))
            Bzf_r = Bz_r.reshape(n_free, rb * rb)
            sc = max(float(np.linalg.norm(B0_r)), float(np.max(np.linalg.norm(Bzf_r, axis=1))), 1e-12)
            blocks.append((idx_b, rb, Qa, B0_r / sc, Bz_r / sc, Bzf_r / sc, sc))

        c0_v = float(c_orig @ y0)
        gv = N_null.T @ c_orig
        tot_n = sum(b[1] for b in blocks)
        z = np.zeros(n_free)
        Sl = [np.eye(b[1]) for b in blocks]
        Xl = [np.eye(b[1]) for b in blocks]

        def mstep(Ml, dMl):
            am = 1.0
            for M, dM in zip(Ml, dMl):
                ev, V = np.linalg.eigh(M)
                Li = V * (1.0 / np.sqrt(np.maximum(ev, 1e-30)))
                G = 0.5 * (Li.T @ dM @ Li + (Li.T @ dM @ Li).T)
                lm = float(np.linalg.eigvalsh(G)[0])
                if lm < -1e-16:
                    am = min(am, -1.0 / lm)
            return am

        for _ in range(1, 45):
            Rpl = []
            rd = gv.copy()
            mu = 0.0
            for a, (_, rb, _, B0, _, Bzf, _) in enumerate(blocks):
                Rp = 0.5 * ((Sl[a] - (B0 + (z @ Bzf).reshape(rb, rb))) + (Sl[a] - (B0 + (z @ Bzf).reshape(rb, rb))).T)
                Rpl.append(Rp)
                rd -= Bzf @ Xl[a].ravel()
                mu += float(np.sum(Sl[a] * Xl[a]))
            mu /= tot_n
            if mu < 1e-11:
                break
            Ms = np.zeros((n_free, n_free))
            Sinvl = []
            for a, (_, rb, _, _, Bz, _, _) in enumerate(blocks):
                ev, V = np.linalg.eigh(Sl[a])
                Si = (V * (1.0 / np.maximum(ev, 1e-30))) @ V.T
                Sinvl.append(Si)
                Ms += (Si @ Bz).reshape(n_free, rb * rb) @ (Bz @ Xl[a]).reshape(n_free, rb * rb).T
            Ms = 0.5 * (Ms + Ms.T)
            dd_m = np.sqrt(np.maximum(np.diag(Ms), 1e-30))
            Mn = (Ms / dd_m[:, None]) / dd_m[None, :] + 1e-14 * np.eye(n_free)

            def sM(rhs):
                try:
                    return np.linalg.solve(Mn, rhs / dd_m) / dd_m
                except np.linalg.LinAlgError:
                    return np.linalg.lstsq(Mn, rhs / dd_m, rcond=1e-14)[0] / dd_m

            def sdir(sv, dSa=None, dXa=None):
                rhs = -rd.copy()
                Rcl = []
                for a, (_, rb, _, _, _, Bzf, _) in enumerate(blocks):
                    Rc = sv * mu * np.eye(rb) - Sl[a] @ Xl[a]
                    if dSa is not None:
                        Rc = Rc - dSa[a] @ dXa[a]
                    Rcl.append(Rc)
                    W = 0.5 * ((Sinvl[a] @ (Rc + Rpl[a] @ Xl[a])) + (Sinvl[a] @ (Rc + Rpl[a] @ Xl[a])).T)
                    rhs += Bzf @ W.ravel()
                dz = sM(rhs)
                dSl, dXl = [], []
                for a, (_, rb, _, _, _, Bzf, _) in enumerate(blocks):
                    dS = 0.5 * (((dz @ Bzf).reshape(rb, rb) - Rpl[a]) + ((dz @ Bzf).reshape(rb, rb) - Rpl[a]).T)
                    dX = 0.5 * ((Sinvl[a] @ (Rcl[a] - dS @ Xl[a])) + (Sinvl[a] @ (Rcl[a] - dS @ Xl[a])).T)
                    dSl.append(dS)
                    dXl.append(dX)
                return dz, dSl, dXl

            _, dSa, dXa = sdir(0.0)
            apa = min(1.0, mstep(Sl, dSa))
            ada = min(1.0, mstep(Xl, dXa))
            mua = sum(float(np.sum((Sl[a] + apa * dSa[a]) * (Xl[a] + ada * dXa[a]))) for a in range(len(blocks))) / tot_n
            sig = float(np.clip((mua / max(mu, 1e-30)) ** 3, 1e-4, 0.8))
            dz, dS, dX = sdir(sig, dSa, dXa)
            ap = min(1.0, 0.96 * mstep(Sl, dS))
            ad = min(1.0, 0.96 * mstep(Xl, dX))
            z += ap * dz
            for a in range(len(blocks)):
                Sl[a] = 0.5 * ((Sl[a] + ap * dS[a]) + (Sl[a] + ap * dS[a]).T)
                Xl[a] = 0.5 * ((Xl[a] + ad * dX[a]) + (Xl[a] + ad * dX[a]).T)
            if ap < 1e-12 and ad < 1e-12:
                break

        y_opt = y0 + N_null @ z
        v1n = float(y_opt[k2i[(1, 1, ())]])
        v2n = float(y_opt[k2i[(2, 2, ())]])
        c_p = (-(c0_v + float(gv @ z))) - dU
        excP = c_p / c_rg - 1.0
        assert excP < 1e-5 and v1n > 5.0
        print(
            f"  Mtilde_2a m={m} (sz0=53, nv={n_var}, nf={n_free}, {time.perf_counter() - t0:.1f}s): "
            f"excP={excP:+.3e} | ker(A) inflation: ||v1||^2={v1n:.1f}, ||v2||^2={v2n:.1f} (vs <=0.094 true)"
        )


# ==============================================================================
# SUITE 3 (ATTACK 2): ANALYTIC OPERATOR THEOREMS & SHARP OBSTRUCTIONS
# ==============================================================================

def run_suite3_attack2_analytic_and_obstructions():
    print("\n" + "=" * 100)
    print("SUITE 3 (ATTACK 2): ANALYTIC THEOREMS (3 & 5) & SHARP SECOND-USE-OF-HOLDEN OBSTRUCTIONS (4)")
    print("=" * 100)

    # 3A: Complex U(3) verification of Theorem 3 (A Bt A - Ct^3 >= 0) and Theorem 5 (E_v[G] in [x_-, x_+])
    print("\n[3A] Complex U(3) Verification of Theorem 3 (A Bt A >= Ct^3) & Theorem 5 (Universal E_v[G] Enclosure):")
    rng = np.random.default_rng(202605)
    min_ka = 1e9
    max_holden_err = 0.0
    Lam53 = 3.2515527340
    xm53, xp53, _ = _o_roots_kappa(Lam53, 1.25)
    Bcap = np.sqrt(1.0 + xp53)
    Ccap = xp53 ** 0.25
    n_ok_53 = 0
    min_margin_G = 1e9
    min_margin_C = 1e9
    for _ in range(150):
        d1 = 10.0 ** rng.uniform(-3.0, -0.05)
        d2 = 10.0 ** rng.uniform(-4.0, np.log10(d1))
        dd = np.array([1.0, d1, d2])
        D = np.diag(dd)
        A = np.diag(np.sqrt(dd))
        # Random complex unitary U in U(3)
        Z_c = rng.standard_normal((3, 3)) + 1j * rng.standard_normal((3, 3))
        U_c, _ = np.linalg.qr(Z_c)
        H = U_c @ np.diag(rng.uniform(0.01, 1.0, 3) * dd) @ U_c.conj().T
        for _ in range(250):
            G = A @ H @ A
            M = _o_matpow_herm(Lam53 * A @ _o_matpow_herm(G, 0.25) @ A, 2.0 / 3.0)
            ev, V = eigh(0.5 * ((M - D) + (M - D).conj().T))
            H = (V * np.maximum(ev, 1e-13)) @ V.conj().T
        G = A @ H @ A
        M = D + H
        B = _o_matpow_herm(M, 0.5)
        C = _o_matpow_herm(G, 0.25)
        err = float(np.linalg.norm(B @ B @ B - Lam53 * A @ C @ A))
        if err > 1e-9:
            continue
        n_ok_53 += 1
        max_holden_err = max(max_holden_err, err)
        Bt = B / Bcap
        Ct = C / Ccap
        KA_mat = A @ Bt @ A - Ct @ Ct @ Ct
        min_ka = min(min_ka, float(np.linalg.eigvalsh(0.5 * (KA_mat + KA_mat.conj().T))[0]))
        eg = float(np.real(G[0, 0]))
        ec = float(np.real(C[0, 0]))
        min_margin_G = min(min_margin_G, eg - xm53, xp53 - eg)
        min_margin_C = min(min_margin_C, ec - (xm53 ** 0.25), (xp53 ** 0.25) - ec)
    assert n_ok_53 >= 100 and min_ka >= -1e-12 and min_margin_G >= -1e-10 and min_margin_C >= -1e-10
    print(
        f"  p=5/3 ({n_ok_53} complex U(3) Holden sols, res<={max_holden_err:.1e}): "
        f"min_eig(A Bt A - Ct^3)={min_ka:+.3e} >= 0 | min(E_v[G] margin)={min_margin_G:+.3e} | min(E_v[C] margin)={min_margin_C:+.3e} (PASS)"
    )

    # Check Theorem 5 across general p in [4/3, 2): p in {7/5, sqrt(2), 3/2, 7/4} (plus p = 5/3 above)
    for plbl, pp, Lam_v in [
        ("7/5", 1.4, 6.1710422),
        ("sqrt(2)", np.sqrt(2.0), 5.6615),
        ("3/2", 1.5, 4.4628),
        ("7/4", 1.75, 2.755),
    ]:
        kp = pp / (2.0 * (pp - 1.0))
        xm, xp, _ = _o_roots_kappa(Lam_v, kp)
        min_mg = 1e9
        cnt = 0
        for _ in range(40):
            d1 = 10.0 ** rng.uniform(-2.5, -0.05)
            dd = np.array([1.0, d1])
            D = np.diag(dd)
            A = np.diag(np.sqrt(dd))
            Z_c = rng.standard_normal((2, 2)) + 1j * rng.standard_normal((2, 2))
            U_c, _ = np.linalg.qr(Z_c)
            H = U_c @ np.diag(rng.uniform(0.01, 1.0, 2) * dd) @ U_c.conj().T
            for _ in range(250):
                G = A @ H @ A
                M = _o_matpow_herm(Lam_v * A @ _o_matpow_herm(G, kp - 1.0) @ A, 1.0 / (2.0 * kp - 1.0))
                ev, V = eigh(0.5 * ((M - D) + (M - D).conj().T))
                H = (V * np.maximum(ev, 1e-13)) @ V.conj().T
            G = A @ H @ A
            M = D + H
            if float(np.linalg.norm(_o_matpow_herm(M, 2.0 * kp - 1.0) - Lam_v * A @ _o_matpow_herm(G, kp - 1.0) @ A)) > 1e-9:
                continue
            cnt += 1
            eg = float(np.real(G[0, 0]))
            min_mg = min(min_mg, eg - xm, xp - eg)
        assert cnt >= 20 and min_mg >= -1e-10
        print(f"  p={plbl:7s} (k={kp:.4f}, {cnt:2d} cplx 2x2 Holden sols): E_v[G] in [{xm:.6f}, {xp:.6f}], min_margin={min_mg:+.3e} (PASS)")

    # 3B: Theorem 4(a) Holden-Free 1x1 Positivity Trap for K_{x0} + V^* B_{sigma_+} V
    print("\n[3B] Theorem 4(a) — Holden-Free 1x1 Positivity Trap (B_{sp}(u) >= 0 on (0, x_+] => K_0 + V^* B V >= K_0):")
    configs = [
        ("5/3", 1.25, 3.251552734, 0.12, "primal"),
        ("7/5", 1.75, 6.1710422,   0.35, "dual"),
        ("5/4", 2.50, 16.905675,   0.55, "dual"),
        ("6/5", 3.00, 33.44807,    0.70, "dual"),
    ]
    for lbl, k, Lam, cV, fam in configs:
        xm, xp, sp = _o_roots_kappa(Lam, k)
        cr = 2.0 * sp
        us = np.geomspace(1e-5, xp, 4000)
        Bsp = sp - (us ** (k - 1.0)) * (us - 1.0)
        assert float(np.min(Bsp)) >= -1e-14
        V2 = (cV * (us - xm) / xp) ** 2
        if fam == "primal":
            gam0 = (1.0 + xm) / Lam
            K0 = sp - xm * (us ** (k - 1.0)) + gam0 / ((1.0 + us) ** (1.5 - k) - gam0 * (us ** (2.0 - k)))
            tot = K0 + V2 * Bsp
            assert float(np.min(tot - K0)) >= -1e-14 and float(np.max(tot)) / cr > 1.05
            print(f"  p={lbl} ({fam:6s}): min_1x1(B_sp)={np.min(Bsp):+.2e} >= 0 | max(K0/cr)={np.max(K0)/cr:.6f} <= max((K0+V2*Bsp)/cr)={np.max(tot)/cr:.6f} (OBSTRUCTED)")
        else:
            s0 = xm ** 0.5
            den = Lam / ((1.0 + us) ** (2.0 * k - 2.0)) - s0 * (us ** (1.5 - k))
            mask = den > 1e-4
            K0 = sp - s0 * (us[mask] ** (k - 0.5)) + 1.0 / den[mask]
            tot = K0 + V2[mask] * Bsp[mask]
            assert float(np.min(tot - K0)) >= -1e-14 and float(np.max(tot)) / cr > 2.0
            print(f"  p={lbl} ({fam:6s}): min_1x1(B_sp)={np.min(Bsp):+.2e} >= 0 | min_den={np.min(den):+.3e} | max_pos((K0+V2*Bsp)/cr)={np.max(tot)/cr:.4f} (OBSTRUCTED)")

    # 3C: Theorem 4(b) Non-Holden 2x2 Misalignment Obstruction + Theorem 4(c) True Holden Alignment Anatomy
    print("\n[3C] Theorem 4(b) — Non-Holden 2x2 Misalignment Obstruction (ALL 1st-Use Bounds OK & Indefinite B_{sp}):")
    rng2 = np.random.default_rng(2026)
    for lbl, k, Lam, cV, fam in configs:
        xm, xp, sp = _o_roots_kappa(Lam, k)
        cr = 2.0 * sp
        best_v = 0.0
        best_inf = None
        for _ in range(3500):
            d1 = 10.0 ** rng2.uniform(-3.0, -0.05)
            dd = np.array([1.0, d1])
            sD = np.sqrt(dd)
            D = np.diag(dd)
            th = rng2.uniform(0.02, 1.5)
            cs, sn = np.cos(th), np.sin(th)
            R = np.array([[cs, -sn], [sn, cs]])
            x1 = 10.0 ** rng2.uniform(-4.0, np.log10(xp))
            x2 = rng2.uniform(x1, xp)
            X = R @ np.diag([x1, x2]) @ R.T
            H = (sD[:, None] * X) * sD[None, :]
            M = D + H
            G = (sD[:, None] * H) * sD[None, :]
            Z = (dd ** (1.0 - k))[:, None] * _o_matpow(G, k - 1.0) * (dd ** (1.0 - k))[None, :]
            Ehat = (dd ** (-k))[:, None] * _o_matpow(G, k) * (dd ** (-k))[None, :] - Z
            Bsp = sp * np.eye(2) - Ehat
            Vop = cV * (X - xm * np.eye(2)) / xp
            if fam == "primal":
                T1 = (dd ** (k - 1.5))[:, None] * _o_matpow(M, 3.0 - 2.0 * k) * (dd ** (k - 1.5))[None, :]
                T2 = (dd ** (k - 2.0))[:, None] * _o_matpow(G, 2.0 - k) * (dd ** (k - 2.0))[None, :]
                if float(np.linalg.eigvalsh(T1 - np.eye(2))[0]) < -1e-12:
                    continue
                if float(np.linalg.eigvalsh((Lam * xp / ((1.0 + xp) ** 2)) * T1 - T2)[0]) < -1e-12:
                    continue
                gam0 = (1.0 + xm) / Lam
                S = T1 - gam0 * T2
                if float(np.linalg.eigvalsh(S)[0]) <= 1e-9:
                    continue
                K0 = sp * np.eye(2) - xm * Z + gam0 * np.linalg.inv(S)
            else:
                if float(np.linalg.eigvalsh(((1.0 + xp) ** 3) * np.diag(dd ** 3) - _o_matpow(M, 3.0))[0]) < -1e-12:
                    continue
                LW1i = Lam * (dd ** (k - 1.0))[:, None] * _o_matpow(M, 2.0 - 2.0 * k) * (dd ** (k - 1.0))[None, :]
                P = (dd ** (k - 1.5))[:, None] * _o_matpow(G, 1.5 - k) * (dd ** (k - 1.5))[None, :]
                Y = (dd ** (0.5 - k))[:, None] * _o_matpow(G, k - 0.5) * (dd ** (0.5 - k))[None, :]
                s0 = xm ** 0.5
                S = LW1i - s0 * P
                if float(np.linalg.eigvalsh(S)[0]) <= 1e-6:
                    continue
                K0 = sp * np.eye(2) - s0 * Y + np.linalg.inv(S)
            tot = K0 + Vop.T @ Bsp @ Vop
            ev_t = float(np.linalg.eigvalsh(0.5 * (tot + tot.T))[-1]) / cr
            min_b = float(np.linalg.eigvalsh(0.5 * (Bsp + Bsp.T))[0])
            if ev_t > best_v and min_b < 0.0:
                best_v = ev_t
                res_h = float(np.linalg.norm((dd ** (0.5 - k))[:, None] * _o_matpow(M, 2.0 * k - 1.0) * (dd ** (0.5 - k))[None, :] - Lam * Z))
                best_inf = (ev_t, float(np.linalg.eigvalsh(0.5 * (K0 + K0.T))[-1]) / cr, min_b, res_h)
        assert best_inf is not None and best_inf[0] > 1.0005
        print(
            f"  p={lbl} ({fam:6s}): K0/cr={best_inf[1]:.6f} -> (K0+V*BV)/cr={best_inf[0]:.6f} "
            f"| min(B_sp)={best_inf[2]:+.3e} | ||Holden||={best_inf[3]:.2e} (OBSTRUCTED)"
        )

    print("\n[3D] Theorem 4(c) — True Holden Non-Commutative Eigenvector-Alignment Cancellation Anatomy (p = 5/3):")
    L2, dd2, X2, _, _, xm2, xp2, sp2 = _o_solve_rg2_53(2)
    cr2 = 2.0 * sp2
    cV2 = 0.12
    triu = np.triu_indices(2)

    def solve_H_d(dd_v, X_ref):
        sD = np.sqrt(dd_v)
        D = np.diag(dd_v)
        Ds = dd_v ** (-0.75)
        w0, V0 = eigh(0.5 * (X_ref + X_ref.T))
        S0 = (V0 * np.log(np.maximum(w0, 1e-14))) @ V0.T

        def res(v):
            S = np.zeros((2, 2))
            S[triu] = v
            S = S + S.T - np.diag(np.diag(S))
            w, V = eigh(S)
            X = (V * np.exp(np.clip(w, -20, 10))) @ V.T
            H = (sD[:, None] * X) * sD[None, :]
            M = D + H
            G = (sD[:, None] * H) * sD[None, :]
            Z = (dd_v ** (-0.25))[:, None] * _o_matpow(G, 0.25) * (dd_v ** (-0.25))[None, :]
            return ((Ds[:, None] * _o_matpow(M, 1.5) * Ds[None, :]) - L2 * Z)[triu]

        sol = root(res, S0[triu], method="hybr", tol=1e-14)
        S = np.zeros((2, 2))
        S[triu] = sol.x
        S = S + S.T - np.diag(np.diag(S))
        w, V = eigh(S)
        return (V * np.exp(np.clip(w, -20, 10))) @ V.T, float(np.linalg.norm(sol.fun))

    best_al = None
    max_S = 0.0
    for dgrid in [np.geomspace(dd2[1], 0.25, 65), np.geomspace(dd2[1], 1e-4, 35)]:
        Xc = X2.copy()
        for d1 in dgrid:
            Xc, err = solve_H_d(np.array([1.0, d1]), Xc)
            if err > 1e-10:
                break
            dd = np.array([1.0, d1])
            sD = np.sqrt(dd)
            D = np.diag(dd)
            H = (sD[:, None] * Xc) * sD[None, :]
            M = D + H
            G = (sD[:, None] * H) * sD[None, :]
            Z = (dd ** (-0.25))[:, None] * _o_matpow(G, 0.25) * (dd ** (-0.25))[None, :]
            Ehat = (dd ** (-1.25))[:, None] * _o_matpow(G, 1.25) * (dd ** (-1.25))[None, :] - Z
            Bsp = sp2 * np.eye(2) - Ehat
            T1 = (dd ** (-0.25))[:, None] * _o_matpow(M, 0.5) * (dd ** (-0.25))[None, :]
            T2 = (dd ** (-0.75))[:, None] * _o_matpow(G, 0.75) * (dd ** (-0.75))[None, :]
            gam0 = (1.0 + xm2) / L2
            K0 = sp2 * np.eye(2) - xm2 * Z + gam0 * np.linalg.inv(T1 - gam0 * T2)
            Vop = cV2 * (Xc - xm2 * np.eye(2)) / xp2
            S = K0 + Vop.T @ Bsp @ Vop
            evK, VK = eigh(0.5 * (K0 + K0.T))
            w_top = VK[:, -1]
            evB, VB = eigh(0.5 * (Bsp + Bsp.T))
            evS = float(np.linalg.eigvalsh(0.5 * (S + S.T))[-1])
            max_S = max(max_S, evS / cr2)
            if best_al is None or evK[-1] / cr2 > best_al[0]:
                Vw = Vop @ w_top
                cos2 = float((VB[:, 0] @ Vw) ** 2 / max(float(Vw @ Vw), 1e-30))
                best_al = (evK[-1] / cr2, evS / cr2, d1, evB[0] / sp2, float(w_top @ (K0 - cr2 * np.eye(2)) @ w_top), float(Vw @ Bsp @ Vw), cos2)
    assert best_al is not None and best_al[6] > 0.9999 and best_al[1] < 1.0
    print(
        f"  p=5/3 worst 2x2 Holden (d1={best_al[2]:.6f}): K0/cr={best_al[0]:.10f} -> (K0+V*BV)/cr={best_al[1]:.10f} "
        f"(global max S/cr={max_S:.10f}, crush={(best_al[0] - 1.0) / max(max_S - 1.0, 1e-16):.1f}x)"
    )
    print(
        f"  min(B_sp)/sp={best_al[3]:+.4f} | <w,(K0-crI)w>={best_al[4]:+.3e} | <Vw,B_sp Vw>={best_al[5]:+.3e} "
        f"| cos^2(V w, neg_eig(B_sp))={best_al[6]:.6f}"
    )


def main():
    t_all = time.perf_counter()
    print("=" * 100)
    print("MODULE 0: WHOLE-SECTION-B AST ZERO-FLOAT PURITY AUDIT & OUTWARD FORMATTER SELF-TESTS")
    print("=" * 100)
    n_fn, n_nodes = run_section_b_ast_audit()
    print(f"  [Module 0] AST Zero-Float Audit PASSED: {n_fn}/{n_fn} Section-B functions ({n_nodes:,d} AST nodes, 0 floats/banned refs)!")

    run_suite1_zero_float_p53_certifications()
    run_suite2_mtilde_2a_benchmark()
    run_suite3_attack2_analytic_and_obstructions()

    print("\n" + "=" * 100)
    print(f"ALL MODULES & SUITES (0, 1, 2, 3) PASSED 100% WITH ZERO ASSERTION FAILURES! (Total: {time.perf_counter() - t_all:.2f}s)")
    print("=" * 100)


if __name__ == "__main__":
    main()
