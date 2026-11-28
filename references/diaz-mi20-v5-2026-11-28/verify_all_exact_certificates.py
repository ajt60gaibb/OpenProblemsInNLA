#!/usr/bin/env python3
"""
verify_all_exact_certificates.py
================================
Author:      Marcio Díaz (Space Research AI, https://spaceresearch.ai, marcio.diaz@gmail.com)
Date:        November 28, 2026
Purpose:     100% ZERO-FLOATING-POINT, ZERO-EXTERNAL-DEPENDENCY master verifier for ALL
             exact rational certificates of Open Problem MI-20 (Version 5):
               - Suite 1 (Theorem 4): Small-integer 2x3 witnesses at p = 3/2, 4/3, 5/4
               - Suite 2 (Theorem 11): World-record 42x42 self-similar tree lower bounds
                   * C_{4/3,2}(inf) > 1.0183715755  (beats Holden's 1.018371575)
                   * C_{3/2,2}(inf) > 1.03643716806 (beats n=14 PSD 1.036437168055)
               - Suite 3 (Theorem 12): Unconditional Two-State Pinch upper-bound chains
                 (including convex-hull trapezoid certification via strict convexity of sigma_+)
                   * p = 4/3, m = 2: Lam <= 21511/2500 => C_{4/3,2}(inf) <= (21511/20000)^(1/4)
                                     = 1.0183748167... (52.1x tighter than Holden's 1.01854047)
                   * p = 3/2, m = 2: Lam <= 890677/200000 => C_{3/2,2}(inf) <= (890677/800000)^(1/3)
                                     = 1.0364382131... (7,795x tighter than Holden's 1.04458345)
               - Suite 4: Negative tamper tests & literal noncommuting rational matrix sanity check
               - Suite 5 (Theorem 17): Unconditional Continuous-Interval Zero-Float Bernstein
                 Multi-Summand World Records (m = 3, 4 at p = 4/3, 3/2; clearing V4 Thm 10B/10C):
                   * p = 4/3, m = 3 (d=5,  8 subintervals): C_{4/3,3}(inf) <= 1.0320685149 (4.26x)
                   * p = 4/3, m = 4 (d=5, 11 subintervals): C_{4/3,4}(inf) <= 1.0430768362 (4.06x)
                   * p = 3/2, m = 3 (d=7,  5 subintervals): C_{3/2,3}(inf) <= 1.0633400433 (5.91x)
                   * p = 3/2, m = 4 (d=7,  4 subintervals): C_{3/2,4}(inf) <= 1.0850902727 (4.36x)
               - Suite 6 (Theorem 22): Unconditional Zero-Float Full-V4-Enclosure Top-Band Exact
                 Reducing-Subspace Splitting P_top = P_1 (+) P_2 (m = 2 at p = 4/3 and p = 3/2):
                   * p = 4/3: full V4 enclosure [860425/100000, 21511/2500] (15 IV boxes)
                              => d_v < 20/73 on mu in [0, 1616/10000], d_v < 0.87601 on mu >= 1616/10000
                   * p = 3/2: full V4 enclosure [445337/100000, 890677/200000] (92 IV patches)
                              => d_v < 2/3 on mu in [0, 9/40], d_v < 0.8301 on mu >= 9/40

Invocation (strictly stdlib-only, no site-packages):
    python3 -B -S verify_all_exact_certificates.py

Every single mathematical decision uses exclusively Python's arbitrary-precision `int`
and `fractions.Fraction`. No `float` value ever enters any bound or assertion.
"""
from fractions import Fraction
import gzip
import json
import math
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))


# ==============================================================================
# Core Exact Rational Arithmetic Helpers (100% Zero-Float)
# ==============================================================================

def parse_frac(s: str) -> Fraction:
    return Fraction(s)


def nth_root_bounds(x: Fraction, n: int, prec_bits: int = 100):
    """Exact (lo, hi) Fractions with 0 <= lo and lo^n <= x <= hi^n."""
    assert x >= 0 and n >= 1
    if x == 0:
        return Fraction(0), Fraction(0)
    scale = 1 << prec_bits
    num_s = x.numerator * (scale ** n)
    den = x.denominator
    target = num_s // den
    if target == 0:
        s = 0
    elif n == 2:
        s = math.isqrt(target)
    else:
        bits = target.bit_length()
        s = 1 << ((bits + n - 1) // n)
        while True:
            s_next = ((n - 1) * s + target // (s ** (n - 1))) // n
            if s_next >= s:
                break
            s = s_next
    while ((s + 1) ** n) * den <= num_s:
        s += 1
    while (s ** n) * den > num_s:
        s -= 1
    lo = Fraction(s, scale)
    hi = lo if (s ** n) * den == num_s else Fraction(s + 1, scale)
    assert lo ** n <= x <= hi ** n
    return lo, hi


def bisect_increasing(f, lo: Fraction, hi: Fraction, iters: int = 90):
    """Exact rational bisection of strictly increasing f with f(lo) < 0 < f(hi)."""
    flo, fhi = f(lo), f(hi)
    assert flo < 0 < fhi, f"Bad bracket: f({lo})={flo}, f({hi})={fhi}"
    for _ in range(iters):
        mid = (lo + hi) / 2
        fmid = f(mid)
        if fmid == 0:
            return mid, mid
        if fmid < 0:
            lo, flo = mid, fmid
        else:
            hi, fhi = mid, fmid
    assert f(lo) <= 0 <= f(hi)
    return lo, hi


def exact_ldlt_is_pd(M):
    """Exact rational LDL^T check on symmetric matrix M of Fractions.
    Returns (True, min_pivot) iff M is strictly positive definite, else (False, bad_pivot)."""
    n = len(M)
    assert n > 0
    for i in range(n):
        assert len(M[i]) == n
        for j in range(i + 1, n):
            assert M[i][j] == M[j][i], f"Non-symmetric matrix entry ({i},{j})"
    L = [[Fraction(0)] * n for _ in range(n)]
    D = [Fraction(0)] * n
    for j in range(n):
        s = M[j][j]
        for k in range(j):
            s -= L[j][k] * L[j][k] * D[k]
        if s <= 0:
            return False, s
        D[j] = s
        L[j][j] = Fraction(1)
        for i in range(j + 1, n):
            s2 = M[i][j]
            for k in range(j):
                s2 -= L[i][k] * L[j][k] * D[k]
            L[i][j] = s2 / D[j]
    return True, min(D)


def fmt_dec(f: Fraction, digits: int = 12, round_up: bool = False) -> str:
    """Pure-integer decimal formatting for display (floor by default, ceil if round_up=True)."""
    neg = f < 0
    f = -f if neg else f
    scale = 10 ** digits
    q, rem = divmod(f.numerator * scale, f.denominator)
    if round_up and not neg and rem > 0:
        q += 1
    ip, fp = divmod(q, scale)
    return f"{'-' if neg else ''}{ip}.{fp:0{digits}d}"


# ==============================================================================
# Suite 1: Theorem 4 Small-Integer 2x3 Witnesses (p = 3/2, 4/3, 5/4)
# ==============================================================================

def verify_suite1_theorem4():
    print("=" * 78)
    print("SUITE 1: Theorem 4 Small-Integer 2x3 Witnesses (p = 3/2, 4/3, 5/4)")
    print("=" * 78)
    sys.path.insert(0, HERE)
    import verify_exact_certificates
    verify_exact_certificates.main()


# ==============================================================================
# Suite 2: Theorem 11 World-Record 42x42 Self-Similar Tree Lower Bounds
# ==============================================================================

def verify_one_lower_record(cert):
    K = cert['K']
    D = cert['scale_den']
    WD = cert['w_den']
    p_num = cert['p_num']
    p_den = cert['p_den']
    q = cert['q']
    assert q * (p_num - p_den) == p_num
    assert D > 0 and WD > 0 and K > 0
    target = Fraction(cert['target_num'], cert['target_den'])

    # 1. Verify exact disjoint block partition of {0, ..., K-1} for L1 and L2, build F_int (2K x K)
    F_int = [[0] * K for _ in range(2 * K)]
    for offset, key in [(0, 'L1_blocks'), (K, 'L2_blocks')]:
        seen = set()
        for blk in cert[key]:
            bidx = blk['idx']
            mat = blk['mat']
            m = len(bidx)
            assert len(mat) == m and all(len(row) == m for row in mat)
            for ii, i in enumerate(bidx):
                assert 0 <= i < K and i not in seen
                seen.add(i)
                for jj, j in enumerate(bidx):
                    assert isinstance(mat[ii][jj], int)
                    F_int[offset + i][j] = mat[ii][jj]
        assert len(seen) == K, f"{key} did not partition 0..{K-1}"

    r_int = cert['r_int']
    assert len(r_int) == 2 * K and all(isinstance(v, int) and v > 0 for v in r_int)

    # 2. Exact integer operator-norm bounds ||U1^T U1||_row <= 1 and ||V1^T V1||_row <= 1
    WD2 = WD * WD
    U1 = cert['U1_int']
    V1 = cert['V1_int']
    assert len(U1) == 2 * K and all(len(row) == K for row in U1)
    assert len(V1) == 2 * K and all(len(row) == K for row in V1)
    for name, M in [('U1', U1), ('V1', V1)]:
        for a in range(K):
            row_sum = 0
            for b in range(K):
                s = 0
                for t in range(2 * K):
                    s += M[t][a] * M[t][b]
                row_sum += abs(s)
            assert row_sum <= WD2, f"{name}^T {name} row {a} exceeds 1: {row_sum} > {WD2}"

    # 3. Exact integer numerator nu = tr((U1^T R F)(F^T V1)) <= ||R F F^T||_1
    nu_int = 0
    for a in range(K):
        for c in range(K):
            sa = 0
            sb = 0
            for t in range(2 * K):
                ftc = F_int[t][c]
                if ftc != 0:
                    sa += U1[t][a] * r_int[t] * ftc
                    sb += ftc * V1[t][a]
            nu_int += sa * sb
    assert nu_int > 0
    nu = Fraction(nu_int, WD2 * (D ** 3))

    # 4. Exact rational R_q = sum_i r_i^q
    Rq = Fraction(sum(v ** q for v in r_int), D ** q)

    # 5. Exact rational block-by-block polar/Weyl upper bound B_hi >= tr((L1 L1^T)^p) + tr((L2 L2^T)^p)
    B_hi = Fraction(0)
    D2 = D * D
    D3 = D * D * D
    for blocks, specs in [(cert['L1_blocks'], cert['spec1']), (cert['L2_blocks'], cert['spec2'])]:
        assert len(blocks) == len(specs)
        for blk, sp in zip(blocks, specs):
            mat = blk['mat']
            m = len(mat)
            Mb = [[sum(mat[i][t] * mat[j][t] for t in range(m)) for j in range(m)] for i in range(m)]
            if m == 1:
                lam_hi = Fraction(Mb[0][0], D2)
                assert lam_hi > 0
                _, p_hi = nth_root_bounds(lam_hi ** p_num, p_den, 90)
                B_hi += p_hi
            else:
                Z = sp['Z']
                E = sp['E']
                assert len(Z) == m and all(len(row) == m for row in Z) and len(E) == m
                assert all(isinstance(v, int) and v > 0 for v in E)
                # delta = ||Z^T Z - I||_row < 1 => polar factor V has ||Z - V||_op <= delta
                delta_int = 0
                for i in range(m):
                    rs = 0
                    for j in range(m):
                        s = sum(Z[t][i] * Z[t][j] for t in range(m)) - (D2 if i == j else 0)
                        rs += abs(s)
                    if rs > delta_int:
                        delta_int = rs
                delta = Fraction(delta_int, D2)
                assert delta < 1, f"delta >= 1"
                # e0 = ||M_b - Z E Z^T||_row
                e0_int = 0
                for i in range(m):
                    rs = 0
                    for j in range(m):
                        zez = sum(Z[i][k] * E[k] * Z[j][k] for k in range(m))
                        rs += abs(Mb[i][j] * D - zez)
                    if rs > e0_int:
                        e0_int = rs
                e0 = Fraction(e0_int, D3)
                E_max = Fraction(max(E), D)
                eta = e0 + delta * (2 + delta) * E_max
                for k in range(m):
                    lam_hi = Fraction(E[k], D) + eta
                    assert lam_hi > 0
                    _, p_hi = nth_root_bounds(lam_hi ** p_num, p_den, 90)
                    B_hi += p_hi

    # 6. Exact rational decision inequality: nu^q > target^q * Rq * B_hi^(q - 1)
    lhs = nu ** q
    rhs = (target ** q) * Rq * (B_hi ** (q - 1))
    assert lhs > rhs, f"Lower-bound certificate FAILED for {cert['label']}"
    ratio_q = lhs / (Rq * (B_hi ** (q - 1)))
    ratio_lo, _ = nth_root_bounds(ratio_q, q, 60)
    assert ratio_lo > target
    return target, ratio_lo


def verify_suite2_lower_records():
    print("\n" + "=" * 78)
    print("SUITE 2: Theorem 11 World-Record 42x42 Lower-Bound Certificates (Zero-Float)")
    print("=" * 78)
    path = os.path.join(HERE, "lower_record_certificates.json")
    with open(path, 'r') as f:
        data = json.load(f)
    for key in ['p43_record', 'p32_record']:
        cert = data[key]
        target, ratio_lo = verify_one_lower_record(cert)
        print(f"  [PASS] {cert['label']}")
        print(f"         Certified C > {fmt_dec(target, 12)} (exact rational lower bound >= {fmt_dec(ratio_lo, 14)})")
    return data


# ==============================================================================
# Suite 3: Theorem 12 Unconditional Two-State Pinch Upper-Bound Chains
# ==============================================================================

def strip_D(w: str) -> str:
    i, j = 0, len(w)
    while i < j and w[i] == 'D':
        i += 1
    while j > i and w[j - 1] == 'D':
        j -= 1
    return w[i:j]


def canon(w: str) -> str:
    s = strip_D(w)
    sr = s[::-1]
    return s if s <= sr else sr


def sigma_plus_bounds_p43(L: Fraction):
    """Exact rational bracket (sig_lo, sig_hi, slope_lo) for sigma_+(L) = h_+(L)^2 - h_+(L)
    and its derivative sigma_+'(L) = (h_+(L) / (1 + h_+(L)))^2 at p = 4/3 (kappa = 2),
    where h_+(L) > 1/2 is the unique root of (1 + h)^3 - L * h = 0 on (1/2, inf).
    Since h -> h/(1+h) is strictly increasing, sigma_+(L) is strictly convex in L."""
    f = lambda h: (1 + h) ** 3 - L * h
    hi = Fraction(2)
    while f(hi) <= 0:
        hi *= 2
    h_lo, h_hi = bisect_increasing(f, Fraction(1, 2), hi, 90)
    assert h_lo >= Fraction(1, 2)
    slope_lo = (h_lo / (1 + h_lo)) ** 2
    return h_lo * h_lo - h_lo, h_hi * h_hi - h_hi, slope_lo


def sigma_plus_bounds_p32(L: Fraction):
    """Exact rational bracket (sig_lo, sig_hi, slope_lo) for sigma_+(L) = m_+(L)^3 - m_+(L)
    and its derivative sigma_+'(L) = m_+(L)^2 / (1 + m_+(L)^2) at p = 3/2 (kappa = 3/2),
    where m_+(L) = sqrt(h_+(L)) > 1 is the unique root of (1 + m^2)^2 - L * m = 0 on (1, inf).
    Since m -> m^2/(1+m^2) is strictly increasing, sigma_+(L) is strictly convex in L."""
    f = lambda m: (1 + m * m) ** 2 - L * m
    assert L > 4 and L < 8
    hi = Fraction(2)
    while f(hi) <= 0:
        hi *= 2
    m_lo, m_hi = bisect_increasing(f, Fraction(1), hi, 90)
    assert m_lo >= Fraction(1)
    slope_lo = (m_lo * m_lo) / (1 + m_lo * m_lo)
    return m_lo ** 3 - m_lo, m_hi ** 3 - m_hi, slope_lo


def allowed_localizers_p43(tau_bar: Fraction, h_bar: Fraction, use_D_le_I: bool):
    F1, Fm1 = Fraction(1), Fraction(-1)
    allowed = {
        'M0': [(F1, '')],
        'D': [(F1, 'D')],
        'H': [(F1, 'H')],
        'hD-H': [(h_bar, 'D'), (Fm1, 'H')],
        'tauD3-Phi': [(tau_bar, 'DDD'), (Fm1, 'HDH'), (F1, 'DHD')],
        'tauD3+Phi': [(tau_bar, 'DDD'), (F1, 'HDH'), (Fm1, 'DHD')],
        'D(tauD3-Phi)': [(tau_bar, 'DDDD'), (Fm1, 'DHDH'), (F1, 'DDHD')],
        'D(tauD3+Phi)': [(tau_bar, 'DDDD'), (F1, 'DHDH'), (Fm1, 'DDHD')],
        'tau2D6-Phi2': [
            (tau_bar * tau_bar, 'DDDDDD'), (Fm1, 'HDHHDH'),
            (F1, 'HDHDHD'), (F1, 'DHDHDH'), (Fm1, 'DHDDHD')
        ],
    }
    if use_D_le_I:
        allowed['I-D'] = [(F1, ''), (Fm1, 'D')]
        allowed['D(I-D)'] = [(F1, 'D'), (Fm1, 'DD')]
        allowed['(I-D)(tauD3-Phi)'] = [
            (tau_bar, 'DDD'), (-tau_bar, 'DDDD'), (Fm1, 'HDH'),
            (F1, 'DHD'), (F1, 'DHDH'), (Fm1, 'DDHD')
        ]
        # Valid unconditionally in State 1: 0 < D <= I => D(I-D) >= 0 commutes with tau D^3 - Phi >= 0.
        allowed['D(I-D)(tauD3-Phi)'] = [
            (tau_bar, 'DDDD'), (-tau_bar, 'DDDDD'), (Fm1, 'DHDH'),
            (F1, 'DDHD'), (F1, 'DDHDH'), (Fm1, 'DDDHD')
        ]
    return allowed


def allowed_localizers_p32(tau_bar: Fraction, m_bar: Fraction, use_D_le_I: bool):
    F1, Fm1 = Fraction(1), Fraction(-1)
    allowed = {
        'M0': [(F1, '')],
        'D': [(F1, 'D')],
        'M': [(F1, 'M')],
        'mI-M': [(m_bar, ''), (Fm1, 'M')],
        'tauD2-Phi': [(tau_bar, 'DD'), (Fm1, 'MDMDM'), (F1, 'DMD')],
        'tauD2+Phi': [(tau_bar, 'DD'), (F1, 'MDMDM'), (Fm1, 'DMD')],
        'D(tauD2-Phi)': [(tau_bar, 'DDD'), (Fm1, 'DMDMDM'), (F1, 'DDMD')],
        'D(tauD2+Phi)': [(tau_bar, 'DDD'), (F1, 'DMDMDM'), (Fm1, 'DDMD')],
    }
    if use_D_le_I:
        allowed['I-D'] = [(F1, ''), (Fm1, 'D')]
        allowed['D(I-D)'] = [(F1, 'D'), (Fm1, 'DD')]
        allowed['(I-D)(tauD2-Phi)'] = [
            (tau_bar, 'DD'), (-tau_bar, 'DDD'), (Fm1, 'MDMDM'),
            (F1, 'DMD'), (F1, 'DMDMDM'), (Fm1, 'DDMD')
        ]
    return allowed


def verify_pinch_rectangle(rect, mode: str):
    """Independently verify a single 4-corner SOS refutation rectangle with 0 floats."""
    assert mode in ('p43', 'p32')
    F1, Fm1 = Fraction(1), Fraction(-1)
    L_lo = parse_frac(rect['L_lo'])
    L_hi = parse_frac(rect['L_hi'])
    P_lo = parse_frac(rect['P_lo'])
    P_hi = parse_frac(rect['P_hi'])
    tau_bar = parse_frac(rect['tau_bar'])
    bound_bar = parse_frac(rect['bound_bar'])
    c0 = parse_frac(rect['c0'])
    use_D_le_I = bool(rect['use_D_le_I'])
    assert L_lo < L_hi and P_lo <= P_hi and c0 > 0 and tau_bar > 0

    # 1. Verify unconditional spectral bound_bar > h_+(L_hi) (p=4/3) or sqrt(h_+(L_hi)) (p=3/2),
    #    and verify exact relation between tau_bar and P_hi!
    if mode == 'p43':
        assert rect['ch1'] == 'H'
        assert bound_bar > Fraction(1, 2)
        assert (1 + bound_bar) ** 3 > L_hi * bound_bar, "bound_bar does not strictly exceed h_+(L_hi)"
        allowed = allowed_localizers_p43(tau_bar, bound_bar, use_D_le_I)
        g_base = [(F1, 'DDD'), (F1, 'DDH'), (F1, 'DHD'), (F1, 'HDD'),
                  (F1, 'DHH'), (F1, 'HDH'), (F1, 'HHD'), (F1, 'HHH')]
        g_lam_word = 'DHD'
        phi_base = [(F1, 'HDH'), (Fm1, 'DHD')]
        comm_terms = [(F1, 'DHDH'), (Fm1, 'DDHD'), (Fm1, 'HDHD'), (F1, 'DHDD')]
        alphabet = {'D', 'H'}
    else:
        assert rect['ch1'] == 'M'
        assert bound_bar > Fraction(1)
        assert (1 + bound_bar * bound_bar) ** 2 > L_hi * bound_bar, "bound_bar does not strictly exceed sqrt(h_+(L_hi))"
        allowed = allowed_localizers_p32(tau_bar, bound_bar, use_D_le_I)
        g_base = [(F1, 'DD'), (F1, 'DMDM'), (F1, 'MDMD'), (F1, 'MDMMDM')]
        g_lam_word = 'DMD'
        phi_base = [(F1, 'MDMDM'), (Fm1, 'DMD')]
        comm_terms = [(F1, 'DMDMDM'), (Fm1, 'DDMD'), (Fm1, 'MDMDMD'), (F1, 'DMDD')]
        alphabet = {'D', 'M'}

    # If Sys2 (use_D_le_I = False), tau = P <= P_hi <= tau_bar is required!
    if not use_D_le_I:
        assert tau_bar >= P_hi, f"Sys2 requires tau_bar >= P_hi ({tau_bar} < {P_hi})"

    # 2. Validate every Q_def against the exact mathematical localizer whitelist!
    Q_parsed = []
    for qd in rect['Q_defs']:
        nm = qd['name']
        assert nm in allowed, f"Unauthorized localizer {nm} in {rect['label']}"
        terms_got = [(parse_frac(c), w) for c, w in qd['terms']]
        assert terms_got == allowed[nm], f"Tampered localizer terms for {nm} in {rect['label']}"
        basis = qd['basis']
        assert all(set(w) <= alphabet for w in basis)
        m = len(basis)
        P_spec = qd['P']
        if P_spec == 'I':
            P_mat = [[Fraction(1 if i == j else 0) for j in range(m)] for i in range(m)]
        else:
            P_mat = [[parse_frac(v) for v in row] for row in P_spec]
            assert len(P_mat) > 0 and all(len(row) == m for row in P_mat)
        # Precompute exact localizer monomial map (i, j) -> list of (coeff, canon_word)
        r = len(P_mat)
        # First build M_f[vi] on original basis, then project PMP = P M P^T
        raw_map = {}
        for i, u in enumerate(basis):
            for j, v in enumerate(basis):
                for c_q, qw in terms_got:
                    cw = canon(u[::-1] + qw + v)
                    if cw not in raw_map:
                        raw_map[cw] = [[Fraction(0)] * m for _ in range(m)]
                    raw_map[cw][i][j] += c_q
        proj_map = {}
        for cw, mat in raw_map.items():
            # Symmetrize (valid since state Re(omega(w)) = Re(omega(w^rev)) and Z is symmetric)
            sym = [[(mat[i][j] + mat[j][i]) / 2 for j in range(m)] for i in range(m)]
            if P_spec == 'I':
                proj_map[cw] = sym
            else:
                pm = [[sum(P_mat[a][i] * sym[i][j] for i in range(m) if P_mat[a][i] != 0 and sym[i][j] != 0)
                       for j in range(m)] for a in range(r)]
                pmp = [[sum(pm[a][j] * P_mat[b][j] for j in range(m) if pm[a][j] != 0 and P_mat[b][j] != 0)
                        for b in range(r)] for a in range(r)]
                if any(pmp[a][b] != 0 for a in range(r) for b in range(r)):
                    proj_map[cw] = pmp
        Q_parsed.append((nm, r, proj_map))

    # 3. Parse shared multipliers (c_g, c_p) and validate words
    g_pairs = rect['g_pairs']
    phi_ws = rect['phi_ws']
    comm_pairs = rect['comm_pairs']
    c_g = [parse_frac(v) for v in rect['c_g']]
    c_p = [parse_frac(v) for v in rect['c_p']]
    assert len(c_g) == len(g_pairs) and len(c_p) == len(phi_ws)
    for u, v in g_pairs:
        assert set(u) <= alphabet and set(v) <= alphabet
    for v in phi_ws:
        assert set(v) <= alphabet
    for u, v in comm_pairs:
        assert set(u) <= alphabet and set(v) <= alphabet

    # 4. Verify all 4 corners (rectangle or convex trapezoid) are present and EXACTLY pass
    #    both zero polynomial residual AND exact rational LDL^T > 0!
    if 'trapezoid_P' in rect:
        P_lo_L, P_hi_L, P_lo_R, P_hi_R = [parse_frac(v) for v in rect['trapezoid_P']]
        assert P_lo_L <= P_hi_L and P_lo_R <= P_hi_R
        assert use_D_le_I, "Convex trapezoid hull is used exclusively for State-1 curve P = sigma_+(L)"
        trap_P = (P_lo_L, P_hi_L, P_lo_R, P_hi_R)
        req_corners = set([(L_lo, P_lo_L), (L_lo, P_hi_L), (L_hi, P_lo_R), (L_hi, P_hi_R)])
    else:
        trap_P = (P_lo, P_hi, P_lo, P_hi)
        req_corners = set([(L_lo, P_lo), (L_lo, P_hi), (L_hi, P_lo), (L_hi, P_hi)])
    seen_corners = set()
    min_piv = None
    for corner in rect['corners']:
        L_c = parse_frac(corner['L'])
        P_c = parse_frac(corner['P'])
        seen_corners.add((L_c, P_c))
        c_cm = [parse_frac(v) for v in corner['c_cm']]
        assert len(c_cm) == len(comm_pairs)

        # Accumulate LHS = sum_s <Z_s, Q_s> + c0 - RHS_g(L_c) - RHS_p(P_c) - RHS_cm
        poly = {'': c0}

        Z_dict = corner['Z']
        assert set(Z_dict.keys()) == set(nm for nm, _, _ in Q_parsed), f"Z keys mismatch in {rect['label']}"
        for nm, r, proj_map in Q_parsed:
            Z = [[parse_frac(v) for v in row] for row in Z_dict[nm]]
            assert len(Z) == r
            ok_pd, piv = exact_ldlt_is_pd(Z)
            assert ok_pd, f"Gram matrix {nm} NOT strictly PD at corner ({L_c},{P_c}) in {rect['label']} (piv={piv})"
            if min_piv is None or piv < min_piv:
                min_piv = piv
            for cw, mat in proj_map.items():
                acc = Fraction(0)
                for a in range(r):
                    za = Z[a]
                    ma = mat[a]
                    for b in range(r):
                        if za[b] != 0 and ma[b] != 0:
                            acc += za[b] * ma[b]
                if acc != 0:
                    poly[cw] = poly.get(cw, Fraction(0)) + acc

        # Subtract shared power-system identity terms: c_g[j] * u * (g_base - L_c * g_lam_word) * v
        for coeff, (u, v) in zip(c_g, g_pairs):
            if coeff == 0:
                continue
            for c_gb, gw in g_base:
                cw = canon(u + gw + v)
                poly[cw] = poly.get(cw, Fraction(0)) - coeff * c_gb
            cw_l = canon(u + g_lam_word + v)
            poly[cw_l] = poly.get(cw_l, Fraction(0)) + coeff * L_c

        # Subtract shared eigenstate flux identity terms: c_p[k] * (Phi + P_c * D^e) * w
        # Note: since D v = v, D^e w has the same canonical word as w (strip_D strips leading D's!).
        for coeff, w in zip(c_p, phi_ws):
            if coeff == 0:
                continue
            for c_pb, pw in phi_base:
                cw = canon(pw + w)
                poly[cw] = poly.get(cw, Fraction(0)) - coeff * c_pb
            cw_p = canon(w)
            poly[cw_p] = poly.get(cw_p, Fraction(0)) - coeff * P_c

        # Subtract corner commutator terms: c_cm[l] * u * [D, Phi] * v
        for coeff, (u, v) in zip(c_cm, comm_pairs):
            if coeff == 0:
                continue
            for c_cmw, cmw in comm_terms:
                cw = canon(u + cmw + v)
                poly[cw] = poly.get(cw, Fraction(0)) - coeff * c_cmw

        # EXACT ZERO RESIDUAL ON EVERY SINGLE CANONICAL WORD!
        for cw, val in poly.items():
            assert val == 0, f"NONZERO RESIDUAL {val} on word '{cw}' at ({L_c},{P_c}) in {rect['label']}!"

    assert req_corners <= seen_corners, f"Missing corners in {rect['label']}"
    return L_lo, L_hi, P_lo, P_hi, tau_bar, use_D_le_I, trap_P, min_piv


def verify_interval_coverage(rects_meta, start_cap: Fraction, final_cap: Fraction,
                             c_kap_hi: Fraction, sigma_fn, mode_name: str):
    """Verify with 100% exact rationals that the rectangles/trapezoids seamlessly refute ALL
    (Lam, tau) with Lam in [final_cap, start_cap] and tau in [sigma_+(Lam), c_kap_hi]."""
    # Group pieces by their exact Lambda interval [L_lo, L_hi]
    by_L = {}
    for L_lo, L_hi, P_lo, P_hi, tau_bar, use_D, trap_P in rects_meta:
        by_L.setdefault((L_lo, L_hi), []).append((P_lo, P_hi, tau_bar, use_D, trap_P))

    # 1. Verify Lambda intervals form a contiguous cover of [final_cap, start_cap]
    L_intervals = sorted(by_L.keys())
    assert L_intervals[0][0] <= final_cap, f"{mode_name}: bottom {L_intervals[0][0]} > {final_cap}"
    cur_L = L_intervals[0][0]
    for a, b in L_intervals:
        assert a <= cur_L, f"{mode_name}: GAP in Lambda between {cur_L} and {a}!"
        if b > cur_L:
            cur_L = b
    assert cur_L >= start_cap, f"{mode_name}: top {cur_L} < start_cap {start_cap}"

    # 2. On EVERY Lambda interval [L_lo, L_hi], verify exact (State 1 + State 2) coverage of tau in [sigma_+(Lam), c_kap_hi]!
    for (L_lo, L_hi), pieces in L_intervals_with_pieces(L_intervals, by_L):
        sig_lo_min, sig_lo_max, slope_lo_min = sigma_fn(L_lo)
        _, sig_hi_max, _ = sigma_fn(L_hi)
        sys1 = [p for p in pieces if p[3]]      # use_D_le_I = True
        sys2 = [p for p in pieces if not p[3]]  # use_D_le_I = False

        if sys1:
            # Sys1 convex quadrilateral conv{(L_lo, P_lo_L), (L_lo, P_hi_L), (L_hi, P_lo_R), (L_hi, P_hi_R)}
            # must contain the ENTIRE graph {(L, sigma_+(L)) : L in [L_lo, L_hi]}.
            # Because sigma_+(L) is strictly convex (sigma_+'(L) = (h_+/(1+h_+))^(2k-2) is strictly increasing):
            #   - Upper secant edge >= sigma_+(L)  <==  P_hi_L >= sig_lo_max and P_hi_R >= sig_hi_max
            #   - Lower edge <= supporting tangent <= sigma_+(L)  <==  P_lo_L <= sig_lo_min
            #     and P_lo_R <= P_lo_L + slope_lo_min * (L_hi - L_lo).
            tau_split = None
            for P_lo, P_hi, tau_bar, _, trap_P in sys1:
                P_lo_L, P_hi_L, P_lo_R, P_hi_R = trap_P
                assert P_lo_L <= sig_lo_min, (
                    f"{mode_name} [{L_lo},{L_hi}]: Sys1 P_lo_L={P_lo_L} > sig_lo_min={fmt_dec(sig_lo_min,10)}"
                )
                assert sig_lo_max <= P_hi_L, (
                    f"{mode_name} [{L_lo},{L_hi}]: Sys1 P_hi_L={P_hi_L} < sig_lo_max={fmt_dec(sig_lo_max,10)}"
                )
                assert sig_hi_max <= P_hi_R, (
                    f"{mode_name} [{L_lo},{L_hi}]: Sys1 P_hi_R={P_hi_R} < sig_hi_max={fmt_dec(sig_hi_max,10)}"
                )
                assert P_lo_R <= P_lo_L + slope_lo_min * (L_hi - L_lo), (
                    f"{mode_name} [{L_lo},{L_hi}]: Sys1 P_lo_R={P_lo_R} exceeds lower supporting tangent!"
                )
                tau_split = tau_bar if tau_split is None else max(tau_split, tau_bar)
            # Sys2 pieces must seamlessly cover [tau_split, c_kap_hi]
            tau_need_lo = tau_split
        else:
            # Pure Sys2 stage: must seamlessly cover ALL tau in [sigma_+(L_lo), c_kap_hi]
            tau_need_lo = sig_lo_min

        sys2_sorted = sorted(sys2, key=lambda x: x[0])
        assert len(sys2_sorted) > 0, f"{mode_name} [{L_lo},{L_hi}]: missing Sys2 coverage!"
        assert sys2_sorted[0][0] <= tau_need_lo, (
            f"{mode_name} [{L_lo},{L_hi}]: Sys2 starts at {sys2_sorted[0][0]} > needed {fmt_dec(tau_need_lo,8)}"
        )
        cur_tau = sys2_sorted[0][0]
        for P_lo, P_hi, tau_bar, _, _ in sys2_sorted:
            assert P_lo <= cur_tau, f"{mode_name} [{L_lo},{L_hi}]: GAP in tau between {cur_tau} and {P_lo}!"
            assert tau_bar >= P_hi
            if P_hi > cur_tau:
                cur_tau = P_hi
        assert cur_tau >= c_kap_hi, f"{mode_name} [{L_lo},{L_hi}]: Sys2 ends at {cur_tau} < c_kap_hi={c_kap_hi}!"


def L_intervals_with_pieces(L_intervals, by_L):
    return [(iv, by_L[iv]) for iv in L_intervals]


def verify_suite3_upper_bounds():
    print("\n" + "=" * 78)
    print("SUITE 3: Theorem 12 Unconditional Two-State Pinch Upper Bounds (Zero-Float)")
    print("=" * 78)

    # Verify exact integer starting caps from Theorem 10 (Lean 4 verified!)
    # 1) p = 4/3, m = 2: Lam <= (13 + 16*sqrt(2))/4 < 891/100  <=>  (16*sqrt(2)*25)^2 < (891 - 325)^2
    assert (16 * 25) ** 2 * 2 < (891 - 325) ** 2  # 320000 < 320356
    #    c_2 = (2-1)^1 / 2^2 = 1/4
    c_kap_43_hi = Fraction(1, 4)

    # 2) p = 3/2, m = 2: Lam <= 49*sqrt(3)/18 < 472/100  <=>  (49*100)^2 * 3 < (472*18)^2
    assert (49 * 100) ** 2 * 3 < (472 * 18) ** 2  # 72030000 < 72182016
    #    c_{3/2} = (1/2)^(1/2) / (3/2)^(3/2) = 2 / (3*sqrt(3)) < 385/1000 <=> 4*1000^2 < 27*385^2
    assert 4 * (1000 ** 2) < 27 * (385 ** 2)      # 4000000 < 4002075
    c_kap_32_hi = Fraction(385, 1000)

    print("  [PASS] Theorem 10 exact integer starting caps & c_kappa bounds:")
    print("         p=4/3: (13+16*sqrt(2))/4 < 891/100 (320000 < 320356), c_2 = 1/4")
    print("         p=3/2: 49*sqrt(3)/18     < 472/100 (72030000 < 72182016), c_{3/2} < 385/1000 (4000000 < 4002075)")

    path = os.path.join(HERE, "upper_bound_certificates.json")
    with open(path, 'r') as f:
        data = json.load(f)

    # Verify p = 4/3 chain
    p43 = data['p43']
    assert parse_frac(p43['start_cap']) == Fraction(891, 100)
    final_43 = parse_frac(p43['final_cap'])
    meta_43 = []
    print(f"\n  --- Chain A: p = 4/3, m = 2 (start={p43['start_cap']} -> final={p43['final_cap']}) ---")
    for rect in p43['rectangles']:
        L_lo, L_hi, P_lo, P_hi, tb, useD, tp, mp = verify_pinch_rectangle(rect, 'p43')
        meta_43.append((L_lo, L_hi, P_lo, P_hi, tb, useD, tp))
        print(f"    [PASS] {rect['label']:44s} | 0 residual | min_LDL_piv={fmt_dec(mp, 10)}")
    verify_interval_coverage(meta_43, Fraction(891, 100), final_43, c_kap_43_hi, sigma_plus_bounds_p43, "p43")
    _, C43_hi = nth_root_bounds(final_43 / 8, 4, 70)
    print(f"  [PASS] p = 4/3 seamless coverage verified: Lam <= {final_43} => C_{{4/3,2}}(inf) <= {fmt_dec(C43_hi, 12, round_up=True)}")

    # Verify p = 3/2 chain
    p32 = data['p32']
    assert parse_frac(p32['start_cap']) == Fraction(472, 100)
    final_32 = parse_frac(p32['final_cap'])
    meta_32 = []
    print(f"\n  --- Chain B: p = 3/2, m = 2 (start={p32['start_cap']} -> final={p32['final_cap']}) ---")
    for rect in p32['rectangles']:
        L_lo, L_hi, P_lo, P_hi, tb, useD, tp, mp = verify_pinch_rectangle(rect, 'p32')
        meta_32.append((L_lo, L_hi, P_lo, P_hi, tb, useD, tp))
        print(f"    [PASS] {rect['label']:44s} | 0 residual | min_LDL_piv={fmt_dec(mp, 10)}")
    verify_interval_coverage(meta_32, Fraction(472, 100), final_32, c_kap_32_hi, sigma_plus_bounds_p32, "p32")
    _, C32_hi = nth_root_bounds(final_32 / 4, 3, 70)
    print(f"  [PASS] p = 3/2 seamless coverage verified: Lam <= {final_32} => C_{{3/2,2}}(inf) <= {fmt_dec(C32_hi, 12, round_up=True)}")

    return data


# ==============================================================================
# Suite 4: Negative Tamper Tests & Noncommuting Rational Matrix Sanity Check
# ==============================================================================

def verify_suite4_tamper_and_algebra(upper_data, lower_data):
    print("\n" + "=" * 78)
    print("SUITE 4: Negative Tamper Tests & Noncommuting Matrix Algebra Sanity Check")
    print("=" * 78)

    # 4a. Tamper with a Gram entry in upper certificate -> MUST FAIL!
    bad_rect = json.loads(json.dumps(upper_data['p43']['rectangles'][0]))
    bad_rect['corners'][0]['Z']['M0'][0][0] = str(parse_frac(bad_rect['corners'][0]['Z']['M0'][0][0]) + Fraction(1, 10**12))
    failed = False
    try:
        verify_pinch_rectangle(bad_rect, 'p43')
    except AssertionError:
        failed = True
    assert failed, "Tampered Gram entry was NOT caught!"

    # 4b. Tamper with a localizer definition -> MUST FAIL!
    bad_rect2 = json.loads(json.dumps(upper_data['p32']['rectangles'][0]))
    bad_rect2['Q_defs'][0]['terms'] = [['2', '']]
    failed = False
    try:
        verify_pinch_rectangle(bad_rect2, 'p32')
    except AssertionError:
        failed = True
    assert failed, "Tampered localizer terms were NOT caught!"

    # 4c. Tamper with a lower-bound target to exceed the achievable value -> MUST FAIL!
    bad_low = json.loads(json.dumps(lower_data['p43_record']))
    bad_low['target_num'] = 1019
    bad_low['target_den'] = 1000
    failed = False
    try:
        verify_one_lower_record(bad_low)
    except AssertionError:
        failed = True
    assert failed, "Inflated lower-bound target was NOT caught!"

    # 4d. Tamper with a State-1 trapezoid lower-right tangent corner -> MUST FAIL!
    bad_meta = [(
        Fraction(4453385, 1000000), Fraction(44536, 10000),
        Fraction(2382, 10000), Fraction(2384, 10000), Fraction(2395, 10000), True,
        (Fraction(23823, 100000), Fraction(23824, 100000), Fraction(23840, 100000), Fraction(23840, 100000))
    )]
    failed = False
    try:
        verify_interval_coverage(bad_meta, Fraction(44536, 10000), Fraction(4453385, 1000000),
                                 Fraction(385, 1000), sigma_plus_bounds_p32, "tamper_trap")
    except AssertionError:
        failed = True
    assert failed, "Tampered convex trapezoid tangent bound was NOT caught!"

    # 4e. Literal noncommuting 2x2 rational matrix sanity check of canon(w) on D v = v
    D = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1, 3)]]
    H = [[Fraction(2, 5), Fraction(1, 7)], [Fraction(1, 7), Fraction(3, 11)]]
    v = [Fraction(1), Fraction(0)]  # exact eigenvector D v = v!
    def mm(A, B):
        return [[A[i][0]*B[0][j] + A[i][1]*B[1][j] for j in range(2)] for i in range(2)]
    def eval_word(w):
        M = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)]]
        for ch in w:
            M = mm(M, D if ch == 'D' else H)
        return sum(v[i] * sum(M[i][j] * v[j] for j in range(2)) for i in range(2))
    for w in ['', 'D', 'DDH', 'HD', 'DHHD', 'HDH', 'DHDH', 'HDHD', 'DDHDH']:
        assert eval_word(w) == eval_word(canon(w)), f"canon failed on literal matrices for '{w}'"

    print("  [PASS] All 4 negative tamper tests caught immediately!")
    print("  [PASS] Literal 2x2 noncommuting rational matrix check of canon(w) on D v = v passed!")


# ==============================================================================
# Suite 5: Theorem 17 Unconditional Continuous-Interval Zero-Float Bernstein
#          Multi-Summand World Records (m = 3, 4 at p = 4/3, 3/2)
# ==============================================================================

def s5_bernstein_matrix_verified(D: int, E: int):
    """Build exact rational M[j][r] and self-verify sum_j M[j][r] B_j^E(s) == (2s - 1)^r in Q[s]."""
    assert E >= D >= 0
    M = [[Fraction(0)] * (D + 1) for _ in range(E + 1)]
    for r in range(D + 1):
        for j in range(E + 1):
            a_lo = max(0, j - (E - r))
            a_hi = min(r, j)
            num = 0
            for a in range(a_lo, a_hi + 1):
                sign = -1 if ((r - a) & 1) else 1
                num += sign * math.comb(r, a) * math.comb(E - r, j - a)
            M[j][r] = Fraction(num, math.comb(E, j))
        lhs_s = [Fraction(0)] * (E + 1)
        for k in range(r + 1):
            lhs_s[k] = Fraction(((-1) ** (r - k)) * (2 ** k) * math.comb(r, k))
        rhs_s = [Fraction(0)] * (E + 1)
        for j in range(E + 1):
            coef_j = M[j][r] * math.comb(E, j)
            for t in range(E - j + 1):
                rhs_s[j + t] += coef_j * Fraction(((-1) ** t) * math.comb(E - j, t))
        assert lhs_s == rhs_s, f"Bernstein identity self-check failed at r={r}"
    return M


def s5_reduce_word(w: str) -> str:
    while True:
        w2 = w.replace('PP', 'P').replace('DP', 'PD')
        if w2 == w:
            return w2
        w = w2


def s5_canon_tracial(w: str) -> str:
    w = s5_reduce_word(w)
    if not w:
        return ''
    n = len(w)
    best = None
    for s in (w, w[::-1]):
        for k in range(n):
            rot = s5_reduce_word(s[k:] + s[:k])
            if best is None or rot < best:
                best = rot
    return best


def s5_gen_words_K(d_cnt: int, max_k: int, max_p: int = 1, exclude_pure_D: bool = False):
    res = set()

    def dfs(w, dc, kc, pc):
        if dc == d_cnt:
            rw = s5_reduce_word(w)
            if not (exclude_pure_D and ('K' not in rw) and ('P' not in rw)):
                res.add(rw)
        if dc < d_cnt:
            dfs(w + 'D', dc + 1, kc, pc)
        if kc < max_k:
            dfs(w + 'K', dc, kc + 1, pc)
        if pc < max_p:
            if not w or w[-1] == 'K':
                dfs(w + 'P', dc, kc, pc + 1)

    dfs('', 0, 0, 0)
    return sorted(res, key=lambda s: (s.count('K'), len(s), s))


def s5_p_add(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else Fraction(0)) + (b[i] if i < len(b) else Fraction(0)) for i in range(n)]


def s5_p_mul(a, b):
    res = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            if bj == 0:
                continue
            res[i + j] += ai * bj
    return res


def s5_p_scale(c, a):
    return [c * x for x in a]


def s5_mul_nc(p1, p2):
    d = {}
    for c1, w1 in p1:
        for c2, w2 in p2:
            w = s5_reduce_word(w1 + w2)
            pr = s5_p_mul(c1, c2)
            d[w] = s5_p_add(d[w], pr) if w in d else pr
    return [(c, w) for w, c in d.items() if any(x != 0 for x in c)]


def s5_add_nc(*polys):
    d = {}
    for p in polys:
        for c, w in p:
            w2 = s5_reduce_word(w)
            d[w2] = s5_p_add(d[w2], c) if w2 in d else list(c)
    return [(c, w) for w, c in d.items() if any(x != 0 for x in c)]


def s5_rebuild_delta_p43(h0: Fraction, h_hi: Fraction, m: int, deg: int):
    F = Fraction
    hp_d = [h0, F(1)]
    t_d = [F(1) + h0, F(1)]
    t2_d = s5_p_mul(t_d, t_d)
    hpt2_d = s5_p_mul(hp_d, t2_d)
    hpt_d = s5_p_mul(hp_d, t_d)
    sp_d = s5_p_add(s5_p_mul(hp_d, hp_d), s5_p_scale(F(-1), hp_d))
    one_d = [F(1)]
    mone_d = [F(-1)]

    g_terms = [
        (s5_p_scale(F(-1), hpt2_d), 'KDD'), (s5_p_scale(F(-1), hpt2_d), 'DDK'),
        (t2_d, 'DKD'),
        (hpt_d, 'KDKD'), (hpt_d, 'KDDK'), (hpt_d, 'DKDK'),
        (s5_p_scale(F(-1), hp_d), 'KDKDK'),
    ]
    D_p = [(one_d, 'D')]
    dPhi = [(hp_d, 'KDD'), (hp_d, 'DDK'), (mone_d, 'DKD'), (mone_d, 'KDDK')]
    Phi_p = s5_add_nc([(sp_d, 'DD')], [(s5_p_scale(F(-1), c), w) for c, w in dPhi])
    commD_terms = s5_add_nc(s5_mul_nc(D_p, dPhi), s5_mul_nc(dPhi, [(mone_d, 'D')]))
    commP_terms = s5_add_nc(s5_mul_nc([(one_d, 'P')], dPhi), s5_mul_nc(dPhi, [(mone_d, 'P')]))
    target_terms = s5_add_nc([(s5_p_scale(F(m, m - 1), sp_d), 'PDDDD')], s5_mul_nc([(mone_d, 'DD')], dPhi))

    P_p = [(one_d, 'P')]
    IP_p = [(one_d, ''), (mone_d, 'P')]
    K_p = [(one_d, 'K')]
    Xhi_p = [([h_hi], ''), (mone_d, 'K')]
    negPPhi = s5_mul_nc([(mone_d, 'P')], Phi_p)
    posIPPhi = s5_mul_nc(IP_p, Phi_p)
    PcPhi = s5_mul_nc(P_p, s5_add_nc([([F(1, 4)], 'DD')], Phi_p))

    mx_K = (deg - 1) // 2
    mx_0 = deg // 2
    B2_K_all = s5_gen_words_K(2, mx_K, 1, False)
    B2_K_noD = s5_gen_words_K(2, mx_K, 1, True)
    B2_0_all = s5_gen_words_K(2, mx_0, 1, False)
    B2_0_noD_noP = s5_gen_words_K(2, mx_0, 0, True)
    c1 = [
        ('C1(P,K)', P_p, K_p, B2_K_all), ('C1(P,Xhi)', P_p, Xhi_p, B2_K_all),
        ('C1(I-P,K)', IP_p, K_p, B2_K_all), ('C1(I-P,Xhi)', IP_p, Xhi_p, B2_K_noD),
        ('C1(P,P)', P_p, P_p, B2_0_all), ('C1(P,I-P)', P_p, IP_p, B2_0_all),
        ('C1(I-P,I-P)', IP_p, IP_p, B2_0_noD_noP),
    ]
    oth = []
    mx3 = (deg - 3) // 2
    if mx3 >= 0:
        B1_all = s5_gen_words_K(1, mx3, 1, False)
        B1_noD = s5_gen_words_K(1, mx3, 1, True)
        oth += [
            ('C3(K,-P*Phi)', K_p, negPPhi, B1_all),
            ('C3(Xhi,-P*Phi)', Xhi_p, negPPhi, B1_all),
            ('C3(K,(I-P)*Phi)', K_p, posIPPhi, B1_all),
        ]
        if B1_noD:
            oth.append(('C3(Xhi,(I-P)*Phi)', Xhi_p, posIPPhi, B1_noD))
        oth += [
            ('C3(K,P(D2/4+Phi))', K_p, PcPhi, B1_all),
            ('C3(Xhi,P(D2/4+Phi))', Xhi_p, PcPhi, B1_all),
        ]
    mx4 = (deg - 2) // 2
    if mx4 >= 0:
        B0_all = s5_gen_words_K(0, mx4, 1, False)
        B0_noD = s5_gen_words_K(0, mx4, 1, True)
        PD2 = [(one_d, 'PDD')]
        IPD2 = [(one_d, 'DD'), (mone_d, 'PDD')]
        oth += [
            ('C4(PD2,-P*Phi)', PD2, negPPhi, B0_all),
            ('C4(PD2,P(D2/4+Phi))', PD2, PcPhi, B0_all),
            ('C4(PD2,(I-P)*Phi)', PD2, posIPPhi, B0_all),
            ('C4((I-P)D2,-P*Phi)', IPD2, negPPhi, B0_all),
            ('C4((I-P)D2,P(D2/4+Phi))', IPD2, PcPhi, B0_all),
        ]
        if B0_noD:
            oth.append(('C4((I-P)D2,(I-P)*Phi)', IPD2, posIPPhi, B0_noD))
    mx6 = (deg - 3) // 2
    if mx6 >= 0:
        B0_a6 = s5_gen_words_K(0, mx6, 1, False)
        B0_n6 = s5_gen_words_K(0, mx6, 1, True)
        D2_negP = s5_mul_nc([(one_d, 'DD')], negPPhi)
        D2_posIP = s5_mul_nc([(one_d, 'DD')], posIPPhi)
        D2_Pc = s5_mul_nc([(one_d, 'DD')], PcPhi)
        oth += [
            ('C6(K,-PD2*Phi)', K_p, D2_negP, B0_a6),
            ('C6(Xhi,-PD2*Phi)', Xhi_p, D2_negP, B0_a6),
            ('C6(K,(I-P)D2*Phi)', K_p, D2_posIP, B0_a6),
        ]
        if B0_n6:
            oth.append(('C6(Xhi,(I-P)D2*Phi)', Xhi_p, D2_posIP, B0_n6))
        oth += [
            ('C6(K,PD2(D2/4+Phi))', K_p, D2_Pc, B0_a6),
            ('C6(Xhi,PD2(D2/4+Phi))', Xhi_p, D2_Pc, B0_a6),
        ]

    def prune_zero_diag(tmps):
        out = []
        for name, pL, pR, Bl in tmps:
            kept = []
            for u in Bl:
                ur = u[::-1]
                dw = {}
                for cL, wL in pL:
                    for cR, wR in pR:
                        cw = s5_canon_tracial(wL + ur + wR + u)
                        pr = s5_p_mul(cL, cR)
                        dw[cw] = s5_p_add(dw[cw], pr) if cw in dw else pr
                if any(any(x != 0 for x in poly) for poly in dw.values()):
                    kept.append(u)
            if kept:
                out.append((name, pL, pR, kept))
        return out

    c1 = prune_zero_diag(c1)
    oth = prune_zero_diag(oth)
    W_g = s5_gen_words_K(2, max(0, deg - 3), max_p=1, exclude_pure_D=False)
    W_cD = s5_gen_words_K(1, max(0, deg - 2), max_p=1, exclude_pure_D=False)
    W_cP = s5_gen_words_K(2, max(0, deg - 2), max_p=1, exclude_pure_D=False)
    return 3, 'PDDDD', 'DDDD', target_terms, c1, oth, [(W_g, g_terms), (W_cD, commD_terms), (W_cP, commP_terms)]


def s5_rebuild_delta_p32(m0: Fraction, m_hi: Fraction, m: int, deg: int):
    F = Fraction
    mp_d = [m0, F(1)]
    mp2_d = s5_p_mul(mp_d, mp_d)
    Lam_mp_d = s5_p_mul(s5_p_add([F(1)], mp2_d), s5_p_add([F(1)], mp2_d))
    sp_d = s5_p_add(s5_p_mul(mp2_d, mp_d), s5_p_scale(F(-1), mp_d))
    one_d = [F(1)]
    mone_d = [F(-1)]
    c_32_Q = F(77, 200)
    assert c_32_Q > 0 and c_32_Q ** 2 > F(4, 27)  # 77/200 > 2/(3*sqrt(3))

    M_p = [(mp_d, ''), (mone_d, 'K')]
    D_p = [(one_d, 'D')]
    MDM = s5_mul_nc(s5_mul_nc(M_p, D_p), M_p)
    S_p = s5_add_nc(D_p, MDM)
    g_terms = s5_add_nc(
        s5_mul_nc([(mp_d, '')], s5_mul_nc(S_p, S_p)),
        s5_mul_nc([(s5_p_scale(F(-1), Lam_mp_d), 'D')], s5_mul_nc(M_p, D_p)),
    )
    assert all(w != 'DD' for _, w in g_terms)
    Phi_p = s5_add_nc(
        s5_mul_nc(MDM, s5_mul_nc(D_p, M_p)),
        s5_mul_nc([(mone_d, 'D')], s5_mul_nc(M_p, D_p)),
    )
    dPhi = s5_add_nc([(sp_d, 'DD')], [(s5_p_scale(F(-1), c), w) for c, w in Phi_p])
    assert all(w != 'DD' for _, w in dPhi)

    commD_terms = s5_add_nc(s5_mul_nc(D_p, dPhi), s5_mul_nc(dPhi, [(mone_d, 'D')]))
    commP_terms = s5_add_nc(s5_mul_nc([(one_d, 'P')], dPhi), s5_mul_nc(dPhi, [(mone_d, 'P')]))
    target_terms = s5_add_nc([(s5_p_scale(F(m, m - 1), sp_d), 'PDDD')], s5_mul_nc([(mone_d, 'D')], dPhi))

    P_p = [(one_d, 'P')]
    IP_p = [(one_d, ''), (mone_d, 'P')]
    K_p = [(one_d, 'K')]
    Mhi_p = [([m_hi], ''), (mone_d, 'K')]
    PD_p = [(one_d, 'PD')]
    IPD_p = [(one_d, 'D'), (mone_d, 'PD')]
    negPPhi = s5_mul_nc([(mone_d, 'P')], Phi_p)
    posIPPhi = s5_mul_nc(IP_p, Phi_p)
    PcPhi = s5_mul_nc(P_p, s5_add_nc([([c_32_Q], 'DD')], Phi_p))

    mx1 = (deg - 1) // 2
    mx0 = deg // 2
    B1_all = s5_gen_words_K(1, mx1, 1, False)
    B1_noD = s5_gen_words_K(1, mx1, 1, True)
    B1_0all = s5_gen_words_K(1, mx0, 1, False)
    B1_0noD = s5_gen_words_K(1, mx0, 1, True)
    c1 = [
        ('C1(PD,K)', PD_p, K_p, B1_all), ('C1(PD,Mhi)', PD_p, Mhi_p, B1_all),
        ('C1((I-P)D,K)', IPD_p, K_p, B1_all), ('C1((I-P)D,Mhi)', IPD_p, Mhi_p, B1_noD),
        ('C1(PD,P)', PD_p, P_p, B1_0all), ('C1(PD,I-P)', PD_p, IP_p, B1_0all),
        ('C1((I-P)D,P)', IPD_p, P_p, B1_0all), ('C1((I-P)D,I-P)', IPD_p, IP_p, B1_0noD),
    ]
    oth = []
    mx2a = (deg - 3) // 2
    if mx2a >= 0:
        B0_a = s5_gen_words_K(0, mx2a, 1, False)
        B0_an = s5_gen_words_K(0, mx2a, 1, True)
        oth += [
            ('C2a(PD,-P*Phi)', PD_p, negPPhi, B0_a),
            ('C2a(PD,P(cD2+Phi))', PD_p, PcPhi, B0_a),
            ('C2a(PD,(I-P)*Phi)', PD_p, posIPPhi, B0_a),
            ('C2a((I-P)D,-P*Phi)', IPD_p, negPPhi, B0_a),
            ('C2a((I-P)D,P(cD2+Phi))', IPD_p, PcPhi, B0_a),
        ]
        if B0_an:
            oth.append(('C2a((I-P)D,(I-P)*Phi)', IPD_p, posIPPhi, B0_an))
    mx2b = (deg - 4) // 2
    if mx2b >= 0:
        B0_b = s5_gen_words_K(0, mx2b, 1, False)
        B0_bn = s5_gen_words_K(0, mx2b, 1, True)
        D_negP = s5_mul_nc(D_p, negPPhi)
        D_posIP = s5_mul_nc(D_p, posIPPhi)
        D_Pc = s5_mul_nc(D_p, PcPhi)
        oth += [
            ('C2b(K,-PD*Phi)', K_p, D_negP, B0_b),
            ('C2b(Mhi,-PD*Phi)', Mhi_p, D_negP, B0_b),
            ('C2b(K,(I-P)D*Phi)', K_p, D_posIP, B0_b),
        ]
        if B0_bn:
            oth.append(('C2b(Mhi,(I-P)D*Phi)', Mhi_p, D_posIP, B0_bn))
        oth += [
            ('C2b(K,PD(cD2+Phi))', K_p, D_Pc, B0_b),
            ('C2b(Mhi,PD(cD2+Phi))', Mhi_p, D_Pc, B0_b),
        ]
    W_g = s5_gen_words_K(1, max(0, deg - 4), max_p=1, exclude_pure_D=False)
    W_cD = s5_gen_words_K(0, max(0, deg - 3), max_p=1, exclude_pure_D=False)
    W_cP = s5_gen_words_K(1, max(0, deg - 3), max_p=1, exclude_pure_D=False)
    return 5, 'PDDD', 'DDD', target_terms, c1, oth, [(W_g, g_terms), (W_cD, commD_terms), (W_cP, commP_terms)]


def verify_one_s5_subinterval(p_str: str, m: int, deg: int, sc: dict, si: int):
    """Independently verify one exact rational Bernstein continuous-interval certificate (0 floats)."""
    h_lo = parse_frac(sc["h_lo"])
    h_hi = parse_frac(sc["h_hi"])
    assert h_lo > 1 and h_hi > h_lo, f"Invalid subinterval {si}: [{h_lo}, {h_hi}]"
    h0 = (h_lo + h_hi) / 2
    Delta = (h_hi - h_lo) / 2

    if p_str == "4/3":
        D_max, norm_word, pure_D_word, target_terms, c1_tmps, oth_tmps, eq_specs = s5_rebuild_delta_p43(h0, h_hi, m, deg)
    else:
        assert p_str == "3/2"
        D_max, norm_word, pure_D_word, target_terms, c1_tmps, oth_tmps, eq_specs = s5_rebuild_delta_p32(h0, h_hi, m, deg)

    # Deterministically filter oth_tmps and eq_specs to the C1-contained algebra (exact valid subset).
    c1_vars = {s5_canon_tracial(norm_word)}
    for _, tw in target_terms:
        c1_vars.add(s5_canon_tracial(tw))
    for _, pL, pR, Bl in c1_tmps:
        for i, u in enumerate(Bl):
            ur = u[::-1]
            for j in range(i, len(Bl)):
                for _, wL in pL:
                    for _, wR in pR:
                        c1_vars.add(s5_canon_tracial(wL + ur + wR + Bl[j]))
    oth_filt = []
    for name, pL, pR, Bl in oth_tmps:
        kept = []
        for u in Bl:
            ur = u[::-1]
            ok = True
            for v in kept + [u]:
                vr = v[::-1]
                for _, wL in pL:
                    for _, wR in pR:
                        if (s5_canon_tracial(wL + ur + wR + v) not in c1_vars) or (
                            s5_canon_tracial(wL + vr + wR + u) not in c1_vars
                        ):
                            ok = False
                            break
                    if not ok:
                        break
                if not ok:
                    break
            if ok:
                kept.append(u)
        if kept:
            oth_filt.append((name, pL, pR, kept))
    oth_tmps = oth_filt
    eq_specs = [
        ([w for w in words if all(s5_canon_tracial(w + tw) in c1_vars for _, tw in terms)], terms)
        for words, terms in eq_specs
    ]

    vars_set = set(c1_vars)

    def build_blocks(tmps, const_only: bool):
        out = []
        for name, pL, pR, Bl in tmps:
            k = len(Bl)
            if k == 0:
                continue
            entries = []
            for i, u in enumerate(Bl):
                ur = u[::-1]
                for j in range(i, k):
                    d_w = {}
                    for cL, wL in pL:
                        for cR, wR in pR:
                            cw = s5_canon_tracial(wL + ur + wR + Bl[j])
                            vars_set.add(cw)
                            pr = s5_p_mul(cL, cR)
                            d_w[cw] = s5_p_add(d_w[cw], pr) if cw in d_w else pr
                    for cw, poly in d_w.items():
                        if any(x != 0 for x in poly):
                            if const_only:
                                assert all(x == 0 for x in poly[1:])
                                entries.append((i, j, cw, poly[0]))
                            else:
                                entries.append((i, j, cw, poly))
            out.append((name, k, entries))
        return out

    c1_specs = build_blocks(c1_tmps, True)
    oth_specs = build_blocks(oth_tmps, False)
    eq_rows = []
    for words, terms in eq_specs:
        for w in words:
            d = {}
            for c_poly, tw in terms:
                cw = s5_canon_tracial(w + tw)
                vars_set.add(cw)
                d[cw] = s5_p_add(d[cw], c_poly) if cw in d else list(c_poly)
            items = [(kw, poly) for kw, poly in d.items() if any(x != 0 for x in poly)]
            if items:
                eq_rows.append(items)

    assert s5_canon_tracial(pure_D_word) not in vars_set, "Pure D^(2*kappa) leaked into algebra!"
    vars_list = sorted(vars_set)
    idx = {w: i for i, w in enumerate(vars_list)}
    n_vars = len(vars_list)
    i_norm = idx[s5_canon_tracial(norm_word)]

    E_bern = int(sc["E_bern"])
    M_bern = s5_bernstein_matrix_verified(D_max, E_bern)
    Delta_pows = [Delta ** r for r in range(D_max + 1)]

    c_polys = [parse_frac(s) for s in sc["c_polys_Q"]]
    assert len(c_polys) == D_max + 1
    eq_pivs = sc["eq_pivots"]
    alpha_Q = [parse_frac(s) for s in sc["alpha_Q"]]
    assert len(eq_pivs) == len(alpha_Q)
    assert all(isinstance(r_i, int) and 0 <= r_i < len(eq_rows) for r_i in eq_pivs)
    Zoth_Q = [[[parse_frac(x) for x in row] for row in mat] for mat in sc["Zoth_Q"]]
    Roth_Q = [[[parse_frac(x) for x in row] for row in mat] for mat in sc["R_oth_Q"]]
    Zc1_polys = [[[[parse_frac(x) for x in row] for row in mat] for mat in d_list] for d_list in sc["Zc1_polys_Q"]]
    Rc1_bern = [[[[parse_frac(x) for x in row] for row in mat] for mat in b_list] for b_list in sc["R_c1_bern_Q"]]
    assert len(Zoth_Q) == len(oth_specs) and len(Roth_Q) == len(oth_specs)
    assert len(Zc1_polys) == D_max + 1 and len(Rc1_bern) == E_bern + 1

    # 1. Exact Bernstein positivity of c(delta) = sum_{j=0}^E c_bern[j] B_j^E(s) > 0 on all s in [0, 1]
    c_bern = [sum(M_bern[j][r] * Delta_pows[r] * c_polys[r] for r in range(D_max + 1)) for j in range(E_bern + 1)]
    c_mg = min(c_bern)
    assert c_mg > 0, f"c_bern <= 0 on subinterval {si}"

    # 2. Exact 0/1 polynomial identity for ALL powers r = 0..D_max and ALL monomials w (zero degree truncation!)
    lhs = [[Fraction(0)] * n_vars for _ in range(D_max + 1)]
    for c_poly, tw in target_terms:
        assert len(c_poly) <= D_max + 1
        vi = idx[s5_canon_tracial(tw)]
        for r in range(len(c_poly)):
            lhs[r][vi] += c_poly[r]
    for ri, row_idx in enumerate(eq_pivs):
        a = alpha_Q[ri]
        if a == 0:
            continue
        for kw, poly in eq_rows[row_idx]:
            assert len(poly) <= D_max + 1
            vi = idx[kw]
            for r in range(len(poly)):
                lhs[r][vi] += a * poly[r]
    for bi, (name, k, entries) in enumerate(oth_specs):
        Zb = Zoth_Q[bi]
        Rb = Roth_Q[bi]
        assert len(Zb) == k and all(len(row) == k for row in Zb)
        assert len(Rb) == k and all(len(row) == k for row in Rb)
        for i in range(k):
            for j in range(i + 1, k):
                assert Zb[i][j] == Zb[j][i], f"Non-symmetric Zoth {name}"
        for i, j, cw, poly in entries:
            assert len(poly) <= D_max + 1
            vi = idx[cw]
            zv = Zb[i][i] if i == j else Fraction(2) * Zb[i][j]
            for r in range(len(poly)):
                lhs[r][vi] -= zv * poly[r]

    rhs = [[Fraction(0)] * n_vars for _ in range(D_max + 1)]
    for r in range(D_max + 1):
        assert len(Zc1_polys[r]) == len(c1_specs)
        rhs[r][i_norm] += c_polys[r]
        for bi, (name, k, entries) in enumerate(c1_specs):
            Zb = Zc1_polys[r][bi]
            assert len(Zb) == k and all(len(row) == k for row in Zb)
            for i in range(k):
                for j in range(i + 1, k):
                    assert Zb[i][j] == Zb[j][i], f"Non-symmetric Zc1 {name} r={r}"
            for i, j, cw, val in entries:
                vi = idx[cw]
                rhs[r][vi] += val * Zb[i][i] if i == j else Fraction(2) * val * Zb[i][j]
        assert all(lhs[r][v] == rhs[r][v] for v in range(n_vars)), f"Non-zero residual at sub {si} deg {r}!"

    # 3. Exact Rump congruence + Gershgorin strict diagonal dominance on ALL oth & Bernstein control matrices
    min_gersh = None
    for bi, (name, k, _) in enumerate(oth_specs):
        Zb = Zoth_Q[bi]
        Rb = Roth_Q[bi]
        RZ = [[sum(Rb[i][t] * Zb[t][j] for t in range(k)) for j in range(k)] for i in range(k)]
        for i in range(k):
            w_ii = sum(RZ[i][t] * Rb[i][t] for t in range(k))
            off = sum(abs(sum(RZ[i][t] * Rb[j][t] for t in range(k))) for j in range(k) if j != i)
            mg = w_ii - off
            assert mg > 0, f"oth Gershgorin fail on sub {si} {name}"
            if min_gersh is None or mg < min_gersh:
                min_gersh = mg
    for j in range(E_bern + 1):
        assert len(Rc1_bern[j]) == len(c1_specs)
        coeffs = [M_bern[j][r] * Delta_pows[r] for r in range(D_max + 1)]
        for bi, (name, k, _) in enumerate(c1_specs):
            Rb = Rc1_bern[j][bi]
            assert len(Rb) == k and all(len(row) == k for row in Rb)
            Zbj = [[sum(coeffs[r] * Zc1_polys[r][bi][ii][jj] for r in range(D_max + 1)) for jj in range(k)] for ii in range(k)]
            RZ = [[sum(Rb[i][t] * Zbj[t][jj] for t in range(k)) for jj in range(k)] for i in range(k)]
            for i in range(k):
                w_ii = sum(RZ[i][t] * Rb[i][t] for t in range(k))
                off = sum(abs(sum(RZ[i][t] * Rb[jj][t] for t in range(k))) for jj in range(k) if jj != i)
                mg = w_ii - off
                assert mg > 0, f"C1 Bernstein Gershgorin fail on sub {si} j={j} {name}"
                if min_gersh is None or mg < min_gersh:
                    min_gersh = mg

    return h_lo, h_hi, c_mg, min_gersh


def verify_suite5_multisummand_intervals():
    print("\n" + "=" * 78)
    print("SUITE 5: Theorem 17 Unconditional Continuous-Interval Bernstein World Records")
    print("=" * 78)
    cert_dir = os.path.join(HERE, "multisummand_interval_certs_v5")
    expected_files = [
        ("interval_qcert_p43_m3_d5.json.gz", "4/3", 3, 5, Fraction(1032736, 10**6), None),
        ("interval_qcert_p43_m4_d5.json.gz", "4/3", 4, 5, Fraction(1043887, 10**6), None),
        ("interval_qcert_p32_m3_d7.json.gz", "3/2", 3, 7, Fraction(1064447, 10**6), (Fraction(12, 5), Fraction(16079, 10000))),
        ("interval_qcert_p32_m4_d7.json.gz", "3/2", 4, 7, Fraction(1086336, 10**6), (Fraction(1189, 500), Fraction(1631, 1000))),
    ]
    t_suite = time.time()
    first_tamper_sample = None

    for fname, exp_p, exp_m, exp_d, C_cap_hi, thm10b_wit in expected_files:
        t0 = time.time()
        path = os.path.join(cert_dir, fname)
        with gzip.open(path, "rt", encoding="ascii") as fp:
            data = json.load(fp)
        p_str = data["p_str"]
        m = int(data["m"])
        deg = int(data["deg"])
        assert (p_str, m, deg) == (exp_p, exp_m, exp_d), f"Metadata mismatch in {fname}"
        h_start = parse_frac(data["h_start"])
        h_end = parse_frac(data["h_end"])
        subs = data["subintervals"]
        assert h_start > 1 and h_end > h_start and len(subs) == int(data["n_subintervals"]) and len(subs) > 0

        cur = h_start
        min_c_all = None
        min_g_all = None
        for si, sc in enumerate(subs):
            h_lo, h_hi, c_mg, g_mg = verify_one_s5_subinterval(p_str, m, deg, sc, si)
            assert h_lo == cur, f"Non-contiguous subinterval {si} in {fname}: {h_lo} != {cur}"
            cur = h_hi
            if min_c_all is None or c_mg < min_c_all:
                min_c_all = c_mg
            if min_g_all is None or g_mg < min_g_all:
                min_g_all = g_mg
        assert cur == h_end, f"Interval end mismatch in {fname}: {cur} != {h_end}"

        if first_tamper_sample is None:
            first_tamper_sample = (p_str, m, deg, json.loads(json.dumps(subs[0])))

        # Exact rational cap verification + exact integer round-UP of unconditional C_{p,m}(inf) bound!
        if p_str == "4/3":
            Lam_lo = ((1 + h_start) ** 3) / h_start
            Lam_hi = ((1 + h_end) ** 3) / h_end
            assert Lam_hi >= 8 * (C_cap_hi ** 4), f"Lam_hi below exact V4 Thm 10C cap in {fname}"
            _, C_lo_hi = nth_root_bounds(Lam_lo / 8, 4, 80)
            C_hi_lo, _ = nth_root_bounds(Lam_hi / 8, 4, 50)
            cap_note = f"clears exact V4 Thm 10C cap ({fmt_dec(C_cap_hi, 6)}) up to C_hi>={fmt_dec(C_hi_lo, 6)}"
        else:
            Lam_lo = ((1 + h_start ** 2) ** 2) / h_start
            Lam_hi = ((1 + h_end ** 2) ** 2) / h_end
            assert Lam_hi >= 4 * (C_cap_hi ** 3), f"Lam_hi below V4 Thm 10B cap in {fname}"
            # Exact zero-float 1-line V4 Theorem 10B witness refuting ALL Lam >= Lam_hi!
            B_Q, g_Q = thm10b_wit
            sp_end = h_end ** 3 - h_end
            assert B_Q > 2 and g_Q > 0
            assert g_Q + (B_Q ** 4) / (64 * g_Q) <= (B_Q - 2) * Lam_hi
            assert (Lam_hi + g_Q) * sp_end / Fraction(m - 1) > (B_Q ** 2) / 4
            _, C_lo_hi = nth_root_bounds(Lam_lo / 4, 3, 80)
            C_hi_lo, _ = nth_root_bounds(Lam_hi / 4, 3, 50)
            cap_note = f"zero-float Thm 10B witness (B={B_Q}, gam={g_Q}) refutes ALL Lam>=Lam_hi (C_hi>={fmt_dec(C_hi_lo, 6)})"

        dt = time.time() - t0
        print(f"  [PASS] {fname} (p={p_str}, m={m}, d={deg}, {len(subs):2d} exact-contiguous subintervals, {dt:.1f}s)")
        print(f"         Interval [{h_start}, {h_end}] | Lam in [{fmt_dec(Lam_lo, 8)}, {fmt_dec(Lam_hi, 8)}] | {cap_note}")
        print(f"         UNCONDITIONAL C_{{{p_str},{m}}}(inf) <= {fmt_dec(C_lo_hi, 10, round_up=True)} | 0/1 residual | min_c={fmt_dec(min_c_all, 6)} | min_Gersh={fmt_dec(min_g_all, 6)}")

    # Suite 5 negative tamper test: perturb one rational entry in Zc1_polys_Q[0][0][0][0] -> MUST FAIL!
    tp, tm, td, bad_sc = first_tamper_sample
    bad_sc["Zc1_polys_Q"][0][0][0][0] = str(parse_frac(bad_sc["Zc1_polys_Q"][0][0][0][0]) + Fraction(1, 10**12))
    caught = False
    try:
        verify_one_s5_subinterval(tp, tm, td, bad_sc, 0)
    except AssertionError:
        caught = True
    assert caught, "Suite 5 tampered Zc1_polys_Q entry was NOT caught!"
    print(f"  [PASS] Suite 5 negative tamper test caught immediately! (Total Suite 5 time: {time.time() - t_suite:.1f}s)")


# ==============================================================================
# Suite 6: Theorem 22 Unconditional Zero-Float Full-V4-Enclosure Top-Band Exact
#          Reducing-Subspace Splitting P_top = P_1 (+) P_2 (p = 4/3 and p = 3/2)
# ==============================================================================

class S6IV:
    """Exact rational interval [lo, hi] using fractions.Fraction exclusively (0 floats)."""
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        lo = Fraction(lo)
        hi = lo if hi is None else Fraction(hi)
        assert lo <= hi, f"bad S6IV: {lo} > {hi}"
        self.lo = lo
        self.hi = hi

    def __add__(self, o):
        o = o if isinstance(o, S6IV) else S6IV(o)
        return S6IV(self.lo + o.lo, self.hi + o.hi)

    def __radd__(self, o):
        return self.__add__(o)

    def __neg__(self):
        return S6IV(-self.hi, -self.lo)

    def __sub__(self, o):
        o = o if isinstance(o, S6IV) else S6IV(o)
        return S6IV(self.lo - o.hi, self.hi - o.lo)

    def __rsub__(self, o):
        return S6IV(o).__sub__(self)

    def __mul__(self, o):
        o = o if isinstance(o, S6IV) else S6IV(o)
        ps = (self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi)
        return S6IV(min(ps), max(ps))

    def __rmul__(self, o):
        return self.__mul__(o)

    def __truediv__(self, o):
        o = o if isinstance(o, S6IV) else S6IV(o)
        assert o.lo > 0 or o.hi < 0, f"div by 0 in S6IV: [{o.lo}, {o.hi}]"
        return self * S6IV(Fraction(1) / o.hi, Fraction(1) / o.lo)

    def sq(self):
        if self.lo >= 0:
            return S6IV(self.lo * self.lo, self.hi * self.hi)
        if self.hi <= 0:
            return S6IV(self.hi * self.hi, self.lo * self.lo)
        return S6IV(Fraction(0), max(self.lo * self.lo, self.hi * self.hi))


def s6_verify_p43_symbolic_cancellation(Lam_q: Fraction, mu_q: Fraction, R_q: Fraction, xi1_q: Fraction):
    eta1 = (R_q + 3 - Lam_q) / 2 - xi1_q
    xi0 = xi1_q - (R_q * eta1 * eta1) / (2 * (xi1_q - 1))
    xi = [xi0, xi1_q, Fraction(1)]

    def eval_M(a, s2, t2, t3):
        t1 = a + mu_q
        s3 = (Lam_q - 4) * a - 2 * s2 - 1 - mu_q
        s4 = Lam_q * t1 - a - s2 - 3 * t1 - 2 * mu_q * a - s3 - t2
        diff_p = Lam_q * (t1 + mu_q * a - t2) + a + t1 + 2 * t2 + mu_q * a - s2 - s3 - s4
        M1 = [
            [1 + a, a + s2, s2 + s3],
            [a + s2, t1 + s3, t1 + mu_q * a + s4],
            [s2 + s3, t1 + mu_q * a + s4, t3 + diff_p],
        ]
        M2 = [
            [R_q - 1, (R_q - 1) * a, (R_q - 1) * a],
            [(R_q - 1) * a, R_q * s2 - t1, R_q * t1 - t2],
            [(R_q - 1) * a, R_q * t1 - t2, R_q * t2 - t3],
        ]
        return M1, M2

    def qf(M, v):
        return sum(v[i] * M[i][j] * v[j] for i in range(3) for j in range(3))

    M1_0, M2_0 = eval_M(Fraction(0), Fraction(0), Fraction(0), Fraction(0))
    M1_a, M2_a = eval_M(Fraction(1), Fraction(0), Fraction(0), Fraction(0))
    d1 = [[M1_a[i][j] - M1_0[i][j] for j in range(3)] for i in range(3)]
    d2 = [[M2_a[i][j] - M2_0[i][j] for j in range(3)] for i in range(3)]
    ca_no0 = qf(d1, xi) + qf(d2, [Fraction(0), eta1, Fraction(1)])
    eta0 = -ca_no0 / (2 * (R_q - 1) * (eta1 + 1))
    eta = [eta0, eta1, Fraction(1)]
    c0 = qf(M1_0, xi) + qf(M2_0, eta)
    for e_vec in [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]:
        M1_e, M2_e = eval_M(*(Fraction(z) for z in e_vec))
        assert qf(M1_e, xi) + qf(M2_e, eta) - c0 == Fraction(0)
    return c0


def s6_r1_quad_iv(Lam_iv: S6IV, R_q: Fraction, xi1_q: Fraction):
    R = S6IV(R_q)
    xi1 = S6IV(xi1_q)
    eta1 = (R + S6IV(3) - Lam_iv) / S6IV(2) - xi1
    xi0 = xi1 - (R * eta1.sq()) / (S6IV(2) * (xi1 - S6IV(1)))
    xi = [xi0, xi1, S6IV(1)]

    def qf(M, v):
        s = S6IV(0)
        for i in range(3):
            for j in range(3):
                if M[i][j] != 0:
                    s = s + v[i] * M[i][j] * v[j]
        return s

    M1_a0 = [[S6IV(1), S6IV(1), Lam_iv - S6IV(4)], [S6IV(1), Lam_iv - S6IV(3), S6IV(1)], [Lam_iv - S6IV(4), S6IV(1), S6IV(6)]]
    M1_a1 = [[0, 0, 0], [0, 0, S6IV(-1)], [0, S6IV(-1), Lam_iv + S6IV(3)]]
    p0 = qf(M1_a0, xi) - eta1.sq() + S6IV(2) * R * eta1
    p1 = qf(M1_a1, xi)
    denom = S6IV(2) * (R - S6IV(1)) * (eta1 + S6IV(1))
    e0 = -p0 / denom
    e1 = -p1 / denom
    M1_00 = [[S6IV(1), 0, S6IV(-1)], [0, S6IV(-1), S6IV(1)], [S6IV(-1), S6IV(1), 0]]
    M1_01 = [[0, 0, S6IV(-1)], [0, 0, Lam_iv - S6IV(1)], [S6IV(-1), Lam_iv - S6IV(1), S6IV(4)]]
    m0 = qf(M1_00, xi)
    m1 = qf(M1_01, xi)
    A = (R - S6IV(1)) * e1.sq()
    B = m1 + S6IV(2) * (R - S6IV(1)) * e0 * e1 - eta1.sq() + S6IV(2) * R * eta1
    C = m0 + (R - S6IV(1)) * e0.sq()
    return A, B, C


def s6_eval_p32_mats(Lam, mu, R, a, s2, q2, q3, y1):
    b = (1 + 2 * a + s2) / Lam
    wH_D_wD = Lam * q2 - 3 * b - 2 * mu - mu * a
    M_H = [[a, s2, b + mu], [s2, 1 + a + Lam * mu - y1, b + mu + mu * a], [b + mu, b + mu + mu * a, q2 + mu * b]]
    M_D = [[1, a, b], [a, y1, wH_D_wD], [b, wH_D_wD, q3]]
    M_R = [
        [R - 1, (R - 1) * a, (R - 1) * b],
        [(R - 1) * a, R * s2 - y1, R * (b + mu) - wH_D_wD],
        [(R - 1) * b, R * (b + mu) - wH_D_wD, R * q2 - q3],
    ]
    M_M = [[b, a], [a, b + mu]]
    return [M_H, M_D, M_R, M_M]


def s6_mats_to_vec(ms):
    out = []
    for M in ms:
        k = len(M)
        for i in range(k):
            for j in range(i, k):
                out.append(M[i][j] if i == j else 2 * M[i][j])
    return out


def s6_vec_to_mats(y):
    ms = []
    idx = 0
    for k in [3, 3, 3, 2]:
        M = [[None] * k for _ in range(k)]
        for i in range(k):
            for j in range(i, k):
                M[i][j] = M[j][i] = y[idx]
                idx += 1
        ms.append(M)
    return ms


def s6_invert_exact_q(M):
    n = len(M)
    A = [[Fraction(M[i][j]) for j in range(n)] + [Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]
    for k in range(n):
        p = next(r for r in range(k, n) if A[r][k] != 0)
        A[k], A[p] = A[p], A[k]
        piv = A[k][k]
        A[k] = [x / piv for x in A[k]]
        for r in range(n):
            if r != k and A[r][k] != 0:
                f = A[r][k]
                A[r] = [A[r][j] - f * A[k][j] for j in range(2 * n)]
    return [row[n:] for row in A]


def s6_verify_p32_iv_box(Lam_iv: S6IV, mu_iv: S6IV, R_q: Fraction, piv_cols, free_vals_q):
    R_iv = S6IV(R_q)
    Lam_m = (Lam_iv.lo + Lam_iv.hi) / 2
    mu_m = (mu_iv.lo + mu_iv.hi) / 2
    free_cols = [c for c in range(21) if c not in piv_cols]

    def exact_rows(Lq, mq):
        m0 = s6_eval_p32_mats(Lq, mq, R_q, Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(0))
        rs = []
        for k in range(5):
            pt = [Fraction(1) if j == k else Fraction(0) for j in range(5)]
            mk = s6_eval_p32_mats(Lq, mq, R_q, *pt)
            dk = [[[mk[m][i][j] - m0[m][i][j] for j in range(len(mk[m]))] for i in range(len(mk[m]))] for m in range(4)]
            rs.append(s6_mats_to_vec(dk))
        return m0, rs

    m0_m, rows_m = exact_rows(Lam_m, mu_m)
    P0 = s6_invert_exact_q([[rows_m[r][c] for c in piv_cols] for r in range(5)])
    y0 = [Fraction(0)] * 21
    for c, vq in zip(free_cols, free_vals_q):
        y0[c] = vq
    rhs0 = [-sum(rows_m[r][c] * y0[c] for c in free_cols) for r in range(5)]
    for idx, c in enumerate(piv_cols):
        y0[c] = sum(P0[idx][t] * rhs0[t] for t in range(5))
    for r in range(5):
        assert sum(rows_m[r][c] * y0[c] for c in range(21)) == Fraction(0)

    # Exact 5-term rational basis decomposition in (Lam, mu, 1/Lam, mu/Lam)
    _, r_L1 = exact_rows(Lam_m + 1, mu_m)
    _, r_L2 = exact_rows(Lam_m + 2, mu_m)
    _, r_m1 = exact_rows(Lam_m, mu_m + 1)
    _, r_L1m1 = exact_rows(Lam_m + 1, mu_m + 1)
    C_L = [[Fraction(0)] * 21 for _ in range(5)]
    C_mu = [[Fraction(0)] * 21 for _ in range(5)]
    C_inv = [[Fraction(0)] * 21 for _ in range(5)]
    C_mi = [[Fraction(0)] * 21 for _ in range(5)]
    for r in range(5):
        for c in range(21):
            mixed = (r_L1m1[r][c] - r_L1[r][c]) - (r_m1[r][c] - rows_m[r][c])
            cMI = -mixed * Lam_m * (Lam_m + 1)
            cM = (r_m1[r][c] - rows_m[r][c]) - cMI / Lam_m
            d1 = r_L1[r][c] - rows_m[r][c]
            d2 = r_L2[r][c] - rows_m[r][c]
            cI_eff = (d2 - 2 * d1) * Lam_m * (Lam_m + 1) * (Lam_m + 2) / 2
            cI = cI_eff - cMI * mu_m
            cL = d1 + cI_eff / (Lam_m * (Lam_m + 1))
            C_L[r][c] = cL
            C_mu[r][c] = cM
            C_inv[r][c] = cI
            C_mi[r][c] = cMI
    _, r_chk = exact_rows(Lam_m + 3, mu_m + 5)
    for r in range(5):
        for c in range(21):
            pred = (
                rows_m[r][c]
                + C_L[r][c] * 3
                + C_mu[r][c] * 5
                + C_inv[r][c] * (Fraction(1) / (Lam_m + 3) - Fraction(1) / Lam_m)
                + C_mi[r][c] * ((mu_m + 5) / (Lam_m + 3) - mu_m / Lam_m)
            )
            assert pred == r_chk[r][c], f"S6 basis check failed at ({r},{c})"

    dL_iv = Lam_iv - S6IV(Lam_m)
    dmu_iv = mu_iv - S6IV(mu_m)
    dInv_iv = S6IV(Fraction(1)) / Lam_iv - S6IV(Fraction(1) / Lam_m)
    dMI_iv = dmu_iv * S6IV(Fraction(1) / Lam_m) + S6IV(mu_m) * dInv_iv + dmu_iv * dInv_iv
    r_iv = []
    for r in range(5):
        gL = sum(C_L[r][c] * y0[c] for c in range(21))
        gM = sum(C_mu[r][c] * y0[c] for c in range(21))
        gI = sum(C_inv[r][c] * y0[c] for c in range(21))
        gMI = sum(C_mi[r][c] * y0[c] for c in range(21))
        r_iv.append(-(S6IV(gL) * dL_iv + S6IV(gM) * dmu_iv + S6IV(gI) * dInv_iv + S6IV(gMI) * dMI_iv))

    A5 = [[None] * 5 for _ in range(5)]
    for i in range(5):
        for j in range(5):
            c = piv_cols[j]
            mL = sum(P0[i][t] * C_L[t][c] for t in range(5))
            mM = sum(P0[i][t] * C_mu[t][c] for t in range(5))
            mI = sum(P0[i][t] * C_inv[t][c] for t in range(5))
            mMI = sum(P0[i][t] * C_mi[t][c] for t in range(5))
            A5[i][j] = S6IV(1 if i == j else 0) + S6IV(mL) * dL_iv + S6IV(mM) * dmu_iv + S6IV(mI) * dInv_iv + S6IV(mMI) * dMI_iv
    b5 = [sum((S6IV(P0[i][t]) * r_iv[t] for t in range(5)), S6IV(0)) for i in range(5)]
    for k in range(5):
        piv = A5[k][k]
        assert piv.lo > 0, f"S6 Krawczyk pivot not > 0: {piv.lo}"
        A5[k] = [x / piv for x in A5[k]]
        b5[k] = b5[k] / piv
        for r in range(5):
            if r != k:
                f = A5[r][k]
                A5[r] = [A5[r][j] - f * A5[k][j] for j in range(5)]
                b5[r] = b5[r] - f * b5[k]

    y_iv = [S6IV(y0[c]) for c in range(21)]
    for idx, c in enumerate(piv_cols):
        y_iv[c] = S6IV(y0[c]) + b5[idx]
    Ys = s6_vec_to_mats(y_iv)
    min_piv = None
    for M in Ys:
        n = len(M)
        A = [[M[i][j] for j in range(n)] for i in range(n)]
        for k in range(n):
            pv = A[k][k]
            assert pv.lo > 0, f"S6 LDL^T pivot not > 0: {pv.lo}"
            min_piv = pv.lo if min_piv is None else min(min_piv, pv.lo)
            for i in range(k + 1, n):
                f = A[i][k] / pv
                for j in range(k + 1, n):
                    A[i][j] = A[i][j] - f * A[k][j]

    Z0 = S6IV(0)
    m0_iv = s6_eval_p32_mats(Lam_iv, mu_iv, R_iv, Z0, Z0, Z0, Z0, Z0)
    c0_vec_iv = s6_mats_to_vec(m0_iv)
    m0_vec_m = s6_mats_to_vec(m0_m)
    c0_mid = sum(m0_vec_m[j] * y0[j] for j in range(21))
    m0_diff_iv = [c0_vec_iv[j] - S6IV(m0_vec_m[j]) for j in range(21)]
    c0_iv = S6IV(c0_mid) + sum((m0_diff_iv[j] * S6IV(y0[j]) for j in range(21)), S6IV(0))
    for idx, c in enumerate(piv_cols):
        c0_iv = c0_iv + c0_vec_iv[c] * b5[idx]
    assert c0_iv.hi < 0, f"S6 c0 not < 0: {c0_iv.hi}"
    return min_piv, c0_iv.hi


def verify_suite6_top_band_splitting():
    print("\n" + "=" * 78)
    print("SUITE 6: Theorem 22 Zero-Float Full-V4-Enclosure Top-Band Exact Splitting")
    print("=" * 78)
    t_s6 = time.time()

    # 6A. p = 4/3, m = 2: full V4 Theorem 12 enclosure [860425/100000, 21511/2500]
    t0 = time.time()
    Lam_lo_43 = Fraction(860425, 100000)
    Lam_hi_43 = Fraction(21511, 2500)
    R_43 = Fraction(73, 20)
    xi1_43 = Fraction(-131, 200)
    mu_hi_43 = Fraction(1616, 10000)
    for Lq in [Lam_lo_43, (Lam_lo_43 + Lam_hi_43) / 2, Lam_hi_43]:
        assert s6_verify_p43_symbolic_cancellation(Lq, mu_hi_43 / 2, R_43, xi1_43) < 0
    k_sub = 15
    step = (Lam_hi_43 - Lam_lo_43) / k_sub
    worst_hi_43 = None
    for j in range(k_sub):
        sub_iv = S6IV(Lam_lo_43 + j * step, Lam_lo_43 + (j + 1) * step)
        A, B, C = s6_r1_quad_iv(sub_iv, R_43, xi1_43)
        assert A.lo > 0, f"S6 p=4/3 A not > 0 on sub {j}"
        v0 = C
        v1 = A * (mu_hi_43 * mu_hi_43) + B * mu_hi_43 + C
        assert v0.hi < 0 and v1.hi < 0, f"S6 p=4/3 failed on sub {j}"
        wh = max(v0.hi, v1.hi)
        worst_hi_43 = wh if worst_hi_43 is None else max(worst_hi_43, wh)
    g_lb_43 = Fraction(114155, 100000)
    assert g_lb_43 * g_lb_43 - g_lb_43 < mu_hi_43
    d_gap_ub_43 = Fraction(1) / g_lb_43
    assert d_gap_ub_43 < Fraction(87601, 100000)
    print(f"  [PASS] p=4/3 FULL V4 ENCLOSURE [{fmt_dec(Lam_lo_43, 5)}, {fmt_dec(Lam_hi_43, 5)}] (15 exact IV boxes, {time.time() - t0:.2f}s)")
    print(f"         mu in [0, 1616/10000]: R=73/20 => d_v < 20/73 ({fmt_dec(Fraction(20, 73), 6, round_up=True)}) | worst c0_hi = {fmt_dec(worst_hi_43, 8)} < 0")
    print(f"         mu >= 1616/10000:      g_+(1616/10000) > 114155/100000 => d_v < {fmt_dec(d_gap_ub_43, 6, round_up=True)} < 0.87601")

    # 6B. p = 3/2, m = 2: full V4 Theorem 12 enclosure [445337/100000, 890677/200000]
    t1 = time.time()
    Lam_lo_32 = Fraction(445337, 100000)
    Lam_hi_32 = Fraction(890677, 200000)
    Lam_iv_32 = S6IV(Lam_lo_32, Lam_hi_32)
    R_32 = Fraction(3, 2)
    json_path = os.path.join(HERE, "top_band_gap_certs_v5", "p32_iv_patches.json")
    with open(json_path, "r") as f:
        patches = json.load(f)
    cur = Fraction(0)
    worst_piv_32 = None
    worst_c0_32 = None
    for idx, pt in enumerate(patches):
        mlo = parse_frac(pt["mu_lo"])
        mhi = parse_frac(pt["mu_hi"])
        assert mlo == cur and mhi > mlo, f"S6 p=3/2 patch {idx} discontinuity: {mlo} != {cur}"
        piv_cols = pt["piv_cols"]
        free_vals = [parse_frac(s) for s in pt["free_vals"]]
        mpiv, c0hi = s6_verify_p32_iv_box(Lam_iv_32, S6IV(mlo, mhi), R_32, piv_cols, free_vals)
        worst_piv_32 = mpiv if worst_piv_32 is None else min(worst_piv_32, mpiv)
        worst_c0_32 = c0hi if worst_c0_32 is None else max(worst_c0_32, c0hi)
        cur = mhi
    assert cur == Fraction(9, 40), f"S6 p=3/2 did not reach 9/40: {cur}"
    m_lb_32 = Fraction(10976, 10000)
    assert m_lb_32 ** 3 - m_lb_32 < Fraction(9, 40)
    d_gap_ub_32 = Fraction(1) / (m_lb_32 * m_lb_32)
    assert d_gap_ub_32 < Fraction(8301, 10000)
    print(f"  [PASS] p=3/2 FULL V4 ENCLOSURE [{fmt_dec(Lam_lo_32, 6)}, {fmt_dec(Lam_hi_32, 6)}] ({len(patches)} exact IV patches, {time.time() - t1:.2f}s)")
    print(f"         mu in [0, 9/40]: R=3/2 => d_v < 2/3 ({fmt_dec(Fraction(2, 3), 6, round_up=True)}) | min LDL^T piv = {fmt_dec(worst_piv_32, 8)} > 0 | worst c0_hi = {fmt_dec(worst_c0_32, 8)} < 0")
    print(f"         mu >= 9/40:      m_+(9/40) > 10976/10000 => d_v < {fmt_dec(d_gap_ub_32, 6, round_up=True)} < 0.8301")

    # 6C. Suite 6 negative tamper test: inflate R_32 = 3/2 -> 10 on patch 0 -> MUST FAIL!
    pt0 = patches[0]
    caught = False
    try:
        s6_verify_p32_iv_box(
            Lam_iv_32, S6IV(parse_frac(pt0["mu_lo"]), parse_frac(pt0["mu_hi"])),
            Fraction(10), pt0["piv_cols"], [parse_frac(s) for s in pt0["free_vals"]],
        )
    except AssertionError:
        caught = True
    assert caught, "Suite 6 negative tamper test was NOT caught!"
    print(f"  [PASS] Suite 6 negative tamper test caught immediately! (Total Suite 6 time: {time.time() - t_s6:.2f}s)")


def main():
    t_all = time.time()
    verify_suite1_theorem4()
    lower_data = verify_suite2_lower_records()
    upper_data = verify_suite3_upper_bounds()
    verify_suite4_tamper_and_algebra(upper_data, lower_data)
    verify_suite5_multisummand_intervals()
    verify_suite6_top_band_splitting()
    print("\n" + "=" * 78)
    print(f"ALL EXACT ZERO-FLOAT CERTIFICATES PASSED (SUITES 1-6, 0 FLOATS, STDLIB ONLY, {time.time() - t_all:.1f}s)!")
    print("=" * 78)


if __name__ == "__main__":
    main()
