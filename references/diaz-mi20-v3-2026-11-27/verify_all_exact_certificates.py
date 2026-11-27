#!/usr/bin/env python3
"""
verify_all_exact_certificates.py
================================
Author:      Marcio Díaz (Space Research AI, https://spaceresearch.ai, marcio.diaz@gmail.com)
Date:        November 27, 2026
Purpose:     100% ZERO-FLOATING-POINT, ZERO-EXTERNAL-DEPENDENCY master verifier for ALL
             exact rational certificates of Open Problem MI-20 (Version 3):
               - Suite 1 (Theorem 4): Small-integer 2x3 witnesses at p = 3/2, 4/3, 5/4
               - Suite 2 (Theorem 11): World-record 42x42 self-similar tree lower bounds
                   * C_{4/3,2}(inf) > 1.0183715755  (beats Holden's 1.018371575)
                   * C_{3/2,2}(inf) > 1.03643716806 (beats n=14 PSD 1.036437168055)
               - Suite 3 (Theorem 12): Unconditional Two-State Pinch upper-bound chains
                   * p = 4/3, m = 2: Lam <= 86045/10000 => C_{4/3,2}(inf) <= (86045/80000)^(1/4)
                                     = 1.0183777756... (27.2x tighter than Holden's 1.01854047)
                   * p = 3/2, m = 2: Lam <= 44536/10000 => C_{3/2,2}(inf) <= (44536/40000)^(1/3)
                                     = 1.0364549111... (459x tighter than Holden's 1.04458345)
               - Suite 4: Negative tamper tests & literal noncommuting rational matrix sanity check

Invocation (strictly stdlib-only, no site-packages):
    python3 -B -S verify_all_exact_certificates.py

Every single mathematical decision uses exclusively Python's arbitrary-precision `int`
and `fractions.Fraction`. No `float` value ever enters any bound or assertion.
"""
from fractions import Fraction
import json
import math
import os
import sys

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
    """Exact rational bracket (lo, hi) for sigma_+(L) = h_+(L)^2 - h_+(L) at p = 4/3 (kappa = 2),
    where h_+(L) > 1/2 is the unique root of (1 + h)^3 - L * h = 0 on (1/2, inf)."""
    f = lambda h: (1 + h) ** 3 - L * h
    hi = Fraction(2)
    while f(hi) <= 0:
        hi *= 2
    h_lo, h_hi = bisect_increasing(f, Fraction(1, 2), hi, 90)
    assert h_lo >= Fraction(1, 2)
    # h -> h^2 - h is strictly increasing on [1/2, inf)
    return h_lo * h_lo - h_lo, h_hi * h_hi - h_hi


def sigma_plus_bounds_p32(L: Fraction):
    """Exact rational bracket (lo, hi) for sigma_+(L) = m_+(L)^3 - m_+(L) at p = 3/2 (kappa = 3/2),
    where m_+(L) = sqrt(h_+(L)) > 1/sqrt(3) is the unique root of (1 + m^2)^2 - L * m = 0 on (1, inf)
    for L > 4."""
    f = lambda m: (1 + m * m) ** 2 - L * m
    # For L > 4, f(1) = 4 - L < 0 and m -> (1+m^2)^2 - L*m is strictly increasing on [1, inf)
    # since f'(m) = 4m(1+m^2) - L; wait: at L <= 4.72 and m >= 1, 4m(1+m^2) >= 8 > 4.72 > L!
    assert L > 4 and L < 8
    hi = Fraction(2)
    while f(hi) <= 0:
        hi *= 2
    m_lo, m_hi = bisect_increasing(f, Fraction(1), hi, 90)
    assert m_lo >= Fraction(1)
    # m -> m^3 - m is strictly increasing on [1, inf)
    return m_lo ** 3 - m_lo, m_hi ** 3 - m_hi


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

    # 4. Verify all 4 corners are present and EXACTLY pass both zero residual AND exact LDL^T > 0!
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
    return L_lo, L_hi, P_lo, P_hi, tau_bar, use_D_le_I, min_piv


def verify_interval_coverage(rects_meta, start_cap: Fraction, final_cap: Fraction,
                             c_kap_hi: Fraction, sigma_fn, mode_name: str):
    """Verify with 100% exact rationals that the rectangles seamlessly refute ALL
    (Lam, tau) with Lam in [final_cap, start_cap] and tau in [sigma_+(Lam), c_kap_hi]."""
    # Group rectangles by their exact Lambda interval [L_lo, L_hi]
    by_L = {}
    for L_lo, L_hi, P_lo, P_hi, tau_bar, use_D in rects_meta:
        by_L.setdefault((L_lo, L_hi), []).append((P_lo, P_hi, tau_bar, use_D))

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
        sig_lo_min, _ = sigma_fn(L_lo)
        _, sig_hi_max = sigma_fn(L_hi)
        sys1 = [p for p in pieces if p[3]]      # use_D_le_I = True
        sys2 = [p for p in pieces if not p[3]]  # use_D_le_I = False

        if sys1:
            # Sys1 must cover P = sigma_+(Lam) across ALL Lam in [L_lo, L_hi]
            # (since sigma_+ is strictly increasing in Lam, [sigma_+(L_lo), sigma_+(L_hi)] <= [P_lo, P_hi])
            tau_split = None
            for P_lo, P_hi, tau_bar, _ in sys1:
                assert P_lo <= sig_lo_min and sig_hi_max <= P_hi, (
                    f"{mode_name} [{L_lo},{L_hi}]: Sys1 P=[{P_lo},{P_hi}] does not cover "
                    f"sigma_+ in [{fmt_dec(sig_lo_min,8)}, {fmt_dec(sig_hi_max,8)}]"
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
        for P_lo, P_hi, tau_bar, _ in sys2_sorted:
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
        L_lo, L_hi, P_lo, P_hi, tb, useD, mp = verify_pinch_rectangle(rect, 'p43')
        meta_43.append((L_lo, L_hi, P_lo, P_hi, tb, useD))
        print(f"    [PASS] {rect['label']:36s} | 0 residual | min_LDL_piv={fmt_dec(mp, 10)}")
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
        L_lo, L_hi, P_lo, P_hi, tb, useD, mp = verify_pinch_rectangle(rect, 'p32')
        meta_32.append((L_lo, L_hi, P_lo, P_hi, tb, useD))
        print(f"    [PASS] {rect['label']:36s} | 0 residual | min_LDL_piv={fmt_dec(mp, 10)}")
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

    # 4d. Literal noncommuting 2x2 rational matrix sanity check of canon(w) on D v = v
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

    print("  [PASS] All 3 negative tamper tests caught immediately!")
    print("  [PASS] Literal 2x2 noncommuting rational matrix check of canon(w) on D v = v passed!")


def main():
    verify_suite1_theorem4()
    lower_data = verify_suite2_lower_records()
    upper_data = verify_suite3_upper_bounds()
    verify_suite4_tamper_and_algebra(upper_data, lower_data)
    print("\n" + "=" * 78)
    print("ALL EXACT ZERO-FLOAT CERTIFICATES PASSED (SUITES 1-4, 0 FLOATS, STDLIB ONLY)!")
    print("=" * 78)


if __name__ == "__main__":
    main()
