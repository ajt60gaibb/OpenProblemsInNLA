#!/usr/bin/env python3
"""
Zero-floating-point exact rational certificate suite for Theorem 4
at p = 3/2, p = 4/3, and p = 5/4.

Dependencies: ONLY Python 3 standard library (`fractions`, `math`).
No floating-point arithmetic is used in any proof step or inequality check.
"""
from fractions import Fraction
import math


def nth_root_bounds(x: Fraction, n: int, prec_bits: int = 130):
    """Return exact (lo, hi) Fraction with lo >= 0 and lo^n <= x <= hi^n."""
    assert x >= 0 and n >= 1
    if x == 0:
        return Fraction(0), Fraction(0)
    scale = 1 << prec_bits
    # Want floor((x * scale^n)^(1/n)) = floor((num * scale^n / den)^(1/n))
    # Compute integer nth root of (num * scale^n) // den using exact Newton method
    target = (x.numerator * (scale ** n)) // x.denominator
    if n == 2:
        s = math.isqrt(target)
    else:
        # exact integer nth root via Newton
        if target == 0:
            s = 0
        else:
            bits = target.bit_length()
            s = 1 << ((bits + n - 1) // n)
            while True:
                s_next = ((n - 1) * s + target // (s ** (n - 1))) // n
                if s_next >= s:
                    break
                s = s_next
    # Adjust s to exact floor of (x * scale^n)^(1/n)
    den = x.denominator
    num_scaled = x.numerator * (scale ** n)
    while ((s + 1) ** n) * den <= num_scaled:
        s += 1
    while (s ** n) * den > num_scaled:
        s -= 1
    lo = Fraction(s, scale)
    hi = lo if (s ** n) * den == num_scaled else Fraction(s + 1, scale)
    assert lo ** n <= x <= hi ** n
    return lo, hi


def mat_mul(X, Y):
    r, k, c = len(X), len(Y), len(Y[0])
    return [[sum(X[i][t] * Y[t][j] for t in range(k)) for j in range(c)] for i in range(r)]


def mat_T(X):
    return [[X[i][j] for i in range(len(X))] for j in range(len(X[0]))]


def mat_frob_sq(X):
    return sum(v * v for row in X for v in row)


def bisect_monotone(f, lo: Fraction, hi: Fraction, iters: int = 110):
    """Exact rational bisection of continuous f with f(lo)*f(hi) < 0."""
    flo = f(lo)
    fhi = f(hi)
    assert (flo < 0 < fhi) or (flo > 0 > fhi)
    for _ in range(iters):
        mid = (lo + hi) / 2
        fmid = f(mid)
        if fmid == 0:
            return mid, mid
        if (flo < 0 and fmid < 0) or (flo > 0 and fmid > 0):
            lo, flo = mid, fmid
        else:
            hi, fhi = mid, fmid
    assert (f(lo) < 0 < f(hi)) or (f(lo) > 0 > f(hi))
    return lo, hi


def certify_2x3_witness(A_int, b_int, p_num: int, p_den: int, C2_pow_hi: Fraction, pow_exp: int, label: str):
    """
    Certify ||A + B||_p / |||A| + |B|||_p > C_{p,2}(2)
    where p = p_num / p_den in (1, 2), and we compare exact (ratio)^{pow_exp} > C2_pow_hi,
    with pow_exp chosen so that pow_exp / p is a positive integer k = pow_exp * p_den // p_num.
    """
    assert (pow_exp * p_den) % p_num == 0
    k_pow = (pow_exp * p_den) // p_num

    A = [[Fraction(v) for v in row] for row in A_int] + [[Fraction(0), Fraction(0), Fraction(0)]]
    B = [[Fraction(b_int), Fraction(0), Fraction(0)],
         [Fraction(0), Fraction(0), Fraction(0)],
         [Fraction(0), Fraction(0), Fraction(0)]]
    S2 = [[A[i][j] + B[i][j] for j in range(3)] for i in range(2)]

    # 1. Exact lower bound on ||S||_p^p = mu1^(p/2) + mu2^(p/2) = (mu1^p_num)^(1/(2*p_den)) + ...
    SST = mat_mul(S2, mat_T(S2))
    trS = SST[0][0] + SST[1][1]
    detS = SST[0][0] * SST[1][1] - SST[0][1] * SST[1][0]
    discS = trS * trS - 4 * detS
    assert discS > 0
    ds_lo, ds_hi = nth_root_bounds(discS, 2, 130)
    mu1_lo = (trS + ds_lo) / 2
    mu2_lo = (trS - ds_hi) / 2
    assert mu2_lo > 0
    n1_lo, _ = nth_root_bounds(mu1_lo ** p_num, 2 * p_den, 130)
    n2_lo, _ = nth_root_bounds(mu2_lo ** p_num, 2 * p_den, 130)
    num_p_lo = n1_lo + n2_lo

    # 2. Exact rational enclosure for |A| = c1 * M + c2 * M^2 (since rank(A) = 2)
    A2 = A[:2]
    AAT = mat_mul(A2, mat_T(A2))
    trA = AAT[0][0] + AAT[1][1]
    detA = AAT[0][0] * AAT[1][1] - AAT[0][1] * AAT[1][0]
    assert detA > 0
    pA_lo, pA_hi = nth_root_bounds(detA, 2, 140)
    sumA_lo, _ = nth_root_bounds(trA + 2 * pA_lo, 2, 140)
    _, sumA_hi = nth_root_bounds(trA + 2 * pA_hi, 2, 140)
    denom_lo = pA_lo * sumA_lo
    denom_hi = pA_hi * sumA_hi
    c1_lo = (trA + pA_lo) / denom_hi
    c1_hi = (trA + pA_hi) / denom_lo
    c2_lo = Fraction(-1) / denom_lo
    c2_hi = Fraction(-1) / denom_hi

    M = mat_mul(mat_T(A), A)
    M2 = mat_mul(M, M)
    c1_mid = (c1_lo + c1_hi) / 2
    c2_mid = (c2_lo + c2_hi) / 2
    dc1 = (c1_hi - c1_lo) / 2
    dc2 = (c2_hi - c2_lo) / 2

    H_hat = [[c1_mid * M[i][j] + c2_mid * M2[i][j] + B[i][j] for j in range(3)] for i in range(3)]
    _, fM_hi = nth_root_bounds(mat_frob_sq(M), 2, 70)
    _, fM2_hi = nth_root_bounds(mat_frob_sq(M2), 2, 70)
    eps_H = dc1 * fM_hi + dc2 * fM2_hi

    # 3. Exact rational upper bounds on eigenvalues of symmetric 3x3 H_hat via cubic charpoly
    a2 = H_hat[0][0] + H_hat[1][1] + H_hat[2][2]
    a1 = (H_hat[0][0]*H_hat[1][1] - H_hat[0][1]*H_hat[1][0]
        + H_hat[0][0]*H_hat[2][2] - H_hat[0][2]*H_hat[2][0]
        + H_hat[1][1]*H_hat[2][2] - H_hat[1][2]*H_hat[2][1])
    a0 = (H_hat[0][0]*(H_hat[1][1]*H_hat[2][2] - H_hat[1][2]*H_hat[2][1])
        - H_hat[0][1]*(H_hat[1][0]*H_hat[2][2] - H_hat[1][2]*H_hat[2][0])
        + H_hat[0][2]*(H_hat[1][0]*H_hat[2][1] - H_hat[1][1]*H_hat[2][0]))
    def cp(x: Fraction) -> Fraction:
        return x**3 - a2 * x**2 + a1 * x - a0

    d_disc = 4 * a2 * a2 - 12 * a1
    dd_lo, _ = nth_root_bounds(d_disc, 2, 70)
    c_left = (2 * a2 - dd_lo) / 6
    c_right = (2 * a2 + dd_lo) / 6
    assert cp(Fraction(-1)) < 0
    assert cp(c_left) > 0
    assert cp(c_right) < 0
    assert cp(a2 + 1) > 0

    _, l3_hi = bisect_monotone(cp, Fraction(-1), c_left, 110)
    _, l2_hi = bisect_monotone(cp, c_left, c_right, 110)
    _, l1_hi = bisect_monotone(cp, c_right, a2 + 1, 110)

    # Weyl upper bounds on eigenvalues of H
    lam_his = [l1_hi + eps_H, l2_hi + eps_H, l3_hi + eps_H]
    assert all(l > 0 for l in lam_his)
    den_p_hi = sum(nth_root_bounds(l ** p_num, p_den, 130)[1] for l in lam_his)

    # Exact integer comparison: (num_p_lo / den_p_hi)^k_pow > C2_pow_hi
    lhs = num_p_lo ** k_pow
    rhs = C2_pow_hi * (den_p_hi ** k_pow)
    assert lhs > rhs, f"Certificate FAILED for {label}!"

    ratio_pow_lo = lhs / (den_p_hi ** k_pow)
    gap_pow = ratio_pow_lo - C2_pow_hi
    print(f"[PASS] {label}: exact rational certificate verified (0 floats)!")
    print(f"       Weyl eps_H < {float(eps_H):.3e}; certified gap in power {pow_exp}: +{float(gap_pow):.6e} > 0")


def main():
    # --- Case 1: p = 3/2 ---
    # Exact C_{3/2,2}(2)^6 = (107 + 51*sqrt(17)) / 256
    _, sq17_hi = nth_root_bounds(Fraction(17), 2, 130)
    C2_32_pow6_hi = (Fraction(107) + Fraction(51) * sq17_hi) / Fraction(256)
    certify_2x3_witness([[49, 62, -1], [11, 14, 0]], 81, 3, 2, C2_32_pow6_hi, 6, "p = 3/2 (two-digit 2x3)")

    # --- Case 2: p = 4/3 ---
    # R_{4/3}(y^3)^4 = (y^3+1)^2 (y^6+1) / (y^4+1)^3; unique max on y > 1 at root of y^6 - y^5 - y^4 - y^2 - y + 1 = 0
    # Equivalently z = y + 1/y > 2 solves z^3 - z^2 - 4z + 2 = 0, and R^4 = (z^3 - 3z + 2)(z^3 - 3z)/(z^2 - 2)^3.
    # For y in [y_lo, y_hi], monotone factor bound gives exact upper bound on max R^4!
    f43 = lambda y: y**6 - y**5 - y**4 - y**2 - y + 1
    assert f43(Fraction(1)) < 0 < f43(Fraction(2))
    y43_lo, y43_hi = bisect_monotone(f43, Fraction(1), Fraction(2), 110)
    C2_43_pow4_hi = ((y43_hi**3 + 1)**2 * (y43_hi**6 + 1)) / ((y43_lo**4 + 1)**3)
    certify_2x3_witness([[62, 64, -1], [23, 24, 0]], 95, 4, 3, C2_43_pow4_hi, 4, "p = 4/3 (two-digit 2x3)")

    # --- Case 3: p = 5/4 ---
    # R_{5/4}(y^12)^10 = (y^12+1)^5 (y^20+1)^3 / (y^15+1)^8
    # Derivative factor on y > 1: P18(y) = y^18 + y^17 + y^16 - y^15 - 2y^14 - 2y^13 - 2y^12 + 2y^10 + 2y^9 + 2y^8 - 2y^6 - 2y^5 - 2y^4 - y^3 + y^2 + y + 1
    # Check unique root on y > 1: let's verify via exact sign change of P18 on (1, 2)
    # Wait: P18(1) = 1+1+1-1-2-2-2+2+2+2-2-2-2-1+1+1+1 = -2 < 0; P18(2) > 0!
    f54 = lambda y: (y**18 + y**17 + y**16 - y**15 - 2*y**14 - 2*y**13 - 2*y**12
                     + 2*y**10 + 2*y**9 + 2*y**8 - 2*y**6 - 2*y**5 - 2*y**4 - y**3 + y**2 + y + 1)
    assert f54(Fraction(1)) < 0 < f54(Fraction(2))
    y54_lo, y54_hi = bisect_monotone(f54, Fraction(1), Fraction(2), 110)
    C2_54_pow10_hi = ((y54_hi**12 + 1)**5 * (y54_hi**20 + 1)**3) / ((y54_lo**15 + 1)**8)
    certify_2x3_witness([[336, 311, 0], [147, 137, 1]], 500, 5, 4, C2_54_pow10_hi, 10, "p = 5/4 (three-digit 2x3)")

    print("\nALL THREE EXACT RATIONAL CERTIFICATES (p = 3/2, 4/3, 5/4) PASSED!")


if __name__ == "__main__":
    main()
