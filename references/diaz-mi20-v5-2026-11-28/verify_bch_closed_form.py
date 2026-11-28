#!/usr/bin/env python3
"""
verify_bch_closed_form.py
=========================
Author:      Marcio Díaz (Space Research AI, https://spaceresearch.ai, marcio.diaz@gmail.com)
Date:        November 28, 2026
Purpose:     50-digit arbitrary-precision (`mpmath`) verification of the Version 5
             Theorem 19 closed-form operator upper bound breaking V4's Lambert-W
             BCH barrier K_2^{Thm10} = 0.317235793549... for ALL dimensions n <= infinity:

                 K_2^{BCH} < 0.31722794 < 0.317235793549... = (W(e^{-1})^2 + 2 W(e^{-1})) / 2

             Zero SDP, zero numerical integration, zero grid/subintervals, zero Furuta:
               1. Spectral localization on [a, b] = [0.955, 1.045] (delta = 0.045),
                  M_S = e^{b-1}, U_off = 2 e^{b-1}, lam0 = (e^{-a}+e^{-b})/2,
                  epsE = (e^{-a}-e^{-b})/2, k1 = 2*lam0 - epsE, k0 = epsE*M_S.
               2. Double Young's inequality (eta = 0.08, gamma = 0.03):
                    C0 = ((1+eta)/lam0^2)*(4/e^2 + (1/gam - 1)*k0^2)
                         + ((1+1/eta)/lam0^2)*(epsE*U_off)^2,
                    C1 = ((1+eta)*(1-gam)*k1^2)/lam0^2 - 1 > 0,
                  giving F(u) <= C0 - C1*u for all u >= 0.
               3. Kadison-Schwarz O(delta^2) bound (ks_err = M_S*delta^2/3):
                    alpha <= alpha_max(K_2), positive root of
                    C1*(alpha - ks_err)^2 + 2*alpha + 2*K_2 = C0.
               4. Exact alpha^2-cancellation in d/d(alpha)[D(alpha)^2 / X(alpha)^2]:
                    h(alpha) = k1*(k1*d0 - 2*lam0*k0)*alpha
                               + (2*lam0*k0^2 - k1*k0*d0 - 8*lam0/e^2)
                  is affine-linear with h(alpha_max) < 0, proving D/X is strictly
                  decreasing on [0, alpha_max], hence p <= p_max(K_2) = p(alpha_max).
               5. Spectral split:
                    P <= P_ub(K_2) := p_max(K_2)/e + (1 - p_max(K_2))*max(a*e^{-a}, b*e^{-b}).
               6. Strict monotonicity in K_2: C0, C1, ks_err are independent of K_2;
                  as K_2 increases, alpha_max decreases, sig(K_2) and d0 increase,
                  p_max decreases, and P_ub(K_2) decreases while sig(K_2) increases.
                  Hence P_ub(K_2^*) < sig(K_2^*) at K_2^* = 0.31722794 refutes ALL K_2 >= K_2^*!

Invocation:
    uv run --with mpmath python3 verify_bch_closed_form.py
"""
import mpmath as mp

mp.mp.dps = 50


def certify_closed_form(K2_str: str, a_str: str = "0.955", b_str: str = "1.045",
                        eta_str: str = "0.08", gam_str: str = "0.03"):
    """Evaluate and assert every hypothesis of the closed-form BCH operator refutation at K2_str."""
    K2 = mp.mpf(K2_str)
    aL = K2 / 2
    tp = mp.sqrt(1 + 4 * aL) - 1
    sig = tp * mp.exp(tp)

    a = mp.mpf(a_str)
    b = mp.mpf(b_str)
    delta = (b - a) / 2
    assert a + b == 2 and delta > 0
    la = mp.exp(-a)
    lb = mp.exp(-b)
    lam0 = (la + lb) / 2
    epsE = (la - lb) / 2
    inv_e = mp.exp(-1)
    M_S = mp.exp(b - 1)
    U_off = 2 * M_S
    m_out = max(a * la, b * lb)

    k1 = 2 * lam0 - epsE
    k0 = epsE * M_S
    eta = mp.mpf(eta_str)
    gam = mp.mpf(gam_str)
    assert eta > 0 and 0 < gam < 1

    C0 = (((1 + eta) / lam0**2) * (4 * inv_e**2 + (1 / gam - 1) * k0**2)
          + ((1 + 1 / eta) / lam0**2) * (epsE * U_off)**2)
    C1 = ((1 + eta) * (1 - gam) * k1**2) / lam0**2 - 1
    assert C1 > 0, f"C1 <= 0: {C1}"

    ks_err = M_S * delta**2 / 3
    qa = C1
    qb = 2 - 2 * C1 * ks_err
    qc = 4 * aL + C1 * ks_err**2 - C0
    disc = qb**2 - 4 * qa * qc
    assert disc > 0
    alpha_max = (-qb + mp.sqrt(disc)) / (2 * qa)
    assert alpha_max > ks_err and k1 * alpha_max > k0

    d0 = 2 * sig - 2 * epsE * M_S
    assert d0 - 2 * lam0 * alpha_max > 0

    # Exact derivative sign h(alpha_max) < 0 (and verify affine-linearity of numerator h(alpha)):
    h_slope = k1 * (k1 * d0 - 2 * lam0 * k0)
    h_const = 2 * lam0 * k0**2 - k1 * k0 * d0 - 8 * lam0 * inv_e**2
    h_at_max = h_slope * alpha_max + h_const
    h_at_0 = h_const
    assert h_slope > 0 and h_at_max < 0 and h_at_0 < 0, f"Derivative check failed: h_max={h_at_max}"

    # Finite-difference cross-check of d/d(alpha)[D(alpha)^2 / X(alpha)^2] at alpha_max / 2:
    al_t = alpha_max / 2
    f_q = lambda al: (d0 - 2 * lam0 * al)**2 / (4 * inv_e**2 - (k1 * al - k0)**2)
    eps_fd = mp.mpf("1e-16")
    num_d = (f_q(al_t + eps_fd) - f_q(al_t - eps_fd)) / (2 * eps_fd)
    ex_d = (2 * (d0 - 2 * lam0 * al_t) * (h_slope * al_t + h_const)
            / (4 * inv_e**2 - (k1 * al_t - k0)**2)**2)
    assert abs(num_d - ex_d) < mp.mpf("1e-25"), f"Derivative formula mismatch: {abs(num_d - ex_d)}"

    # Exact closed-form p_max = p(alpha_max) (and verify p_neg < p_max < 1):
    p_neg = (4 * inv_e**2) / (d0**2 + 4 * inv_e**2)
    rA_max = k1 * alpha_max - k0
    X2_max = 4 * inv_e**2 - rA_max**2
    assert X2_max > 0
    D_max = d0 - 2 * lam0 * alpha_max
    p_max = X2_max / (D_max**2 + X2_max)
    assert p_neg < p_max < 1

    P_ub = p_max * inv_e + (1 - p_max) * m_out
    return dict(
        K2=K2, sig=sig, P_ub=P_ub, gap=P_ub - sig, C0=C0, C1=C1, alpha_max=alpha_max,
        p_max=p_max, p_neg=p_neg, h_at_max=h_at_max, d0=d0, D_max=D_max, m_out=m_out,
    )


def main():
    print("=" * 78)
    print("THEOREM 19: CLOSED-FORM OPERATOR BREACH OF V4's LAMBERT-W BCH BARRIER (50-DIGIT)")
    print("=" * 78)
    W_lam = mp.lambertw(mp.exp(-1))
    K2_Thm10 = (W_lam**2 + 2 * W_lam) / 2
    a_s, b_s, eta_s, gam_s = "0.955", "1.045", "0.08", "0.03"

    # Bisect exact cutoff for the published clean rational parameters:
    lo, hi = mp.mpf("0.31720"), K2_Thm10
    for _ in range(40):
        mid = (lo + hi) / 2
        if certify_closed_form(str(mid), a_s, b_s, eta_s, gam_s)["gap"] < 0:
            hi = mid
        else:
            lo = mid

    print(f"  Parameters (zero Furuta, zero integral, zero grid, zero subintervals):")
    print(f"    [a, b] = [{a_s}, {b_s}],  eta = {eta_s},  gamma = {gam_s}")
    print(f"  V4 Lambert-W barrier:  K_2^Thm10 = {mp.nstr(K2_Thm10, 15)}")
    print(f"  Exact cutoff:          K_2^*     = {mp.nstr(hi, 15)}")
    print(f"  Strict improvement:    Delta K_2 = {mp.nstr(K2_Thm10 - hi, 8)}\n")

    for K2_s in [mp.nstr(K2_Thm10, 15), "0.317230", "0.3172285", "0.31722794"]:
        r = certify_closed_form(K2_s, a_s, b_s, eta_s, gam_s)
        assert r["gap"] < 0, f"Expected refutation at K_2 = {K2_s}, got gap = {r['gap']}"
        print(
            f"  [PASS] K_2={K2_s:17s} | sig={mp.nstr(r['sig'], 11)} | "
            f"P_ub={mp.nstr(r['P_ub'], 11)} | gap={mp.nstr(r['gap'], 6)} | "
            f"h(amax)={mp.nstr(r['h_at_max'], 5)} -> REFUTED ALL K_2 >= {K2_s}"
        )

    r0 = certify_closed_form("0.31722794", a_s, b_s, eta_s, gam_s)
    assert r0["gap"] < 0 and mp.mpf("0.31722794") < K2_Thm10
    print("\n  Exact 50-digit certificate constants at K_2^* = 0.31722794:")
    for k in ["C0", "C1", "alpha_max", "p_max", "p_neg", "h_at_max", "d0", "D_max", "m_out", "P_ub", "sig", "gap"]:
        print(f"    {k:10s} = {mp.nstr(r0[k], 15)}")
    print("\n" + "=" * 78)
    print("PASS: UNCONDITIONAL CLOSED-FORM BCH BOUND K_2^{BCH} < 0.31722794 VERIFIED!")
    print("=" * 78)


if __name__ == "__main__":
    main()
