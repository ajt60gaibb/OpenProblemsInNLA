"""
100% ZERO-FLOAT, ZERO-GAP, 100% CLOSED-FORM mpmath.iv CERTIFICATION OF THE ALL-m THEOREM AT p = 4/3
(PART 2: MODULES 3 AND 4 — UNCONDITIONAL JENSEN DUAL-WITNESS UPPER BOUND):

Together with Part 1 (rigorous_iv_p43_all_m_part1.py, Modules 0, 1, 2), this script certifies
the unconditional Jensen dual-witness upper bound
    T_tilde(delta) <= [ T_0^2/(T_0 + delta) + (2c + c^2)*delta ] / g_min^2
                    < T_0 + (T_0 / sig_+(a)) * delta = (m/(m-1)) * (sig_+(a) + delta)
for EVERY integer m >= 2 (i.e. EVERY a >= 1.1407) and EVERY delta in (0, d_ub(a)]!

Exact Part 1 constants: C_E = 5.25, C_G = 0.32, C0_H = 2.40, C1_H = 3.75, exact d_ub(s) formula.
ZERO float(), ZERO float literals, ZERO numpy/scipy/math inside any certified proof branch!

ARCHITECTURE (exhaustive seam-checked cover of ALL a >= 1.1407, ALL delta in (0, d_ub(a)], ALL (u, v) in [0, 1] x (0, 1]):
  MODULE 3 (Large a >= 7.0, compact s = 1/a in [0, ceil(1/7)]):
    - Step 3A: Rigorous T_0 enclosure & target inequality M(T_0; s, delta) / s^4 > 0, g_min > 0.
    - Step 3B-P1: Singular corner P1 = [0, 0.35]x(0, 0.35] U [0.35, 0.70]x(0, 0.20] via 3 exhaustive projective charts.
    - Step 3B-OUT: Complement P2 U P3 U P4 via direct + exact (s^4, s^3*xi, s^3*zeta, xi*zeta)-factored & MVT/AM-GM bounds.

  MODULE 4 (Compact finite a in [floor(1.1407), 7.0]):
    - Step 4A (Corner [0, 0.04] x (0, 0.04] for ALL a in [floor(1.1407), 7.0]):
      Inner (al + be <= 20*eps) & Outer (al + be >= 20*eps) boundary-layer certification with baseline c_4a(a).
      Monotone increasing in c, so certifying c_band(a) > c_4a(a) in Bands B and C covers the corner everywhere!
    - Band B (a in [3.5, 7.0], s in [floor(1/7), ceil(1/3.5)]):
      100% closed-form witness (c = theta_0(s), kappa_0 = 0.20, ea = 0.005, u_split = 0.30).
      Step B-1 (M/s^4 > 0, g_min > 0, th0 > c_4a), Step B-2 (Zone 1a & Zone 1b), Step B-3 (Zone 2).
    - Band C (a in [floor(1.1407), 3.50]):
      100% closed-form 7 sub-bands (B0, B1a, B1b, B2a, B2, B3, B4; c = alpha*theta_0(1/a) > c_4a(a)) with certified
      quadratic gt(s) <= 0, universal Z1a (c = (19/32)*theta_0 <= c_band, gt = 0), and Baumann optimal-center
      4-variable forward-mode interval AD (Dual4 MVF) on zero-pole P / V across Z1b..Z2.
"""

import multiprocessing as mp_proc
import os
import time
import mpmath as mp
from mpmath import iv

mp.mp.dps = 30
iv.dps = 25

# Exact Part 1 certified constants
C_E = iv.mpf("5.25")
C_G = iv.mpf("0.32")
CGCE = C_G * C_E           # 1.68
CGCE2 = C_G * (C_E ** 2)   # 8.82
C0_H = iv.mpf("2.40")
C1_H = iv.mpf("3.75")

# Shared seam / domain geometry constants
U35 = mp.mpf("0.35")
V20 = mp.mpf("0.20")
U70 = mp.mpf("0.70")
U_CUT = mp.mpf("0.04")
V_CUT = mp.mpf("0.04")
XF_STAR = iv.mpf("0.65")
U_STAR = iv.mpf("0.35")
M_CUT = iv.mpf("20")

# Module 3 & Band B closed-form parameters
KAPPA0_M3 = iv.mpf("0.15")
KAPPA0_B = iv.mpf("0.20")
EA_B = iv.mpf("0.005")
OM_EA_B = 1 - EA_B
U_SPLIT_B = mp.mpf("0.30")


def _init_worker():
    mp.mp.dps = 30
    iv.dps = 25


# ============================================================================
# SHARED PURE-iv PRIMITIVES
# ============================================================================
def iv_pos(x):
    return iv.mpf([max(mp.mpf(0), mp.mpf(x.a)), max(mp.mpf(0), mp.mpf(x.b))])


def iv_unit(x):
    """Intersect x with [0, 1] when mathematically guaranteed in [0, 1]."""
    lo = max(mp.mpf(0), mp.mpf(x.a))
    hi = min(mp.mpf(1), mp.mpf(x.b))
    assert lo <= hi
    return iv.mpf([lo, hi])


def d_ub_iv(sb):
    """Exact d_ub(s) formula from Part 1 (Module 1, Part 1C)."""
    lamb = (sb ** 2) / ((1 + sb) ** 3)
    d36 = 1 - iv.mpf("3.6") * lamb
    x1 = lamb / d36
    P1 = 2 / d36 + lamb / (d36 ** 2)
    op = (1 + x1) ** 2
    A1 = (P1 + op) / (1 - lamb * op) - 1 / (d36 ** 2)
    Ad = 1 + lamb * A1
    cb = C0_H + C1_H * lamb
    B1 = cb / (1 - lamb * cb)
    return ((1 - sb) / ((1 + sb) ** 3)) * (B1 - A1) / Ad


def d_ub_from_a_iv(ab):
    return d_ub_iv(1 / ab)


def d_ub_tight_iv(a0, a1, n_sub=16):
    pts = [a0] + [a0 + (a1 - a0) * mp.mpf(k) / mp.mpf(n_sub) for k in range(1, n_sub)] + [a1]
    lo = mp.mpf("1e9")
    hi = mp.mpf("-1e9")
    for k in range(n_sub):
        assert pts[k] <= pts[k + 1]
        d = d_ub_from_a_iv(iv.mpf([pts[k], pts[k + 1]]))
        if mp.mpf(d.a) < lo:
            lo = mp.mpf(d.a)
        if mp.mpf(d.b) > hi:
            hi = mp.mpf(d.b)
    return iv.mpf([lo, hi])


def c_of_a_step4a_iv(a):
    """Exact zero-wrapping baseline boundary weight for Step 4A corner:
       c_4a(a) = (13/10) * (1 - 0.65) * (1 + 1/a)^2 / (a^3 + 2.35*a^2 + 2*a + 1)."""
    return (iv.mpf(13) / iv.mpf(10)) * U_STAR * ((1 + 1 / a) ** 2) / ((a ** 3) + (3 - XF_STAR) * (a ** 2) + 2 * a + 1)


def th0_from_s_iv(sb):
    phi0 = 1 / (1 + 3 * sb + 2 * (sb ** 2) + sb ** 3)
    return (sb ** 3) * ((1 + sb) ** 2) * phi0


def K0_uv_iv(u, v, a):
    """Positive-sum zero-cancellation K_0(a*(1-u), a*(1-v); a) for u, v in [0, 1], a > 1."""
    al = u / (1 + 1 / a); be = v / (1 + 1 / a)
    w = 1 - (1 - al) * (1 - be)
    den = 1 + a * w
    xi = 1 - u; ze = 1 - v
    br = (a - 1) * (a + 2) + 1 / (a + 1) + (a ** 2) * (xi + ze) + (a ** 3) * xi * ze / (a + 1)
    num = (a ** 2) * ((al - be) ** 2) + al * be * br
    return (a + 1) * num / den


def K0_ua_iv(u, a):
    return (a ** 4) * (u ** 2) / (a + 1 + (a ** 2) * u)


def K0hat_uv_iv(u, v, s):
    """Exact intersection of positive-sum (al, be) form and tight (xi, ze) form of K_0hat = s^2 * K_0."""
    al = u / (1 + s); be = v / (1 + s)
    z = (1 - al) * (1 - be); w = 1 - z
    xi = 1 - u; ze = 1 - v
    br = (1 - s) * (1 + 2 * s) + (s ** 3) / (1 + s) + (xi + ze) + xi * ze / (1 + s)
    k1 = (1 + s) * (((al - be) ** 2) + al * be * br) / (s + w)
    spx = s + xi; spz = s + ze
    den2 = ((1 + s) ** 3) - spx * spz
    if mp.mpf(den2.a) > 0:
        k2 = (1 - s - xi * ze) + (s ** 2) * spx * spz / den2
        lo = max(mp.mpf(k1.a), mp.mpf(k2.a))
        hi = min(mp.mpf(k1.b), mp.mpf(k2.b))
        if lo <= hi:
            return iv.mpf([lo, hi])
    return k1


def K0hat_u0_iv(u, s):
    den = u + s + s * s
    if mp.mpf(den.a) > 0:
        return (u ** 2) / den
    return iv.mpf([mp.mpf(0), mp.mpf(u.b)])


def K0hat_ua_exact(u, s):
    """Exact monotone enclosure of u^2 / (u + s + s^2) (increasing in u >= 0, decreasing in s > 0)."""
    assert mp.mpf(u.a) >= 0 and mp.mpf(s.a) > 0
    u0, u1 = iv.mpf(mp.mpf(u.a)), iv.mpf(mp.mpf(u.b))
    s0, s1 = iv.mpf(mp.mpf(s.a)), iv.mpf(mp.mpf(s.b))
    lo = (u0 * u0) / (u0 + s1 + s1 * s1)
    hi = (u1 * u1) / (u1 + s0 + s0 * s0)
    return iv.mpf([mp.mpf(lo.a), mp.mpf(hi.b)])


def D_ub_uv_iv(u, v, s):
    al = u / (1 + s); be = v / (1 + s)
    w = al + be - al * be
    z = 1 - w
    sw = s + w
    if mp.mpf(sw.a) > 0:
        rat = iv_unit(s / sw)
    else:
        rat = iv.mpf([mp.mpf(0), mp.mpf(1)])
    return CGCE2 * rat * (z ** 3)


def D_uv_s_iv(u, v, s, eps_b):
    al = u / (1 + s); be = v / (1 + s)
    z = (1 - al) * (1 - be); w = 1 - z
    assert mp.mpf(w.a) > 0, f"w.a not > 0: {w}"
    return CGCE2 * s * (z ** 3) / ((1 + eps_b * z / w) * (s + w))


def dD_mono_s_iv(u, v, s, d0, d1):
    """Exact monotone enclosure of s^2 * delta * D_{xy}(delta) on delta in [d0, d1]."""
    al = u / (1 + s); be = v / (1 + s)
    z = (1 - al) * (1 - be); w = 1 - z
    s2 = s * s; A_inv = (s ** 3) / (1 + s)
    if d0 == 0 or mp.mpf(w.a) == 0:
        lo = mp.mpf(0)
    else:
        ep0 = C_E * iv.sqrt(iv.mpf(d0) * A_inv)
        lo = mp.mpf((s2 * iv.mpf(d0) * CGCE2 * s * (z ** 3) / ((1 + ep0 * z / w) * (s + w))).a)
    if d1 == 0:
        hi = mp.mpf(0)
    else:
        ep1 = C_E * iv.sqrt(iv.mpf(d1) * A_inv)
        if mp.mpf(w.a) > 0:
            rat1 = 1 / (1 + ep1 * z / w)
        else:
            wb_hi = iv.mpf(mp.mpf(w.b))
            rat1 = wb_hi / (wb_hi + ep1 * z)
        hi = mp.mpf((s2 * iv.mpf(d1) * CGCE2 * s * (z ** 3) * rat1 / (s + w)).b)
    return iv.mpf([lo, hi])


# ============================================================================
# 4-VARIABLE FORWARD-MODE INTERVAL AD (Dual4) & BAUMANN OPTIMAL CENTER
# ============================================================================
class Dual4:
    """Pure mpmath.iv 4-variable forward-mode interval AD (outward-rounded derivatives)."""
    __slots__ = ("v", "d0", "d1", "d2", "d3")

    def __init__(self, v, d0=None, d1=None, d2=None, d3=None):
        z = iv.mpf(0)
        self.v = v if isinstance(v, iv.mpf) else iv.mpf(v)
        self.d0 = z if d0 is None else d0
        self.d1 = z if d1 is None else d1
        self.d2 = z if d2 is None else d2
        self.d3 = z if d3 is None else d3

    def __add__(self, o):
        if isinstance(o, Dual4):
            return Dual4(self.v + o.v, self.d0 + o.d0, self.d1 + o.d1, self.d2 + o.d2, self.d3 + o.d3)
        return Dual4(self.v + o, self.d0, self.d1, self.d2, self.d3)

    def __radd__(self, o):
        return self.__add__(o)

    def __sub__(self, o):
        if isinstance(o, Dual4):
            return Dual4(self.v - o.v, self.d0 - o.d0, self.d1 - o.d1, self.d2 - o.d2, self.d3 - o.d3)
        return Dual4(self.v - o, self.d0, self.d1, self.d2, self.d3)

    def __rsub__(self, o):
        return Dual4(o - self.v, -self.d0, -self.d1, -self.d2, -self.d3)

    def __neg__(self):
        return Dual4(-self.v, -self.d0, -self.d1, -self.d2, -self.d3)

    def __mul__(self, o):
        if isinstance(o, Dual4):
            sv, ov = self.v, o.v
            return Dual4(sv * ov, self.d0 * ov + sv * o.d0, self.d1 * ov + sv * o.d1,
                         self.d2 * ov + sv * o.d2, self.d3 * ov + sv * o.d3)
        return Dual4(self.v * o, self.d0 * o, self.d1 * o, self.d2 * o, self.d3 * o)

    def __rmul__(self, o):
        return self.__mul__(o)

    def __truediv__(self, o):
        if isinstance(o, Dual4):
            if mp.mpf(o.v.a) <= 0 <= mp.mpf(o.v.b):
                inf_iv = iv.mpf([-mp.inf, mp.inf])
                return Dual4(inf_iv, inf_iv, inf_iv, inf_iv, inf_iv)
            inv = 1 / o.v
            q = self.v * inv
            return Dual4(q, (self.d0 - q * o.d0) * inv, (self.d1 - q * o.d1) * inv,
                         (self.d2 - q * o.d2) * inv, (self.d3 - q * o.d3) * inv)
        if mp.mpf(o.a) <= 0 <= mp.mpf(o.b):
            inf_iv = iv.mpf([-mp.inf, mp.inf])
            return Dual4(inf_iv, inf_iv, inf_iv, inf_iv, inf_iv)
        inv = 1 / o
        return Dual4(self.v * inv, self.d0 * inv, self.d1 * inv, self.d2 * inv, self.d3 * inv)

    def __rtruediv__(self, o):
        if mp.mpf(self.v.a) <= 0 <= mp.mpf(self.v.b):
            inf_iv = iv.mpf([-mp.inf, mp.inf])
            return Dual4(inf_iv, inf_iv, inf_iv, inf_iv, inf_iv)
        inv = 1 / self.v
        q = o * inv
        m = -q * inv
        return Dual4(q, m * self.d0, m * self.d1, m * self.d2, m * self.d3)

    def sqrt(self):
        assert mp.mpf(self.v.a) > 0
        r = iv.sqrt(self.v)
        inv = 1 / (2 * r)
        return Dual4(r, self.d0 * inv, self.d1 * inv, self.d2 * inv, self.d3 * inv)


def K0hat_ua_d(u, s):
    if isinstance(s, Dual4):
        uv, sv = u.v, s.v
        kv = K0hat_ua_exact(uv, sv)
        den = uv + sv + sv * sv; d2 = den * den
        du_k = (uv * (uv + 2 * (sv + sv * sv))) / d2
        ds_k = -(uv * uv * (1 + 2 * sv)) / d2
        return Dual4(kv, du_k * u.d0 + ds_k * s.d0, du_k * u.d1 + ds_k * s.d1,
                     du_k * u.d2 + ds_k * s.d2, du_k * u.d3 + ds_k * s.d3)
    return K0hat_ua_exact(u, s)


def K0hat_uv_d(u, v, s):
    if isinstance(s, Dual4):
        uv, vv, sv = u.v, v.v, s.v
        kv = K0hat_uv_iv(uv, vv, sv)
        xi = 1 - uv; ze = 1 - vv; s2 = sv * sv; s13 = (1 + sv) ** 3
        p = (sv + xi) * (sv + ze); Ds = s13 - p
        if mp.mpf(Ds.a) <= 0:
            inf_iv = iv.mpf([-mp.inf, mp.inf])
            return Dual4(kv, inf_iv, inf_iv, inf_iv, inf_iv)
        D2 = Ds * Ds
        du_k = ze - s2 * s13 * (sv + ze) / D2
        dv_k = xi - s2 * s13 * (sv + xi) / D2
        pp = 2 * sv + xi + ze
        ds_k = -1 + (sv * ((1 + sv) ** 2) * ((2 - sv) * p + sv * (1 + sv) * pp) - 2 * sv * (p ** 2)) / D2
        u0, u1 = mp.mpf(uv.a), mp.mpf(uv.b)
        v0, v1 = mp.mpf(vv.a), mp.mpf(vv.b)
        s0, s1 = mp.mpf(sv.a), mp.mpf(sv.b)
        um = (u0 + u1) / 2; vm = (v0 + v1) / 2; sm = (s0 + s1) / 2
        assert u0 <= um <= u1 and v0 <= vm <= v1 and s0 <= sm <= s1
        um_i, vm_i, sm_i = iv.mpf(um), iv.mpf(vm), iv.mpf(sm)
        kmvf = K0hat_uv_iv(um_i, vm_i, sm_i) + du_k * (uv - um_i) + dv_k * (vv - vm_i) + ds_k * (sv - sm_i)
        lo = max(mp.mpf(kv.a), mp.mpf(kmvf.a))
        hi = min(mp.mpf(kv.b), mp.mpf(kmvf.b))
        if lo <= hi:
            kv = iv.mpf([lo, hi])
        return Dual4(kv, du_k * u.d0 + dv_k * v.d0 + ds_k * s.d0,
                     du_k * u.d1 + dv_k * v.d1 + ds_k * s.d1,
                     du_k * u.d2 + dv_k * v.d2 + ds_k * s.d2,
                     du_k * u.d3 + dv_k * v.d3 + ds_k * s.d3)
    return K0hat_uv_iv(u, v, s)


def D_uv_d(u, v, s, eps):
    inv1s = 1 / (1 + s)
    al = u * inv1s; be = v * inv1s
    z = (1 - al) * (1 - be); w = 1 - z
    return (s * (z * z * z) * CGCE2) / ((1 + eps * z / w) * (s + w))


def baumann_center(lo, hi, g_iv):
    L, U = mp.mpf(g_iv.a), mp.mpf(g_iv.b)
    if not (mp.isfinite(L) and mp.isfinite(U)):
        return (lo + hi) / 2
    if L >= 0:
        return lo
    if U <= 0:
        return hi
    c = (U * lo - L * hi) / (U - L)
    if c < lo:
        c = lo
    if c > hi:
        c = hi
    return c


# ============================================================================
# MODULE 3: Large a >= 7.0 (s = 1/a in [0, ceil(1/7)], ALL delta in (0, d_ub(s)])
# ============================================================================
def _m3_check_chart2(tau_b, th_b, s_b, D_COEFF_IV):
    om_th = 1 - th_b
    th_om = iv.mpf("0.25") - (th_b - iv.mpf("0.5")) ** 2
    al = s_b * tau_b * th_b
    be = s_b * tau_b * om_th
    u = (1 + s_b) * al
    q = 1 - u * u
    w_t = 1 - s_b * tau_b * th_om
    den_w = 1 + tau_b * w_t
    den_a = 1 + tau_b * th_b
    den_b = 1 + tau_b * om_th
    Ys = (1 + s_b) * (om_th ** 2) / den_b
    poly_s = 1 - th_om * (s_b * s_b + (2 + s_b) * s_b * tau_b - (1 + s_b) * (s_b ** 2) * (tau_b ** 2) * th_om)
    Zs = (1 + s_b) * poly_s / den_w
    z = 1 - s_b * tau_b * w_t
    Dub = CGCE2 * (z ** 3) / den_w
    K1v_lo = 1 - s_b
    XsYs = ((1 + s_b) ** 2) * (th_om ** 2) / (den_a * den_b)
    AQ_s = q * (Zs ** 2) - q * Ys * Zs * (s_b * (tau_b ** 2) * Zs + (s_b ** 2) * D_COEFF_IV) / K1v_lo - (1 + Dub) * XsYs
    if mp.mpf(AQ_s.a) <= 0:
        return False
    BQ_num = (q * ((1 - be) * (w_t + om_th * den_w) - (s_b ** 2) * om_th * den_w * den_b)
              - ((1 + s_b) ** 2) * (s_b ** 2) * (tau_b ** 2) * th_om * om_th * den_w)
    BQ_s = (1 + s_b) * BQ_num / (den_w * den_b)
    if mp.mpf(BQ_s.a) <= 0:
        return False
    CQ2_s = (CGCE ** 2) * (1 + Dub) * ((1 + s_b) ** 3) * th_om * (om_th ** 3) / ((den_a ** 2) * (den_b ** 2))
    return mp.mpf((4 * AQ_s * BQ_s - CQ2_s).a) > 0


def _m3_check_chart1a(r_b, at_b, st_b, s_max, D_COEFF_IV):
    s_b = r_b * st_b
    if mp.mpf(s_b.a) > s_max:
        return True
    s_cl = iv.mpf([mp.mpf(s_b.a), min(mp.mpf(s_b.b), s_max)])
    al = r_b * at_b; be = r_b
    u = (1 + s_cl) * al; v = (1 + s_cl) * be
    if mp.mpf(v.a) > U35:
        return True
    q = 1 - u * u
    wt = at_b + 1 - r_b * at_b
    den_w = st_b + wt; den_b = st_b + 1
    sa_sum = st_b + at_b
    if mp.mpf(at_b.a) > 0:
        rho_a = iv_unit(1 / (1 + st_b / at_b))
    elif mp.mpf(sa_sum.a) > 0:
        rho_a = iv_unit(at_b / sa_sum)
    else:
        rho_a = iv.mpf([mp.mpf(0), mp.mpf(1)])
    prod_rs = iv.mpf("0.25") - (rho_a - iv.mpf("0.5")) ** 2
    Xs = (1 + s_cl) * at_b * rho_a
    Ys = (1 + s_cl) / den_b
    poly_s = (at_b + 1) ** 2 - at_b * (s_cl * s_cl + (2 + s_cl) * (al + be) - (1 + s_cl) * al * be)
    Zs = (1 + s_cl) * poly_s / den_w
    z = 1 - r_b * wt
    Dub = CGCE2 * st_b * (z ** 3) / den_w
    K1v_lo = 1 - s_cl
    AQ_s = q * (Zs ** 2) - q * Ys * Zs * (r_b * Zs + (s_cl ** 2) * D_COEFF_IV) / K1v_lo - (1 + Dub) * Xs * Ys
    if mp.mpf(AQ_s.a) <= 0:
        return False
    BQ_s = (1 + s_cl) * (q * ((1 - be) * (1 + st_b * wt / den_w) / den_b - s_cl * be) - ((1 + s_cl) ** 2) * al * be / den_b)
    if mp.mpf(BQ_s.a) <= 0:
        return False
    CQ2_s = (CGCE ** 2) * (1 + Dub) * (Ys ** 2) * (1 + s_cl) * prod_rs
    return mp.mpf((4 * AQ_s * BQ_s - CQ2_s).a) > 0


def _m3_check_chart1b(r_b, bt_b, st_b, s_max, D_COEFF_IV):
    s_b = r_b * st_b
    if mp.mpf(s_b.a) > s_max:
        return True
    s_cl = iv.mpf([mp.mpf(s_b.a), min(mp.mpf(s_b.b), s_max)])
    al = r_b; be = r_b * bt_b
    u = (1 + s_cl) * al; v = (1 + s_cl) * be
    if mp.mpf(u.a) > U70 or mp.mpf(v.a) > U35:
        return True
    if mp.mpf(u.a) > U35 and mp.mpf(v.a) > V20:
        return True
    q = 1 - u * u
    wt = 1 + bt_b - r_b * bt_b
    den_w = st_b + wt; den_a = st_b + 1
    sb_sum = st_b + bt_b
    if mp.mpf(bt_b.a) > 0:
        rho_b = iv_unit(1 / (1 + st_b / bt_b))
    elif mp.mpf(sb_sum.a) > 0:
        rho_b = iv_unit(bt_b / sb_sum)
    else:
        rho_b = iv.mpf([mp.mpf(0), mp.mpf(1)])
    Xs = (1 + s_cl) / den_a
    Ys = (1 + s_cl) * bt_b * rho_b
    poly_s = (1 + bt_b) ** 2 - bt_b * (s_cl * s_cl + (2 + s_cl) * (al + be) - (1 + s_cl) * al * be)
    Zs = (1 + s_cl) * poly_s / den_w
    z = 1 - r_b * wt
    Dub = CGCE2 * st_b * (z ** 3) / den_w
    K1v_lo = 1 - s_cl
    AQ_s = q * (Zs ** 2) - q * Ys * Zs * (r_b * Zs + (s_cl ** 2) * D_COEFF_IV) / K1v_lo - (1 + Dub) * Xs * Ys
    if mp.mpf(AQ_s.a) <= 0:
        return False
    BQ_s = (1 + s_cl) * (q * ((1 - be) * (wt + st_b * rho_b) / den_w - s_cl * be) - ((1 + s_cl) ** 2) * al * be * rho_b)
    if mp.mpf(BQ_s.a) <= 0:
        return False
    CQ2_s = (CGCE ** 2) * (1 + Dub) * (Ys ** 2) * Xs * (st_b / den_a)
    return mp.mpf((4 * AQ_s * BQ_s - CQ2_s).a) > 0


def _m3_check_direct_out_box(u_b, v_b, s_b, cap_v0=None):
    dub = d_ub_iv(s_b)
    phi0 = 1 / (1 + 3 * s_b + 2 * (s_b ** 2) + s_b ** 3)
    th0 = (s_b ** 3) * ((1 + s_b) ** 2) * phi0
    H0 = 1 - s_b + (s_b ** 4) * phi0
    k1v = (1 - s_b) + (s_b ** 3) * (1 + s_b - v_b) / (1 + 2 * s_b + 2 * (s_b ** 2) + s_b ** 3 + s_b * v_b)
    k0v = (cap_v0 ** 2) / (cap_v0 + s_b + s_b ** 2) if cap_v0 is not None else (v_b ** 2) / (v_b + s_b + s_b ** 2)
    xi_d = 1 - u_b; ze_d = 1 - v_b
    kuv = (1 - s_b - xi_d * ze_d) + (s_b ** 2) * (s_b + xi_d) * (s_b + ze_d) / (((1 + s_b) ** 3) - (s_b + xi_d) * (s_b + ze_d))
    ku0 = K0hat_u0_iv(u_b, s_b)
    duv = D_ub_uv_iv(u_b, v_b, s_b)
    du0 = D_ub_uv_iv(u_b, iv.mpf(0), s_b)
    q = 1 - u_b * u_b
    R = 1 / k0v - (1 - th0) / k1v
    pos_num = iv_pos(q * R) + (u_b ** 2) * th0 / k1v
    kt_u0_hi = ku0 + (s_b ** 2) * dub * (1 + du0)
    pos_scaled = (pos_num / kt_u0_hi + KAPPA0_M3 * (s_b ** 4) / k1v) * (k1v * H0 * (kuv ** 2))
    num0 = (1 - th0) * (kuv ** 2) - (1 + duv) * k1v * H0
    slope_d = (s_b ** 2) * dub * (1 + duv) * ((1 - th0) * kuv - k1v)
    min_d_term = iv.mpf(min(mp.mpf(0), mp.mpf(slope_d.a)))
    return mp.mpf((pos_scaled + num0 + min_d_term).a) > 0


def _m3_check_factored_box(xi_b, ze_b, s_b, cap_v0=None):
    u_b = 1 - xi_b; v_b = 1 - ze_b
    dub = d_ub_iv(s_b)
    db = iv.mpf([mp.mpf(0), mp.mpf(dub.b)])
    phi0 = 1 / (1 + 3 * s_b + 2 * (s_b ** 2) + s_b ** 3)
    th0_hat = ((1 + s_b) ** 2) * phi0
    th0 = (s_b ** 3) * th0_hat
    H0 = 1 - s_b + (s_b ** 4) * phi0
    s13 = (1 + s_b) ** 3
    s_den0 = s13 - s_b ** 2
    s_den1 = s13 - s_b * (s_b + ze_b)
    s_den2 = s13 - (s_b + xi_b) * (s_b + ze_b)
    Phi1 = s13 / (s_den2 * s_den0)
    Phi2 = s13 / (s_den2 * s_den1)
    D1_k = (s_b ** 3) * ze_b * s13 / (s_den1 * s_den0)
    K1v = H0 + D1_k
    Kuv = (1 - s_b - xi_b * ze_b) + (s_b ** 2) * (s_b + xi_b) * (s_b + ze_b) / s_den2
    Ku0 = K0hat_u0_iv(u_b, s_b)
    Du0 = D_ub_uv_iv(u_b, iv.mpf(0), s_b)
    Kt_u0_hi = Ku0 + (s_b ** 2) * dub * (1 + Du0)
    Duv_ub = D_ub_uv_iv(u_b, v_b, s_b)
    Kt_uv_lo = Kuv + (s_b ** 2) * db * (1 + Duv_ub)
    Den_star = (H0 + (s_b ** 2) * db) * Kuv * Kt_uv_lo

    al = u_b / (1 + s_b); be = v_b / (1 + s_b)
    w = al + be - al * be
    D_base = CGCE2 / (((1 + s_b) ** 6) * (s_b + w))
    Qx = 3 * (s_b ** 2) + 3 * s_b * xi_b + xi_b ** 2
    Qz = 3 * (s_b ** 2) + 3 * s_b * ze_b + ze_b ** 2

    if mp.mpf(xi_b.a) >= mp.mpf("0.80"):
        C_s4 = KAPPA0_M3 - (s_b ** 3) * D_base * K1v * H0 / Den_star
        C_s3x = -th0_hat / (xi_b * (H0 + (s_b ** 2) * db)) + (H0 / Den_star) * (Phi1 + Phi2 - s_b * D_base * Qx * K1v)
    else:
        C_s4 = (KAPPA0_M3
                + th0_hat * (-(s_b ** 2) * (1 - s_b * phi0 * (1 + s_b + s_b ** 2)) / H0
                             - s_b * (1 - xi_b + s_b + s_b ** 2) * dub * (1 + Du0) / Kt_u0_hi)
                - (s_b ** 3) * D_base * K1v * H0 / Den_star)
        C_s3x = -th0_hat + (H0 / Den_star) * (Phi1 + Phi2 - s_b * D_base * Qx * K1v)

    C_s3z = (H0 / Den_star) * (Phi1 - s_b * D_base * Qz * K1v)
    if mp.mpf(C_s3z.a) <= 0:
        return False
    both_pos = (mp.mpf(C_s4.a) > 0 and mp.mpf(C_s3x.a) > 0)
    comb_pos = (mp.mpf(xi_b.a) > 0 and mp.mpf((s_b * C_s4 + xi_b * C_s3x).a) > 0)
    if not (both_pos or comb_pos):
        return False

    Kt_u0_denom = Kt_u0_hi if mp.mpf(Kt_u0_hi.a) > 0 else iv.mpf(mp.mpf(Kt_u0_hi.b))
    if cap_v0 is not None:
        K0v_cap = (cap_v0 ** 2) / (cap_v0 + s_b + s_b ** 2)
        R_cap = 1 / K0v_cap - (1 - th0) / K1v
        F1 = (2 - xi_b) * K1v * R_cap / (ze_b * Kt_u0_denom)
    else:
        K0v = (v_b ** 2) / (v_b + s_b + s_b ** 2)
        P_R = ((s_b ** 3) * s13 / (s_den1 * s_den0)
               + (1 - th0) * (1 + 2 * s_b + 2 * (s_b ** 2) - ze_b * (1 + s_b + s_b ** 2))
               / ((1 + s_b + s_b ** 2) * (v_b + s_b + s_b ** 2)))
        F1 = (2 - xi_b) * P_R / (K0v * Kt_u0_denom)
    F2 = (2 * H0 + (s_b ** 2) * db * (1 + Duv_ub)) / Den_star
    C_xz = F1 - F2 + (s_b ** 2) * H0 * (Phi1 + Phi2) / Den_star - s_b * D_base * Qx * Qz * K1v * H0 / Den_star
    if mp.mpf(C_xz.a) >= 0:
        return True

    if both_pos and cap_v0 is None and mp.mpf(xi_b.b) <= mp.mpf("0.12") and mp.mpf(ze_b.b) <= mp.mpf("0.12"):
        Du0_0 = D_ub_uv_iv(iv.mpf(1), iv.mpf(0), s_b)
        D_F1 = 1 + (s_b ** 2) * dub * (1 + Du0_0) * (1 + s_b + s_b ** 2)
        diff_F1_s2 = 2 * (-1 - 2 * s_b + 2 * (s_b ** 2)
                          + (1 + 2 * s_b + 2 * (s_b ** 2)) * (s_b ** 2) * phi0 * (2 * (1 - s_b) + (s_b ** 4) * phi0)
                          - s_b * th0_hat * (1 + 2 * s_b + 2 * (s_b ** 2)) * (H0 ** 2)
                          + s_b * s13 * ((1 + s_b + s_b ** 2) ** 2) * (H0 ** 2) / (s_den0 ** 2)
                          - dub * (1 + Du0_0) * (1 + s_b + s_b ** 2)) / (D_F1 * (H0 ** 2))
        xi_m = iv.mpf([mp.mpf(0), mp.mpf(xi_b.b)])
        ze_m = iv.mpf([mp.mpf(0), mp.mpf(ze_b.b)])
        u_m = 1 - xi_m; v_m = 1 - ze_m
        s2_sum = s_b + s_b ** 2
        den_u_m = u_m + s2_sum
        Ku0_m = K0hat_u0_iv(u_m, s_b)
        Du0_m = D_ub_uv_iv(u_m, iv.mpf(0), s_b)
        Kt_u0_m = Ku0_m + (s_b ** 2) * dub * (1 + Du0_m)
        dKu0_dxi = -(u_m * (u_m + 2 * s2_sum)) / (den_u_m ** 2)
        dDu0_dxi = CGCE2 * s_b * ((s_b + xi_m) ** 2) * (3 * den_u_m + (s_b + xi_m)) / (((1 + s_b) ** 2) * (den_u_m ** 2))
        dKtu0_dxi = dKu0_dxi + (s_b ** 2) * dub * dDu0_dxi
        g_xi_m = (2 - xi_m) / Kt_u0_m
        dg_dxi_m = (-Kt_u0_m - (2 - xi_m) * dKtu0_dxi) / (Kt_u0_m ** 2)

        den_v_m = v_m + s2_sum
        K0v_m = (v_m ** 2) / den_v_m
        s_den1_m = s13 - s_b * (s_b + ze_m)
        P_R_m = ((s_b ** 3) * s13 / (s_den1_m * s_den0)
                 + (1 - th0) * (1 + 2 * s_b + 2 * (s_b ** 2) - ze_m * (1 + s_b + s_b ** 2))
                 / ((1 + s_b + s_b ** 2) * den_v_m))
        dK0v_dze = -(v_m * (v_m + 2 * s2_sum)) / (den_v_m ** 2)
        dPR_dze = ((s_b ** 4) * s13 / ((s_den1_m ** 2) * s_den0)
                   - (1 - th0) * (s_b ** 2) * ((1 + s_b) ** 2) / ((1 + s_b + s_b ** 2) * (den_v_m ** 2)))
        h_ze_m = P_R_m / K0v_m
        dh_dze_m = (dPR_dze * K0v_m - P_R_m * dK0v_dze) / (K0v_m ** 2)
        dF1_dxi = dg_dxi_m * h_ze_m
        dF1_dze = g_xi_m * dh_dze_m

        s_den2_m = s13 - (s_b + xi_m) * (s_b + ze_m)
        Kuv_m = (1 - s_b - xi_m * ze_m) + (s_b ** 2) * (s_b + xi_m) * (s_b + ze_m) / s_den2_m
        al_m = u_m / (1 + s_b); be_m = v_m / (1 + s_b)
        w_m = 1 - (1 - al_m) * (1 - be_m)
        Duv_ub_m = D_ub_uv_iv(u_m, v_m, s_b)
        Kt_uv_m = Kuv_m + (s_b ** 2) * db * (1 + Duv_ub_m)
        dKuv_dxi = -ze_m + (s_b ** 2) * s13 * (s_b + ze_m) / (s_den2_m ** 2)
        dKuv_dze = -xi_m + (s_b ** 2) * s13 * (s_b + xi_m) / (s_den2_m ** 2)
        den_w2_m = ((1 + s_b) ** 2) * (s_b + w_m)
        dDuv_dxi = CGCE2 * s_b * ((s_b + xi_m) ** 2) * ((s_b + ze_m) ** 3) * (3 * den_w2_m + (s_b + xi_m) * (s_b + ze_m)) / (((1 + s_b) ** 4) * (den_w2_m ** 2))
        dDuv_dze = CGCE2 * s_b * ((s_b + xi_m) ** 3) * ((s_b + ze_m) ** 2) * (3 * den_w2_m + (s_b + xi_m) * (s_b + ze_m)) / (((1 + s_b) ** 4) * (den_w2_m ** 2))
        N_F2_m = 2 * H0 + (s_b ** 2) * db * (1 + Duv_ub_m)
        Q_uv_m = Kuv_m * Kt_uv_m
        dNF2_dxi = (s_b ** 2) * db * dDuv_dxi
        dNF2_dze = (s_b ** 2) * db * dDuv_dze
        dQuv_dxi = (2 * Kuv_m + (s_b ** 2) * db * (1 + Duv_ub_m)) * dKuv_dxi + (s_b ** 2) * db * Kuv_m * dDuv_dxi
        dQuv_dze = (2 * Kuv_m + (s_b ** 2) * db * (1 + Duv_ub_m)) * dKuv_dze + (s_b ** 2) * db * Kuv_m * dDuv_dze
        dF2_dxi = (dNF2_dxi * Q_uv_m - N_F2_m * dQuv_dxi) / ((H0 + (s_b ** 2) * db) * (Q_uv_m ** 2))
        dF2_dze = (dNF2_dze * Q_uv_m - N_F2_m * dQuv_dze) / ((H0 + (s_b ** 2) * db) * (Q_uv_m ** 2))

        m_xi = dF1_dxi - dF2_dxi
        m_ze = dF1_dze - dF2_dze
        if mp.mpf(m_xi.a) <= 0 or mp.mpf(m_ze.a) <= 0:
            return False
        fac_D = D_base * K1v * H0 / Den_star
        m_xi_eff = m_xi - fac_D * (3 * (s_b ** 3) * (3 * s_b + xi_b) + s_b * (3 * s_b + xi_b) * (3 * s_b + ze_b) * ze_b)
        m_ze_eff = m_ze - fac_D * (3 * (s_b ** 3) * (3 * s_b + ze_b))
        if mp.mpf(m_xi_eff.a) <= 0 or mp.mpf(m_ze_eff.a) <= 0:
            return False
        rem_s2 = diff_F1_s2 + H0 * (Phi1 + Phi2) / Den_star - 9 * (s_b ** 3) * fac_D
        amgm_margin = (2 * iv.sqrt(iv.mpf(mp.mpf(C_s3x.a)) * iv.mpf(mp.mpf(m_ze_eff.a)))
                       + 2 * iv.sqrt(iv.mpf(mp.mpf(C_s3z.a)) * iv.mpf(mp.mpf(m_xi_eff.a)))
                       + iv.sqrt(s_b) * rem_s2)
        return mp.mpf(amgm_margin.a) > 0
    return False


def _m3_worker(task):
    kind = task[0]
    if kind == "C2":
        _, s_max, D_COEFF = task
        D_COEFF_IV = iv.mpf(D_COEFF)
        stack = [(mp.mpf(0), mp.mpf(1), mp.mpf(0), mp.mpf(1), mp.mpf(0), s_max, 0)]
        cnt = 0
        while stack:
            t0b, t1b, h0b, h1b, s0b, s1b, dep = stack.pop()
            if _m3_check_chart2(iv.mpf([t0b, t1b]), iv.mpf([h0b, h1b]), iv.mpf([s0b, s1b]), D_COEFF_IV):
                cnt += 1; continue
            assert dep < 18, f"Chart 2 failed at tau=[{t0b},{t1b}], th=[{h0b},{h1b}], s=[{s0b},{s1b}]"
            dim = max([(t1b - t0b, 0), (h1b - h0b, 1), ((s1b - s0b) / s_max, 2)])[1]
            if dim == 0:
                m = (t0b + t1b) / 2
                stack.append((m, t1b, h0b, h1b, s0b, s1b, dep + 1)); stack.append((t0b, m, h0b, h1b, s0b, s1b, dep + 1))
            elif dim == 1:
                m = (h0b + h1b) / 2
                stack.append((t0b, t1b, m, h1b, s0b, s1b, dep + 1)); stack.append((t0b, t1b, h0b, m, s0b, s1b, dep + 1))
            else:
                m = (s0b + s1b) / 2
                stack.append((t0b, t1b, h0b, h1b, m, s1b, dep + 1)); stack.append((t0b, t1b, h0b, h1b, s0b, m, dep + 1))
        return ("C2", cnt)
    if kind == "C1a":
        _, s_max, D_COEFF = task
        D_COEFF_IV = iv.mpf(D_COEFF)
        stack = [(mp.mpf(0), U35, mp.mpf(0), mp.mpf(1), mp.mpf(0), mp.mpf(2), 0)]
        cnt = 0
        while stack:
            r0b, r1b, a0b, a1b, s0b, s1b, dep = stack.pop()
            if _m3_check_chart1a(iv.mpf([r0b, r1b]), iv.mpf([a0b, a1b]), iv.mpf([s0b, s1b]), s_max, D_COEFF_IV):
                cnt += 1; continue
            assert dep < 24, f"Chart 1a failed at r=[{r0b},{r1b}], at=[{a0b},{a1b}], st=[{s0b},{s1b}]"
            dim = max([((r1b - r0b) / U35, 0), (a1b - a0b, 1), ((s1b - s0b) / 2, 2)])[1]
            if dim == 0:
                m = (r0b + r1b) / 2
                stack.append((m, r1b, a0b, a1b, s0b, s1b, dep + 1)); stack.append((r0b, m, a0b, a1b, s0b, s1b, dep + 1))
            elif dim == 1:
                m = (a0b + a1b) / 2
                stack.append((r0b, r1b, m, a1b, s0b, s1b, dep + 1)); stack.append((r0b, r1b, a0b, m, s0b, s1b, dep + 1))
            else:
                m = (s0b + s1b) / 2
                stack.append((r0b, r1b, a0b, a1b, m, s1b, dep + 1)); stack.append((r0b, r1b, a0b, a1b, s0b, m, dep + 1))
        return ("C1a", cnt)
    if kind == "C1b":
        _, s_max, D_COEFF = task
        D_COEFF_IV = iv.mpf(D_COEFF)
        stack = [(mp.mpf(0), U70, mp.mpf(0), mp.mpf(1), mp.mpf(0), mp.mpf(2), 0)]
        cnt = 0
        while stack:
            r0b, r1b, b0b, b1b, s0b, s1b, dep = stack.pop()
            if _m3_check_chart1b(iv.mpf([r0b, r1b]), iv.mpf([b0b, b1b]), iv.mpf([s0b, s1b]), s_max, D_COEFF_IV):
                cnt += 1; continue
            assert dep < 26, f"Chart 1b failed at r=[{r0b},{r1b}], bt=[{b0b},{b1b}], st=[{s0b},{s1b}]"
            dim = max([((r1b - r0b) / U70, 0), (b1b - b0b, 1), ((s1b - s0b) / 2, 2)])[1]
            if dim == 0:
                m = (r0b + r1b) / 2
                stack.append((m, r1b, b0b, b1b, s0b, s1b, dep + 1)); stack.append((r0b, m, b0b, b1b, s0b, s1b, dep + 1))
            elif dim == 1:
                m = (b0b + b1b) / 2
                stack.append((r0b, r1b, m, b1b, s0b, s1b, dep + 1)); stack.append((r0b, r1b, b0b, m, s0b, s1b, dep + 1))
            else:
                m = (s0b + s1b) / 2
                stack.append((r0b, r1b, b0b, b1b, m, s1b, dep + 1)); stack.append((r0b, r1b, b0b, b1b, s0b, m, dep + 1))
        return ("C1b", cnt)
    # Out rectangle (P2, P3, P4): strictly outward-rounded xi0, xi1, ze0, ze1 and ub = 1 - xib, vb = 1 - zeb!
    _, name, u0, u1, v0, v1, cap_v0_s, s_max = task
    cap_v0 = iv.mpf(cap_v0_s) if cap_v0_s is not None else None
    xi0 = mp.mpf((1 - iv.mpf(u1)).a); xi1 = mp.mpf((1 - iv.mpf(u0)).b)
    ze0 = mp.mpf((1 - iv.mpf(v1)).a); ze1 = mp.mpf((1 - iv.mpf(v0)).b)
    stack = [(xi0, xi1, ze0, ze1, mp.mpf(0), s_max, 0)]
    cnt = 0
    while stack:
        x0, x1, z0, z1, s0, s1, dep = stack.pop()
        xib = iv.mpf([x0, x1]); zeb = iv.mpf([z0, z1]); sb = iv.mpf([s0, s1])
        ub = 1 - xib; vb = 1 - zeb
        ok = False
        if s0 > 0 or (x0 > 0 and z0 > 0):
            ok = _m3_check_direct_out_box(ub, vb, sb, cap_v0=cap_v0)
        if not ok:
            ok = _m3_check_factored_box(xib, zeb, sb, cap_v0=cap_v0)
        if ok:
            cnt += 1; continue
        assert dep < 22, f"{name} failed at xi=[{x0},{x1}], ze=[{z0},{z1}], s=[{s0},{s1}]"
        dim = max([(x1 - x0, 0), (z1 - z0, 1), ((s1 - s0) / s_max, 2)])[1]
        if dim == 0:
            m = (x0 + x1) / 2
            stack.append((m, x1, z0, z1, s0, s1, dep + 1)); stack.append((x0, m, z0, z1, s0, s1, dep + 1))
        elif dim == 1:
            m = (z0 + z1) / 2
            stack.append((x0, x1, m, z1, s0, s1, dep + 1)); stack.append((x0, x1, z0, m, s0, s1, dep + 1))
        else:
            m = (s0 + s1) / 2
            stack.append((x0, x1, z0, z1, m, s1, dep + 1)); stack.append((x0, x1, z0, z1, s0, m, dep + 1))
    return (name, cnt)


def certify_module_3(pool):
    t0 = time.time()
    s_max = mp.mpf((iv.mpf(1) / iv.mpf(7)).b)
    assert s_max >= mp.mpf((iv.mpf(1) / iv.mpf("7.0")).b)

    # Step 3A: Target inequality M(T_0; s, delta) / s^4 > 0 & g_min > 0 on s in [0, ceil(1/7)]
    tA = time.time()
    N_s = 60
    s_grid = [mp.mpf(0)] + [mp.mpf((iv.mpf(s_max) * k / N_s).a) for k in range(1, N_s)] + [s_max]
    min_M_s4 = mp.mpf("1e30"); min_gmin = mp.mpf("1e30"); max_dub = mp.mpf(0)
    for k in range(N_s):
        sb = iv.mpf([s_grid[k], s_grid[k + 1]])
        lamb = (sb ** 2) / ((1 + sb) ** 3)
        d36 = 1 - iv.mpf("3.6") * lamb
        assert mp.mpf(d36.a) > 0
        y0 = lamb / d36
        assert mp.mpf((1 - sb * y0).a) > 0
        assert mp.mpf((1 - lamb * (1 + y0)).a) > 0
        assert mp.mpf((1 - lamb * ((1 + y0) ** 2)).a) > 0
        assert mp.mpf((1 - sb * (1 + y0) / ((1 + sb) ** 2)).a) > 0
        assert mp.mpf((1 - sb - sb * y0).a) > 0
        neg_lin = 1 / d36 - iv.mpf("1.6") - iv.mpf("1.6") * y0 - lamb * ((1 + y0) ** 2)
        assert mp.mpf(neg_lin.b) < 0

        dT_lo = ((1 + y0) ** 2) / (((1 + sb) ** 3) * (1 - lamb * ((1 + y0) ** 2))) - (sb ** 2) / (((1 + sb) ** 6) * (d36 ** 2))
        dT_hi = ((1 + y0) / (((1 + sb) ** 3) * (1 - lamb * (1 + y0)))
                 + (iv.mpf(4) / iv.mpf(27)) * ((1 + y0) ** 2)
                 / ((1 - sb - sb * y0) * ((1 + sb) ** 6) * ((1 - lamb * (1 + y0)) ** 2) * (1 - sb * (1 + y0) / ((1 + sb) ** 2))))
        assert mp.mpf(dT_lo.a) > 0 and mp.mpf(dT_lo.a) <= mp.mpf(dT_hi.b)
        dT_box = iv.mpf([mp.mpf(dT_lo.a), mp.mpf(dT_hi.b)])

        dub = d_ub_iv(sb)
        assert mp.mpf(dub.a) > 0
        if mp.mpf(dub.b) > max_dub:
            max_dub = mp.mpf(dub.b)
        db = iv.mpf([mp.mpf(0), mp.mpf(dub.b)])

        phi0 = 1 / (1 + 3 * sb + 2 * (sb ** 2) + sb ** 3)
        th0_hat = ((1 + sb) ** 2) * phi0
        th0 = (sb ** 3) * th0_hat
        H0 = 1 - sb + (sb ** 4) * phi0
        D1 = H0 + (sb ** 2) * db
        DT = D1 + (sb ** 4) * (dT_box - phi0)
        E = (1 - th0) / D1 + KAPPA0_M3 * (sb ** 4)
        gmin = 1 - (sb ** 2) * db * E
        assert mp.mpf(gmin.a) > 0
        if mp.mpf(gmin.a) < min_gmin:
            min_gmin = mp.mpf(gmin.a)

        B1 = 1 - sb + (sb ** 2) * db
        term1 = 2 * ((1 - th0) * phi0 / D1 - KAPPA0_M3 * B1)
        term4 = dT_box * (((1 - (sb ** 2) * db * E) ** 2) / (1 - sb) - 2 * E + (sb ** 2) * db * (E ** 2))
        term23 = db * (-sb * th0_hat * (2 - th0) / D1
                       + (sb ** 2) * ((dT_box - phi0) / (D1 * DT)
                                     + KAPPA0_M3 * (2 * (1 - th0) + KAPPA0_M3 * (sb ** 4) * D1)
                                     - phi0 * (E ** 2)))
        term5 = -(sb ** 2) * (th0_hat ** 2)
        M_s4 = term1 + term4 + term23 + term5
        assert mp.mpf(M_s4.a) > 0
        if mp.mpf(M_s4.a) < min_M_s4:
            min_M_s4 = mp.mpf(M_s4.a)
    print(f"  [Module 3 / Step 3A PASS] M(T_0; s, delta)/s^4 >= +{float(min_M_s4):.5f} > 0, "
          f"g_min >= {float(min_gmin):.6f} on s in [0, 1/7] ({time.time()-tA:.2f}s)", flush=True)

    # Step 3B: Run all 3 projective charts + 3 complement rectangles in parallel!
    tB = time.time()
    dub_max_iv = iv.mpf(max_dub)
    D_COEFF = mp.mpf((dub_max_iv * (1 + CGCE2)).b)
    assert mp.mpf(dub_max_iv.b) < mp.mpf("0.42")
    m3_tasks = [
        ("C2", s_max, D_COEFF),
        ("C1a", s_max, D_COEFF),
        ("C1b", s_max, D_COEFF),
        ("OUT", "P2", U70, mp.mpf(1), mp.mpf(0), V20, "0.20", s_max),
        ("OUT", "P3", mp.mpf(0), U35, U35, mp.mpf(1), None, s_max),
        ("OUT", "P4", U35, mp.mpf(1), V20, mp.mpf(1), None, s_max),
    ]
    res_map = dict(pool.map(_m3_worker, m3_tasks))
    p1_tot = res_map["C2"] + res_map["C1a"] + res_map["C1b"]
    out_tot = res_map["P2"] + res_map["P3"] + res_map["P4"]
    print(f"  [Module 3 / Step 3B PASS] P1={res_map['C2']}+{res_map['C1a']}+{res_map['C1b']}={p1_tot}, "
          f"OUT={res_map['P2']}+{res_map['P3']}+{res_map['P4']}={out_tot} iv boxes ({time.time()-tB:.2f}s)", flush=True)
    print(f"[MODULE 3 PASS] ALL a >= 7.0 (s in [0, ceil(1/7)]), ALL delta in (0, d_ub(s)] CERTIFIED in {time.time()-t0:.2f}s!", flush=True)
    return s_max


# ============================================================================
# MODULE 4 / STEP 4A: Corner [0, 0.04] x (0, 0.04] for ALL a in [floor(1.1407), 7.0]
# ============================================================================
def _s4a_check_inner_r_slice(a_b, tau_b, th_b, r_cl, dub_b, A_b):
    d_s = 1 / (C_E ** 2)
    om_th = 1 - th_b
    th_om = iv.mpf("0.25") - (th_b - iv.mpf("0.5")) ** 2
    al = r_cl * th_b; be = r_cl * om_th
    w = r_cl * (1 - r_cl * th_om)
    z = 1 - w; za = 1 - al
    wt = tau_b * (1 - r_cl * th_om)
    den_w = 1 + a_b * w; den_a = 1 + a_b * al; den_b = 1 + a_b * be
    Yt = (om_th ** 2) / den_b
    XtYt = (th_om ** 2) / (den_a * den_b)
    poly_t = 1 - th_om * (1 / (a_b ** 2) + (2 + 1 / a_b) * r_cl - (1 + 1 / a_b) * (r_cl ** 2) * th_om)
    Zt = poly_t / den_w
    D_xy = CGCE2 * (z ** 3) / ((1 + z / wt) * den_w) if mp.mpf(wt.a) > 0 else CGCE2 * (z ** 3) * wt / ((wt + z) * den_w)
    D_xa_over_tth = CGCE2 * (za ** 3) / ((tau_b * th_b + za) * den_a)
    D_s = d_s * (1 + D_xy)
    v_sv = (a_b + 1) * be / a_b
    xs_sv = XF_STAR * a_b
    Lam_b = ((1 + a_b) ** 3) / a_b
    p_sv_a = (1 + xs_sv) * (1 + a_b)
    p_sv_y = (1 + xs_sv) * (1 + a_b * (1 - v_sv))
    Ksv = K0_ua_iv(U_STAR, a_b) + a_b * v_sv * (xs_sv - Lam_b * (1 + xs_sv) / ((Lam_b - p_sv_a) * (Lam_b - p_sv_y)))
    if mp.mpf(Ksv.a) <= 0:
        return False
    c_b = c_of_a_step4a_iv(a_b)
    if mp.mpf(tau_b.a) > 0:
        eps_sl = r_cl / tau_b
        d_hi = min(mp.mpf(dub_b.b), mp.mpf((A_b * (eps_sl ** 2) * d_s).b))
    else:
        d_hi = mp.mpf(dub_b.b)
    delta_cap_iv = iv.mpf([mp.mpf(0), d_hi])
    Z_full = A_b * (r_cl ** 2) * Zt
    D_full = delta_cap_iv * (1 + D_xy)
    w_unit = 1 - r_cl * th_om
    ZY_hat = (1 - be) * (w_unit + om_th * den_w) / (den_w * den_b) - om_th / (a_b ** 2)
    B1 = (Zt ** 2) - (1 - c_b) * Yt * Zt * (Z_full + D_full) / Ksv - (1 + D_xy) * XtYt
    B2 = D_s * (ZY_hat - Yt * tau_b * D_xa_over_tth)
    if mp.mpf(tau_b.a) == 0:
        return mp.mpf(B1.a) > 0 and mp.mpf(B2.a) > 0
    return mp.mpf(((tau_b ** 2) * B1 + th_b * B2).a) > 0


def _s4a_check_inner_box(a_b, tau_b, th_b):
    dub_b = d_ub_from_a_iv(a_b)
    if mp.mpf(dub_b.a) <= 0:
        return False
    A_b = (a_b ** 2) * (a_b + 1)
    eps_ub_b = C_E * iv.sqrt(iv_pos(dub_b / A_b))
    r_max_b = a_b * iv.mpf(U_CUT + V_CUT) / (a_b + 1)
    r_hi = min(mp.mpf((eps_ub_b * tau_b).b), mp.mpf(r_max_b.b))
    if _s4a_check_inner_r_slice(a_b, tau_b, th_b, iv.mpf([mp.mpf(0), r_hi]), dub_b, A_b):
        return True
    if mp.mpf((a_b * iv.mpf(r_hi)).b) <= mp.mpf("0.04"):
        return False
    r_st = [(mp.mpf(0), r_hi, 0)]
    while r_st:
        r0, r1, rd = r_st.pop()
        if _s4a_check_inner_r_slice(a_b, tau_b, th_b, iv.mpf([r0, r1]), dub_b, A_b):
            continue
        if rd >= 4:
            return False
        rm = (r0 + r1) / 2
        r_st.append((rm, r1, rd + 1)); r_st.append((r0, rm, rd + 1))
    return True


def _s4a_check_outer_box(a_b, r_b, th_b):
    om_th = 1 - th_b
    th_om = iv.mpf("0.25") - (th_b - iv.mpf("0.5")) ** 2
    al = r_b * th_b; be = r_b * om_th
    w = r_b * (1 - r_b * th_om); z = 1 - w
    den_w = 1 + a_b * w; den_a = 1 + a_b * al; den_b = 1 + a_b * be
    XtYt = (th_om ** 2) / (den_a * den_b)
    Yt = (om_th ** 2) / den_b
    poly_t = 1 - th_om * (1 / (a_b ** 2) + (2 + 1 / a_b) * r_b - (1 + 1 / a_b) * (r_b ** 2) * th_om)
    Zt = poly_t / den_w
    Dub = CGCE2 * (z ** 3) / den_w
    v_sv = (a_b + 1) * be / a_b
    xs_sv = XF_STAR * a_b
    Lam_b = ((1 + a_b) ** 3) / a_b
    p_sv_a = (1 + xs_sv) * (1 + a_b)
    p_sv_y = (1 + xs_sv) * (1 + a_b * (1 - v_sv))
    Ksv = K0_ua_iv(U_STAR, a_b) + a_b * v_sv * (xs_sv - Lam_b * (1 + xs_sv) / ((Lam_b - p_sv_a) * (Lam_b - p_sv_y)))
    c_b = c_of_a_step4a_iv(a_b)
    A_b = (a_b ** 2) * (a_b + 1)
    d_over_Ar2 = 1 / ((M_CUT ** 2) * (C_E ** 2))
    Z_full = A_b * (r_b ** 2) * Zt
    D_full_ub = A_b * (r_b ** 2) * d_over_Ar2 * (1 + Dub)
    val = (Zt ** 2) - (1 - c_b) * Yt * Zt * (Z_full + D_full_ub) / Ksv - (1 + Dub) * XtYt - (1 + Dub) * Yt * d_over_Ar2 * CGCE2
    return mp.mpf(val.a) > 0


def _s4a_worker(task):
    kind = task[0]
    if kind == "IN":
        _, tau_lo, tau_hi, a_init_4a = task
        stack = [(a_init_4a[i], a_init_4a[i + 1], tau_lo, tau_hi, mp.mpf(0), mp.mpf(1), 0)
                 for i in range(len(a_init_4a) - 1)]
        cnt = 0
        while stack:
            a0, a1, t0b, t1b, h0, h1, dep = stack.pop()
            if _s4a_check_inner_box(iv.mpf([a0, a1]), iv.mpf([t0b, t1b]), iv.mpf([h0, h1])):
                cnt += 1; continue
            assert dep < 18, f"Step 4A Inner failed at a=[{a0},{a1}], tau=[{t0b},{t1b}], th=[{h0},{h1}]"
            dim = max([((a1 - a0) / a0, 0), ((t1b - t0b) / (tau_hi - tau_lo), 1), (h1 - h0, 2)])[1]
            if dim == 0:
                m = (a0 + a1) / 2
                stack.append((m, a1, t0b, t1b, h0, h1, dep + 1)); stack.append((a0, m, t0b, t1b, h0, h1, dep + 1))
            elif dim == 1:
                m = (t0b + t1b) / 2
                stack.append((a0, a1, m, t1b, h0, h1, dep + 1)); stack.append((a0, a1, t0b, m, h0, h1, dep + 1))
            else:
                m = (h0 + h1) / 2
                stack.append((a0, a1, t0b, t1b, m, h1, dep + 1)); stack.append((a0, a1, t0b, t1b, h0, m, dep + 1))
        return ("IN", cnt)
    _, a_init_4a = task
    a_min, a_max = a_init_4a[0], a_init_4a[-1]
    stack = [(a_init_4a[i], a_init_4a[i + 1], mp.mpf(0), mp.mpf("0.08"), mp.mpf(0), mp.mpf(1), 0)
             for i in range(len(a_init_4a) - 1)]
    cnt = 0
    while stack:
        a0, a1, r0, r1, h0, h1, dep = stack.pop()
        if _s4a_check_outer_box(iv.mpf([a0, a1]), iv.mpf([r0, r1]), iv.mpf([h0, h1])):
            cnt += 1; continue
        assert dep < 18, f"Step 4A Outer failed at a=[{a0},{a1}], r=[{r0},{r1}], th=[{h0},{h1}]"
        dim = max([((a1 - a0) / (a_max - a_min), 0), ((r1 - r0) / mp.mpf("0.08"), 1), (h1 - h0, 2)])[1]
        if dim == 0:
            m = (a0 + a1) / 2
            stack.append((m, a1, r0, r1, h0, h1, dep + 1)); stack.append((a0, m, r0, r1, h0, h1, dep + 1))
        elif dim == 1:
            m = (r0 + r1) / 2
            stack.append((a0, a1, m, r1, h0, h1, dep + 1)); stack.append((a0, a1, r0, m, h0, h1, dep + 1))
        else:
            m = (h0 + h1) / 2
            stack.append((a0, a1, r0, r1, m, h1, dep + 1)); stack.append((a0, a1, r0, r1, h0, m, dep + 1))
    return ("OUT", cnt)


def certify_step_4a(pool):
    tC = time.time()
    a_min = mp.mpf(iv.mpf("1.1407").a)
    a_init_4a = [a_min] + [mp.mpf(s) for s in ["1.18", "1.24", "1.32", "1.42", "1.55", "1.75",
                                              "2.0", "2.35", "2.8", "3.4", "4.2", "5.3", "7.0"]]
    assert a_init_4a[0] <= mp.mpf(iv.mpf("1.1407").a) and a_init_4a[-1] == mp.mpf("7.0")
    tau_grid = [mp.mpf(s) for s in ["0", "0.02", "0.06", "0.15", "0.35", "0.8", "1.8", "4.0", "9.0", "20.0"]]
    tasks = [("IN", tau_grid[ti], tau_grid[ti + 1], a_init_4a) for ti in range(len(tau_grid) - 1)]
    tasks.append(("OUT", a_init_4a))
    n_inner = 0; n_outer = 0
    for kind, cnt in pool.map(_s4a_worker, tasks):
        if kind == "IN":
            n_inner += cnt
        else:
            n_outer += cnt
    print(f"  [Module 4 / Step 4A PASS] Corner [0, 0.04]x(0, 0.04] certified for ALL a in [floor(1.1407), 7.0]: "
          f"Inner={n_inner}, Outer={n_outer} iv boxes ({time.time()-tC:.2f}s)", flush=True)


# ============================================================================
# MODULE 4 / BAND B: a in [3.5, 7.0] (s in [floor(1/7), ceil(1/3.5)]), 100% CLOSED-FORM
# ============================================================================
def _bandB_check_zone1_box(u0, u1, v0, v1, s0, s1, us_iv, allow_d_split):
    sb = iv.mpf([s0, s1]); ub = iv.mpf([u0, u1]); vb = iv.mpf([v0, v1])
    dub = d_ub_iv(sb); d_hi = mp.mpf(dub.b)
    db = iv.mpf([mp.mpf(0), d_hi])
    s2 = sb * sb; s2d = s2 * db
    phi0 = 1 / (1 + 3 * sb + 2 * s2 + sb ** 3)
    th0 = (sb ** 3) * ((1 + sb) ** 2) * phi0
    H0 = 1 - sb + (sb ** 4) * phi0
    E = (1 - th0) / (H0 + s2d) + KAPPA0_B * (sb ** 4)
    Kuv = K0hat_uv_iv(ub, vb, sb); Ksv = K0hat_uv_iv(us_iv, vb, sb)
    Ku0 = K0hat_ua_exact(ub, sb)
    Duv_ub = D_ub_uv_iv(ub, vb, sb)
    s2dDuv = dD_mono_s_iv(ub, vb, sb, mp.mpf(0), d_hi)
    s2dDu0 = dD_mono_s_iv(ub, iv.mpf(0), sb, mp.mpf(0), d_hi)
    Kt_uv = Kuv + s2d + s2dDuv; Kt_u0 = Ku0 + s2d + s2dDu0
    if v0 == 0:
        K0v_ub = K0hat_ua_exact(iv.mpf(v1), sb)
        val = 1 / K0v_ub - (1 - th0) / Ksv + Kt_u0 * (E / Ksv - (1 + Duv_ub) / (Kuv * Kt_uv))
        return mp.mpf(val.a) > 0
    K0v = K0hat_ua_exact(vb, sb)
    diff_inv = None
    if v0 >= mp.mpf("0.50"):
        xi = 1 - ub; xis = 1 - us_iv; ze = 1 - vb
        s13 = (1 + sb) ** 3; s_den0 = s13 - s2
        s_den_s1 = s13 - sb * (sb + xis); s_den_01 = s13 - sb * (sb + 1)
        s_den_sv = s13 - (sb + xis) * (sb + ze); s_den_0v = s13 - (sb + 1) * (sb + ze)
        s_den_uv = s13 - (sb + xi) * (sb + ze)
        f0 = (sb ** 3) * xis * s13 / (s_den_s1 * s_den0)
        br = ((us_iv - th0) + s2 * s13 * (sb + xis) / (s_den_sv * s_den_s1)
              - (1 - th0) * s2 * s13 * (sb + 1) / (s_den_0v * s_den_01))
        diff_inv = (f0 + ze * br) / (K0v * Ksv)
        Ruv = s2 * s13 * (sb * (xi + ze) + xi * ze) / (s_den_uv * s_den0)
        Rsv = s2 * s13 * (sb * (xis + ze) + xis * ze) / (s_den_sv * s_den0)
        Del_uv = -xi * ze + Ruv
        D_hi_u = iv.mpf(mp.mpf(Duv_ub.b)); s2d_hi_u = s2d * (1 + D_hi_u); Ktv_hi_u = Kuv + s2d_hi_u
        denA = (H0 + s2d) * Ksv * Kuv * Ktv_hi_u
        ze_coef_u = br / (K0v * Ksv) + Kt_u0 * (H0 * (xis - 2 * xi) + s2d_hi_u * (xis - xi)) / denA
        rem_u = (H0 * (2 * Ruv - Rsv) + (Del_uv ** 2) - th0 * (Kuv ** 2) - D_hi_u * Ksv * H0
                 + s2d_hi_u * ((Ruv - Rsv) - th0 * Kuv))
        valA = f0 / (K0v * Ksv) + ze * ze_coef_u + Kt_u0 * (KAPPA0_B * (sb ** 4) / Ksv + rem_u / denA)
        if mp.mpf(valA.a) > 0:
            return True
    val1 = 1 / K0v - (1 - th0) / Ksv + Kt_u0 * (E / Ksv - (1 + Duv_ub) / (Kuv * Kt_uv))
    if mp.mpf(val1.a) > 0:
        return True
    al_s = ub / (1 + sb); be_s = vb / (1 + sb); w_s = 1 - (1 - al_s) * (1 - be_s)
    Kuv_m_K0v = ub * ((1 - be_s) * (sb * (w_s + be_s) + w_s * be_s) / ((sb + w_s) * (sb + be_s)) - sb * be_s)
    valC = (Kuv_m_K0v / (K0v * Kuv) + (1 - (Ku0 + s2dDu0) * (1 + Duv_ub) / Kuv) / Kt_uv
            - (1 - th0) / Ksv + Kt_u0 * E / Ksv)
    if mp.mpf(valC.a) > 0:
        return True
    if not allow_d_split:
        return False
    d_fracs = ([mp.mpf(0), mp.mpf("0.015"), mp.mpf("0.12"), mp.mpf("0.45"), mp.mpf("1.0")]
               if allow_d_split == 1 else
               [mp.mpf(0), mp.mpf("0.002"), mp.mpf("0.015"), mp.mpf("0.06"), mp.mpf("0.20"), mp.mpf("0.50"), mp.mpf("1.0")])
    for di in range(len(d_fracs) - 1):
        dd0 = d_hi * d_fracs[di]; dd1 = d_hi * d_fracs[di + 1]
        ddb = iv.mpf([dd0, dd1]); ss2d = s2 * ddb
        eps_b = C_E * iv.sqrt(ddb * (sb ** 3) / (1 + sb))
        Duv_d = D_uv_s_iv(ub, vb, sb, eps_b)
        sd_uv = dD_mono_s_iv(ub, vb, sb, dd0, dd1)
        sd_u0 = dD_mono_s_iv(ub, iv.mpf(0), sb, dd0, dd1)
        Ktu_d = Ku0 + ss2d + sd_u0; Ktv_d = Kuv + ss2d + sd_uv
        E_d = (1 - th0) / (H0 + ss2d) + KAPPA0_B * (sb ** 4)
        if diff_inv is not None:
            D_hi_d = iv.mpf(mp.mpf(Duv_d.b)); s2d_hi_d = ss2d * (1 + D_hi_d); Ktv_hi_d = Kuv + s2d_hi_d
            denA_d = (H0 + ss2d) * Ksv * Kuv * Ktv_hi_d
            ze_coef_d = br / (K0v * Ksv) + Ktu_d * (H0 * (xis - 2 * xi) + s2d_hi_d * (xis - xi)) / denA_d
            rem_d = (H0 * (2 * Ruv - Rsv) + (Del_uv ** 2) - th0 * (Kuv ** 2) - D_hi_d * Ksv * H0
                     + s2d_hi_d * ((Ruv - Rsv) - th0 * Kuv))
            vA_d = f0 / (K0v * Ksv) + ze * ze_coef_d + Ktu_d * (KAPPA0_B * (sb ** 4) / Ksv + rem_d / denA_d)
            if mp.mpf(vA_d.a) > 0:
                continue
        v1_d = (diff_inv if diff_inv is not None else (1 / K0v - (1 - th0) / Ksv)) + Ktu_d * (E_d / Ksv - (1 + Duv_d) / (Kuv * Ktv_d))
        if mp.mpf(v1_d.a) > 0:
            continue
        vC_d = (Kuv_m_K0v / (K0v * Kuv) + (1 - (Ku0 + sd_u0) * (1 + Duv_d) / Kuv) / Ktv_d
                - (1 - th0) / Ksv + Ktu_d * E_d / Ksv)
        if mp.mpf(vC_d.a) <= 0:
            return False
    return True


def _bandB_check_zone2_direct(u0, u1, v0, v1, s0, s1):
    ub = iv.mpf([u0, u1]); vb = iv.mpf([v0, v1]); sb = iv.mpf([s0, s1])
    dub = d_ub_iv(sb)
    phi0 = 1 / (1 + 3 * sb + 2 * (sb ** 2) + sb ** 3)
    th0 = (sb ** 3) * ((1 + sb) ** 2) * phi0
    H0 = 1 - sb + (sb ** 4) * phi0
    k1v = (1 - sb) + (sb ** 3) * (1 + sb - vb) / (1 + 2 * sb + 2 * (sb ** 2) + sb ** 3 + sb * vb)
    k0v = K0hat_ua_exact(iv.mpf(v1), sb) if v0 == 0 else K0hat_ua_exact(vb, sb)
    kuv = K0hat_uv_iv(ub, vb, sb); ku0 = K0hat_ua_exact(ub, sb)
    duv = D_ub_uv_iv(ub, vb, sb); du0 = D_ub_uv_iv(ub, iv.mpf(0), sb)
    q = 1 - OM_EA_B * (ub * ub); om_q = OM_EA_B * (ub * ub)
    R = 1 / k0v - (1 - th0) / k1v
    pos_num = iv_pos(q * R) + om_q * th0 / k1v
    kt_u0_hi = ku0 + (sb ** 2) * dub * (1 + du0)
    pos_scaled = (pos_num / kt_u0_hi + KAPPA0_B * (sb ** 4) / k1v) * (k1v * H0 * (kuv ** 2))
    num0 = (1 - th0) * (kuv ** 2) - (1 + duv) * k1v * H0
    slope_d = (sb ** 2) * dub * (1 + duv) * ((1 - th0) * kuv - k1v)
    min_d_term = iv.mpf(min(mp.mpf(0), mp.mpf(slope_d.a)))
    return mp.mpf((pos_scaled + num0 + min_d_term).a) > 0


def _bandB_check_zone2_near11(u0, u1, v0, v1, s0, s1):
    ub = iv.mpf([u0, u1]); vb = iv.mpf([v0, v1]); sb = iv.mpf([s0, s1])
    xi = 1 - ub; ze = 1 - vb
    s2 = sb * sb; s13 = (1 + sb) ** 3; s_den0 = s13 - s2
    phi0 = 1 / (1 + 3 * sb + 2 * s2 + sb ** 3)
    th0 = (sb ** 3) * ((1 + sb) ** 2) * phi0
    H0 = 1 - sb + (sb ** 4) * phi0
    dub = d_ub_iv(sb); d_hi = mp.mpf(dub.b)
    Kuv = K0hat_uv_iv(ub, vb, sb); Ku0 = K0hat_ua_exact(ub, sb)
    s_den1 = s13 - sb * (sb + ze); s_den2 = s13 - (sb + xi) * (sb + ze)
    D1_k = (sb ** 3) * ze * s13 / (s_den1 * s_den0)
    Ruv_ze = (sb ** 3) * ze * s13 / (s_den2 * s_den0)
    Ruv_xi = s2 * s13 * (sb + ze) / (s_den2 * s_den0)
    Ruv = Ruv_ze + xi * Ruv_xi
    twoR_m_D1_over_ze = (sb ** 3) * s13 * (s_den1 + xi * (sb + ze)) / (s_den0 * s_den1 * s_den2)
    R_m_D1_over_xize = (sb ** 3) * s13 * (sb + ze) / (s_den0 * s_den1 * s_den2)
    K1v = H0 + D1_k
    Del_uv = -xi * ze + Ruv
    if v0 == 0:
        K0v_cap = K0hat_ua_exact(iv.mpf(v1), sb)
        R_term_over_ze = (1 / K0v_cap - (1 - th0) / K1v) / ze
    else:
        K0v = K0hat_ua_exact(vb, sb)
        P_R = ((sb ** 3) * s13 / (s_den1 * s_den0)
               + (1 - th0) * (1 + 2 * sb + 2 * s2 - ze * (1 + sb + s2)) / ((1 + sb + s2) * (vb + sb + s2)))
        R_term_over_ze = P_R / (K0v * K1v)
    om_q = OM_EA_B * (ub * ub)
    s_den_u0 = s13 - (sb + xi) * (sb + 1)
    Ru0_0 = (sb ** 3) * s13 / (s_den_u0 * s_den0)
    Ru0_xi = s2 * s13 * (sb + 1) / (s_den_u0 * s_den0)
    d_fracs = [mp.mpf(0), mp.mpf("0.05"), mp.mpf("0.15"), mp.mpf("0.30"),
               mp.mpf("0.48"), mp.mpf("0.66"), mp.mpf("0.83"), mp.mpf("1.0")]
    for di in range(len(d_fracs) - 1):
        dd0 = d_hi * d_fracs[di]; dd1 = d_hi * d_fracs[di + 1]
        ddb = iv.mpf([dd0, dd1]); s2d = s2 * ddb
        eps_b = C_E * iv.sqrt(ddb * (sb ** 3) / (1 + sb))
        Duv_iv = D_uv_s_iv(ub, vb, sb, eps_b)
        D_hi_sc = iv.mpf(mp.mpf(Duv_iv.b))
        s2d_hi = s2d * (1 + D_hi_sc)
        s2dDu0 = dD_mono_s_iv(ub, iv.mpf(0), sb, dd0, dd1)
        D1_d = H0 + s2d; Kt_uv_hi = Kuv + s2d_hi; Kt_u0 = Ku0 + s2d + s2dDu0
        Den = D1_d * K1v * Kuv * Kt_uv_hi
        th_base = th0 * ((H0 * s2d_hi + s2d * s2d_hi - Kuv * (Ru0_0 + s2dDu0)) / (Kt_u0 * D1_d * Kt_uv_hi) - EA_B / Kt_u0) / K1v
        rem_base = ((Del_uv ** 2) - H0 * K1v * D_hi_sc - s2d_hi * th0 * Kuv) / Den
        xi_coef = (th0 * (Kuv * (1 - Ru0_xi) / (Kt_u0 * D1_d * Kt_uv_hi) - OM_EA_B * (2 - xi) / Kt_u0) / K1v
                   + (2 * H0 + s2d_hi) * Ruv_xi / Den)
        ze_coef = (EA_B * R_term_over_ze / Kt_u0 + H0 * twoR_m_D1_over_ze / Den
                   + xi * (OM_EA_B * (2 - xi) * R_term_over_ze / Kt_u0 - (2 * H0 + s2d_hi) / Den + s2d_hi * R_m_D1_over_xize / Den))
        if mp.mpf((KAPPA0_B * (sb ** 4) / K1v + th_base + rem_base + xi * xi_coef + ze * ze_coef).a) > 0:
            continue
        ze_part = ze * (EA_B * R_term_over_ze / Kt_u0
                        + xi * (OM_EA_B * (2 - xi) * R_term_over_ze / Kt_u0 - (2 * H0 + s2d_hi) / Den))
        rem_B = (H0 * (2 * Ruv - D1_k) + (Del_uv ** 2) - th0 * (Kuv ** 2) - H0 * K1v * D_hi_sc
                 + s2d_hi * (Ruv - D1_k - th0 * Kuv))
        if mp.mpf((KAPPA0_B * (sb ** 4) / K1v + th0 * om_q / (Kt_u0 * K1v) + ze_part + rem_B / Den).a) <= 0:
            return False
    return True


def _bandB_worker(task):
    kind = task[0]
    if kind in ("Z1a", "Z1b"):
        _, u_lo, u_hi, v_lo, v_hi, s_a, s_b, s_span, us_s = task
        us_iv = iv.mpf(us_s)
        if v_lo > 0:
            v_grid = [v_lo, mp.mpf("0.07"), mp.mpf("0.13"), mp.mpf("0.25"), mp.mpf("0.50"), mp.mpf("0.80"), v_hi]
        else:
            v_grid = [mp.mpf(0), mp.mpf("0.02"), mp.mpf("0.06"), mp.mpf("0.15"), mp.mpf("0.35"), mp.mpf("0.65"), v_hi]
        stack = [(u_lo, u_hi, v_grid[j], v_grid[j + 1], s_a, s_b, 0) for j in range(len(v_grid) - 1)]
        cnt = 0
        while stack:
            u0, u1, v0, v1, s0, s1, dep = stack.pop()
            if _bandB_check_zone1_box(u0, u1, v0, v1, s0, s1, us_iv, allow_d_split=(2 if dep >= 5 else (1 if dep >= 1 else 0))):
                cnt += 1; continue
            assert dep < 18, f"Band B {kind} failed at u=[{u0},{u1}], v=[{v0},{v1}], s=[{s0},{s1}]"
            dim = max([((u1 - u0) / max(u0, mp.mpf("0.01")), 0), ((v1 - v0) / max(v0, mp.mpf("0.02")), 1), ((s1 - s0) / s_span, 2)])[1]
            if dim == 0:
                m = (u0 + u1) / 2
                stack.append((m, u1, v0, v1, s0, s1, dep + 1)); stack.append((u0, m, v0, v1, s0, s1, dep + 1))
            elif dim == 1:
                m = (v0 + v1) / 2
                stack.append((u0, u1, m, v1, s0, s1, dep + 1)); stack.append((u0, u1, v0, m, s0, s1, dep + 1))
            else:
                m = (s0 + s1) / 2
                stack.append((u0, u1, v0, v1, m, s1, dep + 1)); stack.append((u0, u1, v0, v1, s0, m, dep + 1))
        return (kind, cnt, 0)
    _, s_a, s_b, s_span = task
    stack = [(U_SPLIT_B, mp.mpf(1), mp.mpf(0), mp.mpf(1), s_a, s_b, 0)]
    n_dir = 0; n_n11 = 0
    while stack:
        u0, u1, v0, v1, s0, s1, dep = stack.pop()
        if _bandB_check_zone2_direct(u0, u1, v0, v1, s0, s1):
            n_dir += 1; continue
        if v0 >= mp.mpf("0.20") and _bandB_check_zone2_near11(u0, u1, v0, v1, s0, s1):
            n_n11 += 1; continue
        assert dep < 18, f"Band B Zone 2 failed at u=[{u0},{u1}], v=[{v0},{v1}], s=[{s0},{s1}]"
        dim = max([((u1 - u0) / (1 - U_SPLIT_B), 0), (v1 - v0, 1), ((s1 - s0) / s_span, 2)])[1]
        if dim == 0:
            m = (u0 + u1) / 2
            stack.append((m, u1, v0, v1, s0, s1, dep + 1)); stack.append((u0, m, v0, v1, s0, s1, dep + 1))
        elif dim == 1:
            m = (v0 + v1) / 2
            stack.append((u0, u1, m, v1, s0, s1, dep + 1)); stack.append((u0, u1, v0, m, s0, s1, dep + 1))
        else:
            m = (s0 + s1) / 2
            stack.append((u0, u1, v0, v1, m, s1, dep + 1)); stack.append((u0, u1, v0, v1, s0, m, dep + 1))
    return ("Z2", n_dir, n_n11)


def certify_band_B(pool, s_max_mod3):
    t0 = time.time()
    s_lo = mp.mpf((1 / iv.mpf("7.0")).a)
    s_hi = mp.mpf((1 / iv.mpf("3.5")).b)
    # Explicit seam assertions linking Module 3 (s <= s_max_mod3) to Band B to Band C (a <= 3.5):
    assert s_lo <= s_max_mod3, f"Seam gap between Module 3 ({s_max_mod3}) and Band B ({s_lo})!"
    assert s_hi >= mp.mpf((1 / iv.mpf("3.5")).b)

    # Step B-1: Target inequality M/s^4 > 0, g_min > 0, and theta_0(s) > c_4a(1/s)
    t1 = time.time()
    N_s = 40
    s_pts = [s_lo] + [s_lo + (s_hi - s_lo) * mp.mpf(k) / mp.mpf(N_s) for k in range(1, N_s)] + [s_hi]
    min_M_s4 = mp.mpf("1e9"); min_gmin = mp.mpf("1e9")
    for i in range(N_s):
        sb = iv.mpf([s_pts[i], s_pts[i + 1]])
        lamb = (sb ** 2) / ((1 + sb) ** 3)
        d36 = 1 - iv.mpf("3.6") * lamb
        assert mp.mpf(d36.a) > 0
        y0 = lamb / d36
        assert mp.mpf((1 - sb * y0).a) > 0
        assert mp.mpf((1 - lamb * (1 + y0)).a) > 0
        assert mp.mpf((1 - lamb * ((1 + y0) ** 2)).a) > 0
        assert mp.mpf((1 - sb * (1 + y0) / ((1 + sb) ** 2)).a) > 0
        assert mp.mpf((1 - sb - sb * y0).a) > 0
        assert mp.mpf((1 / d36 - iv.mpf("1.6") - iv.mpf("1.6") * y0 - lamb * ((1 + y0) ** 2)).b) < 0

        dT_lo = ((1 + y0) ** 2) / (((1 + sb) ** 3) * (1 - lamb * ((1 + y0) ** 2))) - (sb ** 2) / (((1 + sb) ** 6) * (d36 ** 2))
        dT_hi = ((1 + y0) / (((1 + sb) ** 3) * (1 - lamb * (1 + y0)))
                 + (iv.mpf(4) / iv.mpf(27)) * ((1 + y0) ** 2)
                 / ((1 - sb - sb * y0) * ((1 + sb) ** 6) * ((1 - lamb * (1 + y0)) ** 2) * (1 - sb * (1 + y0) / ((1 + sb) ** 2))))
        assert mp.mpf(dT_lo.a) > 0 and mp.mpf(dT_lo.a) <= mp.mpf(dT_hi.b)
        dT_box = iv.mpf([mp.mpf(dT_lo.a), mp.mpf(dT_hi.b)])
        dub = d_ub_iv(sb); assert mp.mpf(dub.a) > 0
        db = iv.mpf([mp.mpf(0), mp.mpf(dub.b)])
        phi0 = 1 / (1 + 3 * sb + 2 * (sb ** 2) + sb ** 3)
        th0_hat = ((1 + sb) ** 2) * phi0; th0 = (sb ** 3) * th0_hat
        assert mp.mpf((th0 - c_of_a_step4a_iv(1 / sb)).a) > 0
        H0 = 1 - sb + (sb ** 4) * phi0
        D1 = H0 + (sb ** 2) * db; DT = D1 + (sb ** 4) * (dT_box - phi0)
        E = (1 - th0) / D1 + KAPPA0_B * (sb ** 4); assert mp.mpf(E.a) > 0
        gmin = 1 - (sb ** 2) * db * E; assert mp.mpf(gmin.a) > 0
        if mp.mpf(gmin.a) < min_gmin:
            min_gmin = mp.mpf(gmin.a)
        B1 = 1 - sb + (sb ** 2) * db
        term1 = 2 * ((1 - th0) * phi0 / D1 - KAPPA0_B * B1)
        term4 = dT_box * (((1 - (sb ** 2) * db * E) ** 2) / (1 - sb) - 2 * E + (sb ** 2) * db * (E ** 2))
        term23 = db * (-sb * th0_hat * (2 - th0) / D1
                       + (sb ** 2) * ((dT_box - phi0) / (D1 * DT)
                                     + KAPPA0_B * (2 * (1 - th0) + KAPPA0_B * (sb ** 4) * D1)
                                     - phi0 * (E ** 2)))
        term5 = -(sb ** 2) * (th0_hat ** 2)
        M_s4 = term1 + term4 + term23 + term5
        assert mp.mpf(M_s4.a) > 0
        if mp.mpf(M_s4.a) < min_M_s4:
            min_M_s4 = mp.mpf(M_s4.a)
    print(f"  [Band B / Step B-1 PASS] M/s^4 >= +{float(min_M_s4):.5f}, g_min >= {float(min_gmin):.6f}, "
          f"th0 > c_4a ({time.time()-t1:.2f}s)", flush=True)

    # Steps B-2 & B-3 in parallel across 4 s-tiles x 3 zones = 12 tasks!
    t2 = time.time()
    s_grid = [s_lo, mp.mpf("0.18"), mp.mpf("0.22"), mp.mpf("0.255"), s_hi]
    s_span = s_hi - s_lo
    b_tasks = []
    for i in range(len(s_grid) - 1):
        sa, sb_p = s_grid[i], s_grid[i + 1]
        b_tasks.append(("Z1a", mp.mpf(0), U_CUT, V_CUT, mp.mpf(1), sa, sb_p, s_span, "0.35"))
        b_tasks.append(("Z1b", U_CUT, U_SPLIT_B, mp.mpf(0), mp.mpf(1), sa, sb_p, s_span, "0.50"))
        b_tasks.append(("Z2", sa, sb_p, s_span))
    n_z1a = 0; n_z1b = 0; n_z2d = 0; n_z2n = 0
    for kind, c1, c2 in pool.map(_bandB_worker, b_tasks):
        if kind == "Z1a":
            n_z1a += c1
        elif kind == "Z1b":
            n_z1b += c1
        else:
            n_z2d += c1; n_z2n += c2
    print(f"  [Band B / Steps B-2 & B-3 PASS] Zone 1a={n_z1a}, Zone 1b={n_z1b}, "
          f"Zone 2 direct={n_z2d}, near11={n_z2n} iv boxes ({time.time()-t2:.2f}s)", flush=True)
    print(f"[BAND B PASS] ALL a in [3.5, 7.0], ALL delta in (0, d_ub(a)] CERTIFIED in {time.time()-t0:.2f}s!", flush=True)


# ============================================================================
# MODULE 4 / BAND C: a in [floor(1.1407), 3.50], 100% CLOSED-FORM
# ============================================================================
def eval_target_quad(u, v, s, t, us_iv, q_sc, q_ea, alpha_iv, gt0_iv, gt1_iv, gt2_iv, sref_iv, mode="P"):
    is_d = isinstance(s, Dual4)
    if is_d:
        us_iv = Dual4(us_iv); q_sc = Dual4(q_sc); q_ea = Dual4(q_ea); alpha_iv = Dual4(alpha_iv)
        gt0_iv = Dual4(gt0_iv); gt1_iv = Dual4(gt1_iv); gt2_iv = Dual4(gt2_iv)
        sref_iv = Dual4(sref_iv); z0 = Dual4(iv.mpf(0))
    else:
        z0 = iv.mpf(0)
    ds_gt = s - sref_iv
    gt_val = gt0_iv + ds_gt * (gt1_iv + gt2_iv * ds_gt)
    s2 = s * s; s3 = s2 * s; s4 = s2 * s2
    phi0 = 1 / (1 + 3 * s + 2 * s2 + s3)
    th0 = s3 * ((1 + s) * (1 + s)) * phi0
    H0 = 1 - s + s4 * phi0
    d = t * t; s2d = s2 * d
    c_b = th0 * alpha_iv
    eta_s = (1 - c_b - gt_val) / (H0 + s2d)
    eps = t * ((s3 / (1 + s)).sqrt() if is_d else iv.sqrt(s3 / (1 + s))) * C_E
    xi = 1 - u
    q = q_ea + q_sc * xi * (2 - xi)
    Ksv = K0hat_uv_d(us_iv, v, s)
    Kuv = K0hat_uv_d(u, v, s)
    Ku0 = K0hat_ua_d(u, s)
    K0v = K0hat_ua_d(v, s)
    Duv = D_uv_d(u, v, s, eps)
    Kt_uv = Kuv + s2d * (1 + Duv)
    s2dDu0 = s2d * D_uv_d(u, z0, s, eps)
    if mode == "V":
        A = c_b / Ksv + q * (1 / K0v - 1 / Ksv)
        B = eta_s / Ksv - (1 + Duv) / (Kuv * Kt_uv)
        return A + (Ku0 + s2d) * B, A + (Ku0 + s2d + s2dDu0) * B
    KK = Kuv * Kt_uv
    rat0s = K0v / Ksv
    term_base = (q * (1 - rat0s) + c_b * rat0s) * KK
    coef_u0 = K0v * (eta_s * KK / Ksv - (1 + Duv))
    return term_base + (Ku0 + s2d) * coef_u0, term_base + (Ku0 + s2d + s2dDu0) * coef_u0


def enclose_dT0_list_iv(a0, a1):
    step = mp.mpf("0.004") if a0 < mp.mpf("1.80") else (mp.mpf("0.008") if a0 < mp.mpf("2.30") else mp.mpf("0.015"))
    n_sub = max(2, int(mp.ceil((a1 - a0) / step)))
    aa_pts = [a0] + [a0 + (a1 - a0) * mp.mpf(k) / mp.mpf(n_sub) for k in range(1, n_sub)] + [a1]
    am_mid = (a0 + a1) / 2
    with mp.workdps(12):
        am_ = +am_mid; sigm = am_ * (am_ - 1); a2m = am_ * am_; inv_am = 1 / am_
        zes = [mp.mpf(j) / 20 for j in range(21)]
        D1s = [(1 + z * am_) / (a2m + am_ * (3 - z) + 2 + inv_am) for z in zes]
        best_hi = (mp.mpf("1e9"), mp.mpf("0.68"), mp.mpf("0.825"))
        for xi2 in [mp.mpf("0.55"), mp.mpf("0.65"), mp.mpf("0.72"), mp.mpf("0.78"), mp.mpf("0.84")]:
            D2s = [-a2m * xi2 * z + (1 + xi2 * am_) * (1 + z * am_)
                   / (a2m * (1 - xi2 * z) + am_ * (3 - xi2 - z) + 2 + inv_am) for z in zes]
            for w2_i in range(1, 14):
                w2 = mp.mpf(w2_i) / 40; w1 = 1 - w2
                mx = max((sigm * (w1 * D1s[j] + w2 * D2s[j]) + D1s[j] * D2s[j])
                         / (sigm + w1 * D2s[j] + w2 * D1s[j]) for j in range(21))
                if mx < best_hi[0]:
                    best_hi = (mx, xi2, w1)
    x2_iv = iv.mpf(mp.mpf(best_hi[1])); u1_iv = iv.mpf(1); u2_iv = 1 - x2_iv
    w1_iv = iv.mpf(mp.mpf(best_hi[2])); w2_iv = 1 - w1_iv
    assert mp.mpf(w1_iv.a) > 0 and mp.mpf(w2_iv.a) > 0 and mp.mpf(x2_iv.a) > 0 and mp.mpf(x2_iv.b) < 1
    out = []
    for s_i in range(n_sub):
        aa0, aa1 = aa_pts[s_i], aa_pts[s_i + 1]
        assert aa0 <= aa1
        ab_s = iv.mpf([aa0, aa1]); a2_s = ab_s * ab_s; sb_s = 1 / ab_s
        lamb = (sb_s ** 2) / ((1 + sb_s) ** 3)
        d36 = 1 - iv.mpf("3.6") * lamb
        assert mp.mpf(d36.a) > 0
        y0 = lamb / d36
        assert mp.mpf((1 - sb_s * y0).a) > 0 and mp.mpf((1 - lamb * ((1 + y0) ** 2)).a) > 0
        dT_lo_iv = (sb_s ** 2) * (((1 + y0) ** 2) / (((1 + sb_s) ** 3) * (1 - lamb * ((1 + y0) ** 2)))
                                  - (sb_s ** 2) / (((1 + sb_s) ** 6) * (d36 ** 2)))
        dK0_s = mp.mpf((iv.mpf(aa1) / (((1 + iv.mpf(aa1)) ** 3) - iv.mpf(aa1))).a)
        dT_lo_s = max(dK0_s, mp.mpf(dT_lo_iv.a))
        sigp_s = iv.mpf([mp.mpf((iv.mpf(aa0) * (iv.mpf(aa0) - 1)).a),
                         mp.mpf((iv.mpf(aa1) * (iv.mpf(aa1) - 1)).b)])
        dT_hi_s = mp.mpf("-1e9")
        stack = [(mp.mpf(j) / 8, mp.mpf(j + 1) / 8, 0) for j in range(8)]
        while stack:
            v0, v1, dep = stack.pop()
            vb = iv.mpf([v0, v1]); ze = 1 - vb
            K1 = K0_uv_iv(u1_iv, vb, ab_s); K2 = K0_uv_iv(u2_iv, vb, ab_s)
            assert mp.mpf(K1.a) > 0 and mp.mpf(K2.a) > 0
            D1 = (1 + ze * ab_s) / (a2_s + ab_s * (3 - ze) + 2 + 1 / ab_s)
            Phi2 = (1 + x2_iv * ab_s) * (1 + ze * ab_s) / (a2_s * (1 - x2_iv * ze) + ab_s * (3 - x2_iv - ze) + 2 + 1 / ab_s)
            D2_a = -a2_s * x2_iv * ze + Phi2; D2_b = K2 - sigp_s
            D2 = iv.mpf([max(mp.mpf(D2_a.a), mp.mpf(D2_b.a)), min(mp.mpf(D2_a.b), mp.mpf(D2_b.b))])
            val = (sigp_s * (w1_iv * D1 + w2_iv * D2) + D1 * D2) / (w1_iv * K2 + w2_iv * K1)
            if mp.mpf(val.b) <= dT_hi_s:
                continue
            if mp.mpf(val.b) - mp.mpf(val.a) > mp.mpf("0.0015") and dep < 6:
                vm = (v0 + v1) / 2
                stack.append((vm, v1, dep + 1)); stack.append((v0, vm, dep + 1))
                continue
            if mp.mpf(val.b) > dT_hi_s:
                dT_hi_s = mp.mpf(val.b)
        assert dT_lo_s > 0 and dT_lo_s <= dT_hi_s
        out.append((aa0, aa1, iv.mpf([dT_lo_s, dT_hi_s])))
    return out


def check_M_and_gmin_quad(dT0_list, d0, d1, alpha_iv, gt0_iv, gt1_iv, gt2_iv, sref_iv):
    nd = 4 if (d1 - d0) > mp.mpf("0.02") else 2
    for aa0, aa1, dT0_s in dT0_list:
        ab_s = iv.mpf([aa0, aa1])
        d1_eff = min(d1, mp.mpf(d_ub_from_a_iv(ab_s).b))
        if d0 > d1_eff:
            continue
        d_sub = [d0] + [d0 + (d1_eff - d0) * mp.mpf(k) / mp.mpf(nd) for k in range(1, nd)] + [d1_eff]
        sb_s = 1 / ab_s
        c_s = alpha_iv * th0_from_s_iv(sb_s)
        ds_gt = sb_s - sref_iv
        gt_s = gt0_iv + ds_gt * (gt1_iv + gt2_iv * ds_gt)
        a0_i, a1_i = iv.mpf(aa0), iv.mpf(aa1)
        sigp = iv.mpf([mp.mpf((a0_i * (a0_i - 1)).a), mp.mpf((a1_i * (a1_i - 1)).b)])
        dK0 = iv.mpf([mp.mpf((a1_i / (((1 + a1_i) ** 3) - a1_i)).a),
                      mp.mpf((a0_i / (((1 + a0_i) ** 3) - a0_i)).b)])
        K00 = sigp + dK0
        for j in range(nd):
            assert d_sub[j] <= d_sub[j + 1]
            db_s = iv.mpf([d_sub[j], d_sub[j + 1]])
            D0 = K00 + db_s; Ds = sigp + db_s
            if mp.mpf((K00 + db_s * (c_s + gt_s)).a) <= 0:
                return False
            dK0_over_D0 = 1 / (1 + Ds / dK0)
            rho = gt_s + (1 - c_s - gt_s) * dK0_over_D0
            # Exact concavity in T_0: d^2 M / dT_0^2 = -2*delta / (T_0 + delta)^3 < 0,
            # so min_{dT in [dT0_s.a, dT0_s.b]} M(sig_+ + dT) is attained at one of the two endpoints!
            for dT_ep in (iv.mpf(mp.mpf(dT0_s.a)), iv.mpf(mp.mpf(dT0_s.b))):
                T0_over_Ds = 1 + (dT_ep - db_s) / Ds
                if mp.mpf(T0_over_Ds.a) <= 0:
                    return False
                b_dir = 2 * rho - 1 / (1 + Ds / dT_ep)
                term_lo = mp.mpf(b_dir.a)
                if mp.mpf(dT_ep.a) >= mp.mpf(dK0.b):
                    b_comb = 2 * gt_s + (2 * (1 - c_s - gt_s) * dK0 - dT_ep) / D0
                    if mp.mpf(b_comb.a) > term_lo:
                        term_lo = mp.mpf(b_comb.a)
                bracket_lo = iv.mpf(term_lo) + db_s * ((c_s + rho) ** 2) / sigp
                M_val = T0_over_Ds * bracket_lo + 2 * c_s * (dT_ep - db_s) / Ds - c_s * c_s
                if mp.mpf(M_val.a) <= 0:
                    return False
    return True


def fit_certified_quad_gt(dT0_list, a0, a1, d0, d1, alpha_iv):
    def find_pt(a_pt, dT0_box):
        pt_list = [(a_pt, a_pt, dT0_box)]
        if not check_M_and_gmin_quad(pt_list, d0, d1, alpha_iv, iv.mpf(0), iv.mpf(0), iv.mpf(0), iv.mpf(0)):
            return None
        lo_g, hi_g = mp.mpf("-0.5"), mp.mpf(0)
        while check_M_and_gmin_quad(pt_list, d0, d1, alpha_iv, iv.mpf(lo_g), iv.mpf(0), iv.mpf(0), iv.mpf(0)):
            hi_g = lo_g; lo_g -= mp.mpf("0.5")
            if lo_g < mp.mpf("-5"):
                break
        for _ in range(16):
            m = (lo_g + hi_g) / 2
            if check_M_and_gmin_quad(pt_list, d0, d1, alpha_iv, iv.mpf(m), iv.mpf(0), iv.mpf(0), iv.mpf(0)):
                hi_g = m
            else:
                lo_g = m
        return hi_g

    am = (a0 + a1) / 2
    mid_idx = len(dT0_list) // 2
    g_A = find_pt(a0, dT0_list[0][2])
    g_M = find_pt(am, dT0_list[mid_idx][2])
    g_B = find_pt(a1, dT0_list[-1][2])
    assert g_A is not None and g_M is not None and g_B is not None
    s_B = 1 / a1; s_M = 1 / am; s_A = 1 / a0
    xM = s_M - s_B; xA = s_A - s_B
    gt0_b = g_B
    d1_M = (g_M - g_B) / xM
    d1_A = (g_A - g_B) / xA
    gt2_b = (d1_A - d1_M) / (xA - xM)
    gt1_b = d1_M - gt2_b * xM
    sref_iv = iv.mpf(s_B)
    lo_s, hi_s = mp.mpf(0), mp.mpf(1)
    for _ in range(14):
        m = (lo_s + hi_s) / 2
        if check_M_and_gmin_quad(dT0_list, d0, d1, alpha_iv,
                                 iv.mpf(gt0_b * m), iv.mpf(gt1_b * m), iv.mpf(gt2_b * m), sref_iv):
            lo_s = m
        else:
            hi_s = m
    sc = lo_s * mp.mpf("0.985")
    gt0_iv = iv.mpf(gt0_b * sc); gt1_iv = iv.mpf(gt1_b * sc); gt2_iv = iv.mpf(gt2_b * sc)
    assert check_M_and_gmin_quad(dT0_list, d0, d1, alpha_iv, gt0_iv, gt1_iv, gt2_iv, sref_iv)
    for aa0, aa1, _ in dT0_list:
        ds_chk = 1 / iv.mpf([aa0, aa1]) - sref_iv
        assert mp.mpf((gt0_iv + ds_chk * (gt1_iv + gt2_iv * ds_chk)).b) <= 0
    return gt0_b * sc, gt1_b * sc, gt2_b * sc, s_B


def _bandC_check_q1_3d_box(u0, u1, v0, v1, a0, a1, d0_sl, d1_sl, us_iv, alpha_iv, gt0_iv, gt1_iv, gt2_iv, sref_iv, max_d_dep, check_c_mono):
    ub = iv.mpf([u0, u1]); vb = iv.mpf([v0, v1]); ab = iv.mpf([a0, a1]); sb = 1 / ab
    dub = d_ub_from_a_iv(ab)
    d_hi = min(d1_sl, mp.mpf(dub.b))
    if d0_sl > d_hi:
        return True
    db = iv.mpf([d0_sl, d_hi]); s2 = sb * sb; s2d = s2 * db
    s13 = (1 + sb) ** 3; s_den0 = s13 - s2
    phi0 = 1 / (1 + 3 * sb + 2 * s2 + sb ** 3)
    th0 = (sb ** 3) * ((1 + sb) ** 2) * phi0
    H0 = 1 - sb + (sb ** 4) * phi0
    c_b = alpha_iv * th0
    ds_g = sb - sref_iv
    gt_b = gt0_iv + ds_g * (gt1_iv + gt2_iv * ds_g)
    eta = (1 - c_b - gt_b) / (H0 + s2d)
    Kuv = K0hat_uv_iv(ub, vb, sb); Ksv = K0hat_uv_iv(us_iv, vb, sb)
    Ku0 = K0hat_ua_exact(ub, sb)
    al_s = ub / (1 + sb); be_s = vb / (1 + sb); z_s = (1 - al_s) * (1 - be_s); w_s = 1 - z_s
    Duv_ub = CGCE2 * sb * (z_s ** 3) / (sb + w_s)
    s2dDuv = dD_mono_s_iv(ub, vb, sb, d0_sl, d_hi)
    s2dDu0 = dD_mono_s_iv(ub, iv.mpf(0), sb, d0_sl, d_hi)
    Kt_uv = Kuv + s2d + s2dDuv; Kt_u0 = Ku0 + s2d + s2dDu0
    if check_c_mono:
        assert mp.mpf((H0 + s2d - Kt_u0).a) > 0
        assert mp.mpf(gt_b.b) <= 0
    if v0 == 0:
        K0v_ub = K0hat_ua_exact(iv.mpf(v1), sb)
        val = 1 / K0v_ub - (1 - c_b) / Ksv + Kt_u0 * (eta / Ksv - (1 + Duv_ub) / (Kuv * Kt_uv))
        return mp.mpf(val.a) > 0
    K0v = K0hat_ua_exact(vb, sb)
    xi = 1 - ub; ze = 1 - vb; xis = 1 - us_iv
    use_A = (v0 >= mp.mpf("0.45"))
    if use_A:
        s_den_s1 = s13 - sb * (sb + xis); s_den_01 = s13 - sb * (sb + 1)
        s_den_sv = s13 - (sb + xis) * (sb + ze); s_den_0v = s13 - (sb + 1) * (sb + ze)
        s_den_uv = s13 - (sb + xi) * (sb + ze)
        f0_al = (sb ** 3) * s13 * (xis / s_den_s1 - (1 - alpha_iv) / s_den_01) / s_den0
        br_al = ((us_iv - c_b) + s2 * s13 * (sb + xis) / (s_den_sv * s_den_s1)
                 - (1 - c_b) * s2 * s13 * (sb + 1) / (s_den_0v * s_den_01))
        Ruv = s2 * s13 * (sb * (xi + ze) + xi * ze) / (s_den_uv * s_den0)
        Rsv = s2 * s13 * (sb * (xis + ze) + xis * ze) / (s_den_sv * s_den0)
        Del_uv = -xi * ze + Ruv
        D_hi_u = iv.mpf(mp.mpf(Duv_ub.b)); s2d_hi_u = s2d * (1 + D_hi_u); Ktv_hi_u = Kuv + s2d_hi_u
        denA = (H0 + s2d) * Ksv * Kuv * Ktv_hi_u
        ze_c = br_al / (K0v * Ksv) + Kt_u0 * (H0 * (xis - 2 * xi) + s2d_hi_u * (xis - xi)) / denA
        num_r = (H0 * (2 * Ruv - Rsv) + (Del_uv ** 2) - (c_b + gt_b) * (Kuv ** 2)
                 - D_hi_u * Ksv * H0 + s2d_hi_u * ((Ruv - Rsv) - (c_b + gt_b) * Kuv))
        if mp.mpf((f0_al / (K0v * Ksv) + ze * ze_c + Kt_u0 * num_r / denA).a) > 0:
            return True
    Kuv_m_K0v = ub * ((1 - be_s) * (sb * (w_s + be_s) + w_s * be_s) / ((sb + w_s) * (sb + be_s)) - sb * be_s)
    if mp.mpf((Kuv_m_K0v / (K0v * Kuv) + (1 - (Ku0 + s2dDu0) * (1 + Duv_ub) / Kuv) / Kt_uv
               - (1 - c_b) / Ksv + Kt_u0 * eta / Ksv).a) > 0:
        return True
    if mp.mpf((1 / K0v - (1 - c_b) / Ksv + Kt_u0 * (eta / Ksv - (1 + Duv_ub) / (Kuv * Kt_uv))).a) > 0:
        return True
    if max_d_dep <= 0:
        return False
    d_init = [mp.mpf(0), mp.mpf("0.015"), mp.mpf("0.10"), mp.mpf("0.35"), mp.mpf("1.0")]
    dst = [(d0_sl + (d_hi - d0_sl) * d_init[k], d0_sl + (d_hi - d0_sl) * d_init[k + 1], 0)
           for k in range(len(d_init) - 1)]
    while dst:
        dd0, dd1, dd = dst.pop()
        ddb = iv.mpf([dd0, dd1]); ss2d = s2 * ddb
        ep = C_E * iv.sqrt(ddb * (sb ** 3) / (1 + sb))
        Duv_d = D_uv_d(ub, vb, sb, ep)
        sd_uv = dD_mono_s_iv(ub, vb, sb, dd0, dd1)
        sd_u0 = dD_mono_s_iv(ub, iv.mpf(0), sb, dd0, dd1)
        Ktu_d = Ku0 + ss2d + sd_u0; Ktv_d = Kuv + ss2d + sd_uv
        eta_d = (1 - c_b - gt_b) / (H0 + ss2d)
        if use_A:
            D_hi_d = iv.mpf(mp.mpf(Duv_d.b)); s2d_hi_d = ss2d * (1 + D_hi_d); Ktv_hi_d = Kuv + s2d_hi_d
            denA_d = (H0 + ss2d) * Ksv * Kuv * Ktv_hi_d
            ze_cd = br_al / (K0v * Ksv) + Ktu_d * (H0 * (xis - 2 * xi) + s2d_hi_d * (xis - xi)) / denA_d
            num_rd = (H0 * (2 * Ruv - Rsv) + (Del_uv ** 2) - (c_b + gt_b) * (Kuv ** 2)
                      - D_hi_d * Ksv * H0 + s2d_hi_d * ((Ruv - Rsv) - (c_b + gt_b) * Kuv))
            if mp.mpf((f0_al / (K0v * Ksv) + ze * ze_cd + Ktu_d * num_rd / denA_d).a) > 0:
                continue
        if mp.mpf((1 / K0v - (1 - c_b) / Ksv + Ktu_d * (eta_d / Ksv - (1 + Duv_d) / (Kuv * Ktv_d))).a) > 0:
            continue
        if mp.mpf((Kuv_m_K0v / (K0v * Kuv) + (1 - (Ku0 + sd_u0) * (1 + Duv_d) / Kuv) / Ktv_d
                   - (1 - c_b) / Ksv + Ktu_d * eta_d / Ksv).a) > 0:
            continue
        if dd >= max_d_dep:
            return False
        dm = (dd0 + dd1) / 2
        dst.append((dm, dd1, dd + 1)); dst.append((dd0, dm, dd + 1))
    return True


def _bandC_q1_worker(task):
    (bname, zname, u_lo, u_hi, v_lo, v_hi, us_s, a0, a1, d0_sl, d1_sl, als, gt0, gt1, gt2, sref, chk_m) = task
    t_s = time.time()
    us_iv = iv.mpf(us_s); alpha_iv = iv.mpf(als)
    gt0_iv = iv.mpf(gt0); gt1_iv = iv.mpf(gt1); gt2_iv = iv.mpf(gt2); sref_iv = iv.mpf(sref)
    if v_lo > 0:
        v_grid = [v_lo, mp.mpf("0.08"), mp.mpf("0.16"), mp.mpf("0.35"), mp.mpf("0.65"), v_hi]
    else:
        v_grid = [mp.mpf(0), mp.mpf("0.015"), mp.mpf("0.05"), mp.mpf("0.14"), mp.mpf("0.35"), mp.mpf("0.65"), v_hi]
    u_grid = [u_lo, mp.mpf("0.12"), u_hi] if u_lo > 0 else [u_lo, u_hi]
    stack = [(u_grid[i], u_grid[i + 1], v_grid[j], v_grid[j + 1], a0, a1, 0)
             for i in range(len(u_grid) - 1) for j in range(len(v_grid) - 1)]
    cnt = 0
    while stack:
        u0, u1, v0, v1, aa0, aa1, dep = stack.pop()
        md = 8 if dep >= 6 else (3 if dep >= 2 else 0)
        if _bandC_check_q1_3d_box(u0, u1, v0, v1, aa0, aa1, d0_sl, d1_sl, us_iv, alpha_iv,
                                  gt0_iv, gt1_iv, gt2_iv, sref_iv, md, chk_m):
            cnt += 1; continue
        if dep >= 18:
            return (False, bname, zname, a0, a1, cnt, time.time() - t_s)
        dim = max([((u1 - u0) / max(u0, mp.mpf("0.01")), 0),
                   ((v1 - v0) / max(v0, mp.mpf("0.02")), 1),
                   (2 * (aa1 - aa0) / (aa0 - 1), 2)])[1]
        if dim == 0:
            m = (u0 + u1) / 2
            stack.append((m, u1, v0, v1, aa0, aa1, dep + 1)); stack.append((u0, m, v0, v1, aa0, aa1, dep + 1))
        elif dim == 1:
            m = (v0 + v1) / 2
            stack.append((u0, u1, m, v1, aa0, aa1, dep + 1)); stack.append((u0, u1, v0, m, aa0, aa1, dep + 1))
        else:
            m = (aa0 + aa1) / 2
            stack.append((u0, u1, v0, v1, m, aa1, dep + 1)); stack.append((u0, u1, v0, v1, aa0, m, dep + 1))
    return (True, bname, zname, a0, a1, cnt, time.time() - t_s)


def _bandC_dual4_worker(task):
    (bname, zname, u_lo, u_hi, v_lo, v_hi, us_s, qsc_s, qea_s, a0, a1, d0, d1, als, gt0, gt1, gt2, sref) = task
    t_start = time.time()
    us_iv = iv.mpf(us_s); q_sc = iv.mpf(qsc_s); q_ea = iv.mpf(qea_s)
    alpha_iv = iv.mpf(als); gt0_iv = iv.mpf(gt0); gt1_iv = iv.mpf(gt1); gt2_iv = iv.mpf(gt2); sref_iv = iv.mpf(sref)
    assert mp.mpf(q_sc.a) >= 0 and mp.mpf(q_ea.a) >= 0 and u_lo > 0

    sb0 = 1 / iv.mpf([a0, a1])
    s_lo, s_hi = mp.mpf(sb0.a), mp.mpf(sb0.b)
    t_lo = mp.mpf(0) if d0 == 0 else mp.mpf(iv.sqrt(iv.mpf(d0)).a)
    t_hi = mp.mpf(iv.sqrt(iv.mpf(d1)).b)

    is_z2 = (zname == "Z2")
    v_grid = [mp.mpf(0), mp.mpf("0.04"), mp.mpf("0.15"), mp.mpf("0.40"), mp.mpf("0.70"), v_hi]
    u_grid = [u_lo, (u_lo + u_hi) / 2, u_hi]
    stack = [(u_grid[i], u_grid[i + 1], v_grid[j], v_grid[j + 1], s_lo, s_hi, t_lo, t_hi, 0)
             for i in range(len(u_grid) - 1) for j in range(len(v_grid) - 1)]
    cnt = 0
    while stack:
        u0, u1, v0, v1, s0, s1, t0, t1, dep = stack.pop()
        ub = iv.mpf([u0, u1]); vb = iv.mpf([v0, v1]); sb = iv.mpf([s0, s1]); tb = iv.mpf([t0, t1])
        dub_b = d_ub_from_a_iv(1 / sb)
        t1_cap = mp.mpf(iv.sqrt(iv.mpf(mp.mpf(dub_b.b))).b)
        if t0 > t1_cap:
            cnt += 1; continue
        if t1 > t1_cap:
            t1 = t1_cap; tb = iv.mpf([t0, t1])
        mode = "V" if (is_z2 and v0 > 0) else "P"
        P0, P1 = eval_target_quad(ub, vb, sb, tb, us_iv, q_sc, q_ea, alpha_iv, gt0_iv, gt1_iv, gt2_iv, sref_iv, mode)
        if mp.isfinite(mp.mpf(P0.a)) and mp.isfinite(mp.mpf(P1.a)) and mp.mpf(P0.a) > 0 and mp.mpf(P1.a) > 0:
            cnt += 1; continue
        P0d, P1d = eval_target_quad(Dual4(ub, iv.mpf(1)), Dual4(vb, None, iv.mpf(1)),
                                    Dual4(sb, None, None, iv.mpf(1)), Dual4(tb, None, None, None, iv.mpf(1)),
                                    us_iv, q_sc, q_ea, alpha_iv, gt0_iv, gt1_iv, gt2_iv, sref_iv, mode)
        cu0 = baumann_center(u0, u1, P0d.d0); cv0 = baumann_center(v0, v1, P0d.d1)
        cs0 = baumann_center(s0, s1, P0d.d2); ct0 = baumann_center(t0, t1, P0d.d3)
        assert u0 <= cu0 <= u1 and v0 <= cv0 <= v1 and s0 <= cs0 <= s1 and t0 <= ct0 <= t1
        P0_c, _ = eval_target_quad(iv.mpf(cu0), iv.mpf(cv0), iv.mpf(cs0), iv.mpf(ct0),
                                   us_iv, q_sc, q_ea, alpha_iv, gt0_iv, gt1_iv, gt2_iv, sref_iv, mode)
        if mp.isfinite(mp.mpf(P0_c.b)) and mp.mpf(P0_c.b) <= 0:
            return (False, bname, zname, a0, a1, cnt, time.time() - t_start)
        t0_t = [P0d.d0 * (ub - iv.mpf(cu0)), P0d.d1 * (vb - iv.mpf(cv0)),
                P0d.d2 * (sb - iv.mpf(cs0)), P0d.d3 * (tb - iv.mpf(ct0))]
        P0_b = P0_c + t0_t[0] + t0_t[1] + t0_t[2] + t0_t[3]
        cu1 = baumann_center(u0, u1, P1d.d0); cv1 = baumann_center(v0, v1, P1d.d1)
        cs1 = baumann_center(s0, s1, P1d.d2); ct1 = baumann_center(t0, t1, P1d.d3)
        assert u0 <= cu1 <= u1 and v0 <= cv1 <= v1 and s0 <= cs1 <= s1 and t0 <= ct1 <= t1
        _, P1_c = eval_target_quad(iv.mpf(cu1), iv.mpf(cv1), iv.mpf(cs1), iv.mpf(ct1),
                                   us_iv, q_sc, q_ea, alpha_iv, gt0_iv, gt1_iv, gt2_iv, sref_iv, mode)
        if mp.isfinite(mp.mpf(P1_c.b)) and mp.mpf(P1_c.b) <= 0:
            return (False, bname, zname, a0, a1, cnt, time.time() - t_start)
        t1_t = [P1d.d0 * (ub - iv.mpf(cu1)), P1d.d1 * (vb - iv.mpf(cv1)),
                P1d.d2 * (sb - iv.mpf(cs1)), P1d.d3 * (tb - iv.mpf(ct1))]
        P1_b = P1_c + t1_t[0] + t1_t[1] + t1_t[2] + t1_t[3]
        if mp.isfinite(mp.mpf(P0_b.a)) and mp.isfinite(mp.mpf(P1_b.a)) and mp.mpf(P0_b.a) > 0 and mp.mpf(P1_b.a) > 0:
            cnt += 1; continue
        if dep >= 28:
            return (False, bname, zname, a0, a1, cnt, time.time() - t_start)
        terms = t1_t if (not mp.isfinite(mp.mpf(P1_b.a)) or mp.mpf(P1_b.a) <= mp.mpf(P0_b.a)) else t0_t
        losses = [-mp.mpf(x.a) for x in terms]
        if all(mp.isfinite(x) for x in losses) and max(losses) > 0:
            dim = max((losses[k], k) for k in range(4))[1]
        else:
            dim = max(((u1 - u0) / (u_hi - u_lo), 0), ((v1 - v0) / (v_hi - v_lo), 1),
                      ((s1 - s0) / (s_hi - s_lo + mp.mpf("1e-9")), 2),
                      ((t1 - t0) / (t_hi - t_lo + mp.mpf("1e-9")), 3))[1]
        if dim == 0:
            m = (u0 + u1) / 2
            stack.append((m, u1, v0, v1, s0, s1, t0, t1, dep + 1)); stack.append((u0, m, v0, v1, s0, s1, t0, t1, dep + 1))
        elif dim == 1:
            m = (v0 + v1) / 2
            stack.append((u0, u1, m, v1, s0, s1, t0, t1, dep + 1)); stack.append((u0, u1, v0, m, s0, s1, t0, t1, dep + 1))
        elif dim == 2:
            m = (s0 + s1) / 2
            stack.append((u0, u1, v0, v1, m, s1, t0, t1, dep + 1)); stack.append((u0, u1, v0, v1, s0, m, t0, t1, dep + 1))
        else:
            m = (t0 + t1) / 2
            stack.append((u0, u1, v0, v1, s0, s1, m, t1, dep + 1)); stack.append((u0, u1, v0, v1, s0, s1, t0, m, dep + 1))
    return (True, bname, zname, a0, a1, cnt, time.time() - t_start)


def _bandC_dispatch(item):
    kind, payload = item
    return _bandC_q1_worker(payload) if kind == "Q1" else _bandC_dual4_worker(payload)


def certify_band_C(pool):
    t0 = time.time()
    a_min = mp.mpf(iv.mpf("1.1407").a)
    z_b0_rest = [
        ("Z1b", U_CUT,          mp.mpf("0.34"), mp.mpf(0), mp.mpf(1), "0.50", "0",     "1"),
        ("Z1c", mp.mpf("0.34"), mp.mpf("0.52"), mp.mpf(0), mp.mpf(1), "0.58", "0.75",  "0.25"),
        ("Z1d", mp.mpf("0.52"), mp.mpf("0.68"), mp.mpf(0), mp.mpf(1), "0.74", "0.92",  "0.08"),
        ("Z1e", mp.mpf("0.68"), mp.mpf("0.84"), mp.mpf(0), mp.mpf(1), "0.94", "1.04",  "0.006"),
        ("Z2",  mp.mpf("0.84"), mp.mpf(1),      mp.mpf(0), mp.mpf(1), "1",    "1.05",  "0.002"),
    ]
    z_b1a_rest = [
        ("Z1b", U_CUT,          mp.mpf("0.32"), mp.mpf(0), mp.mpf(1), "0.50", "0",     "1"),
        ("Z1c", mp.mpf("0.32"), mp.mpf("0.54"), mp.mpf(0), mp.mpf(1), "0.64", "0.92",  "0.04"),
        ("Z1d", mp.mpf("0.54"), mp.mpf("0.68"), mp.mpf(0), mp.mpf(1), "0.76", "0.94",  "0.04"),
        ("Z1e", mp.mpf("0.68"), mp.mpf("0.82"), mp.mpf(0), mp.mpf(1), "0.92", "1.00",  "0.006"),
        ("Z2",  mp.mpf("0.82"), mp.mpf(1),      mp.mpf(0), mp.mpf(1), "1",    "1.02",  "0.002"),
    ]
    z_b1_rest = [
        ("Z1b", U_CUT,          mp.mpf("0.32"), mp.mpf(0), mp.mpf(1), "0.50", "0",     "1"),
        ("Z1c", mp.mpf("0.32"), mp.mpf("0.54"), mp.mpf(0), mp.mpf(1), "0.64", "0.92",  "0.04"),
        ("Z1d", mp.mpf("0.54"), mp.mpf("0.82"), mp.mpf(0), mp.mpf(1), "0.88", "0.95",  "0.005"),
        ("Z2",  mp.mpf("0.82"), mp.mpf(1),      mp.mpf(0), mp.mpf(1), "1",    "1.02",  "0.002"),
    ]
    z_b2_rest = [
        ("Z1b", U_CUT,          mp.mpf("0.34"), mp.mpf(0), mp.mpf(1), "0.50", "0",     "1"),
        ("Z1c", mp.mpf("0.34"), mp.mpf("0.56"), mp.mpf(0), mp.mpf(1), "0.64", "0.94",  "0.04"),
        ("Z1d", mp.mpf("0.56"), mp.mpf("0.80"), mp.mpf(0), mp.mpf(1), "0.88", "0.94",  "0.005"),
        ("Z2",  mp.mpf("0.80"), mp.mpf(1),      mp.mpf(0), mp.mpf(1), "1",    "0.998", "0.002"),
    ]
    for zlist in (z_b0_rest, z_b1a_rest, z_b1_rest, z_b2_rest):
        assert zlist[0][1] == U_CUT
        for k in range(len(zlist) - 1):
            assert zlist[k][2] == zlist[k + 1][1]
        assert zlist[-1][2] == 1

    band_specs = [
        ("B0",  [a_min, mp.mpf("1.16"), mp.mpf("1.19"), mp.mpf("1.23"), mp.mpf("1.28"), mp.mpf("1.34"), mp.mpf("1.40")], "0.60", z_b0_rest),
        ("B1a", [mp.mpf("1.40"), mp.mpf("1.52")],                                                                         "0.60", z_b1a_rest),
        ("B1b", [mp.mpf("1.52"), mp.mpf("1.64")],                                                                         "0.60", z_b1_rest),
        ("B2a", [mp.mpf("1.64"), mp.mpf("1.76")],                                                                         "0.62", z_b2_rest),
        ("B2",  [mp.mpf("1.76"), mp.mpf("1.95"), mp.mpf("2.15")],                                                         "0.65", z_b2_rest),
        ("B3",  [mp.mpf("2.15"), mp.mpf("2.55"), mp.mpf("3.00")],                                                         "0.74", z_b2_rest),
        ("B4",  [mp.mpf("3.00"), mp.mpf("3.50")],                                                                         "0.85", z_b2_rest),
    ]
    for bi in range(len(band_specs) - 1):
        assert band_specs[bi][1][-1] == band_specs[bi + 1][1][0]
    assert band_specs[0][1][0] <= mp.mpf(iv.mpf("1.1407").a)
    assert band_specs[-1][1][-1] == mp.mpf("3.50")

    t_prep = time.time()
    q1_items = []
    z1b_items = []
    rest_items = []
    # 1) Universal Z1a across ALL [floor(1.1407), 3.50] using exact dyadic c = (19/32)*th0 <= c_band and gt = 0 >= gt_band:
    a_z1a = [a_min, mp.mpf("1.17"), mp.mpf("1.22"), mp.mpf("1.30"), mp.mpf("1.42"),
             mp.mpf("1.60"), mp.mpf("1.85"), mp.mpf("2.15"), mp.mpf("2.55"), mp.mpf("3.00"), mp.mpf("3.50")]
    assert a_z1a[0] == a_min and a_z1a[-1] == mp.mpf("3.50")
    for k in range(len(a_z1a) - 1):
        assert a_z1a[k] < a_z1a[k + 1]
    z0 = mp.mpf(0); d_cap = mp.mpf("1.0")
    for k in range(len(a_z1a) - 1):
        q1_items.append(("Q1", ("ALL", "Z1a", mp.mpf(0), U_CUT, V_CUT, mp.mpf(1), "0.35",
                                a_z1a[k], a_z1a[k + 1], z0, d_cap, "0.59375", z0, z0, z0, z0, True)))

    # 2) Band-specific M>0, g_min>0, c_band>c_4a, gt<=0 certification + Z1b..Z2 (all Baumann Dual4 zero-pole P / V):
    u_z1b_mid = mp.mpf("0.16")
    for bname, a_pts, als, zones in band_specs:
        alpha_iv = iv.mpf(als)
        assert mp.mpf(alpha_iv.a) >= mp.mpf("0.59375")
        for i in range(len(a_pts) - 1):
            a0, a1 = a_pts[i], a_pts[i + 1]
            dT0_list = enclose_dT0_list_iv(a0, a1)
            for aa0, aa1, _ in dT0_list:
                ab_s = iv.mpf([aa0, aa1])
                assert mp.mpf((alpha_iv * th0_from_s_iv(1 / ab_s) - c_of_a_step4a_iv(ab_s)).a) > 0
            dub_b = d_ub_tight_iv(a0, a1)
            assert mp.mpf(dub_b.a) > 0
            dub_hi = mp.mpf(dub_b.b)
            d_mid = dub_hi * (mp.mpf("0.18") if bname == "B0" else mp.mpf("0.35"))
            for d0, d1 in [(mp.mpf(0), d_mid), (d_mid, dub_hi)]:
                gt0, gt1, gt2, sref = fit_certified_quad_gt(dT0_list, a0, a1, d0, d1, alpha_iv)
                for zname, ulo, uhi, vlo, vhi, us_s, qsc_s, qea_s in zones:
                    if zname == "Z1b":
                        assert ulo < u_z1b_mid < uhi
                        z1b_items.append(("D4", (bname, "Z1b-lo", ulo, u_z1b_mid, vlo, vhi, us_s, qsc_s, qea_s,
                                                 a0, a1, d0, d1, als, gt0, gt1, gt2, sref)))
                        z1b_items.append(("D4", (bname, "Z1b-hi", u_z1b_mid, uhi, vlo, vhi, us_s, qsc_s, qea_s,
                                                 a0, a1, d0, d1, als, gt0, gt1, gt2, sref)))
                    else:
                        rest_items.append(("D4", (bname, zname, ulo, uhi, vlo, vhi, us_s, qsc_s, qea_s,
                                                  a0, a1, d0, d1, als, gt0, gt1, gt2, sref)))
    # LPT order: launch slowest tasks (Z1a and Z1b) first so all workers stay balanced!
    work_items = q1_items + z1b_items + rest_items
    print(f"  [Band C Prep PASS] Certified M>0, g_min>0, c_band>c_4a, gt<=0 across {len(work_items)} zone-slices ({time.time()-t_prep:.2f}s)", flush=True)

    tot_boxes = 0; done_cnt = 0; failed = []
    for res in pool.imap_unordered(_bandC_dispatch, work_items):
        ok, bname, zname, a0_r, a1_r, nbox, dt = res
        tot_boxes += nbox; done_cnt += 1
        if not ok:
            failed.append(res)
            print(f"    FAIL: {bname}-{zname} a=[{float(a0_r):.4f},{float(a1_r):.4f}] boxes={nbox} ({dt:.2f}s)", flush=True)
        elif done_cnt % 30 == 0 or done_cnt == len(work_items):
            print(f"    [Band C] Progress: {done_cnt}/{len(work_items)} done ({tot_boxes} boxes, {time.time()-t0:.1f}s)", flush=True)
    assert not failed, f"Band C had {len(failed)} failed tasks!"
    print(f"[BAND C PASS] ALL a in [floor(1.1407), 3.50], ALL delta in (0, d_ub(a)] CERTIFIED in "
          f"{len(work_items)} zone-slices, {tot_boxes} iv boxes ({time.time()-t0:.2f}s)!", flush=True)


def main():
    t_all = time.time()
    n_workers = max(1, (os.cpu_count() or 4) - 2)
    print(f"=== PART 2 ZERO-FLOAT mpmath.iv CERTIFICATION (Modules 3 & 4) on {n_workers} workers ===", flush=True)
    ctx = mp_proc.get_context("fork")
    with ctx.Pool(processes=n_workers, initializer=_init_worker) as pool:
        s_max_mod3 = certify_module_3(pool)
        certify_step_4a(pool)
        certify_band_B(pool, s_max_mod3)
        certify_band_C(pool)
    print(f"\n================================================================================")
    print(f"[ALL-m PART 2 PASS] EVERY a >= 1.1407 (EVERY integer m >= 2) and EVERY delta in (0, d_ub(a)]")
    print(f"CERTIFIED 100% PURE ZERO-FLOAT mpmath.iv (EXIT CODE 0) in {time.time()-t_all:.2f}s!")
    print(f"================================================================================", flush=True)


if __name__ == "__main__":
    main()
