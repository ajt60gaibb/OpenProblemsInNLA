r"""
================================================================================
VERSION 7: 100% ZERO-FLOAT, PURE mpmath.iv GLOBAL COMPLEX-INTERPOLATION ENVELOPE
FOR OPEN PROBLEM MI-20 (ALL 1 < p < 2, m = 2, 3, 4, ALL MATRIX DIMENSIONS n >= 1)
================================================================================

Owner: loopy-hunter (#147; p = 5/3 anchors refreshed per #180 to #178/#179)
File:  scratch/rigorous_iv_global_interpolation_v7.py
Zero-Float Guarantee:
  Pure Python stdlib (ast, pathlib, time) + mpmath / mpmath.iv ONLY.
  ZERO `float()`, ZERO float literals, ZERO `numpy`, ZERO `scipy`, ZERO `math`,
  ZERO `sympy`, ZERO `cvxpy` anywhere in this entire file (enforced by Module 0
  whole-file AST audit on `__file__`). Every certified bound, gap, drop, slope
  jump, and improvement ratio is formatted via self-asserted strictly outward
  `iv.mpf(s)` decimal/scientific formatters (`mp.mp.dps = 55`, `iv.dps = 50`).

MATHEMATICAL FOUNDATIONS (100% SELF-CONTAINED):
  1) Exact Endpoints:
     - p = 1: C_1(m) = 1 (triangle inequality ||sum A_j||_1 <= sum ||A_j||_1).
     - p = 2: C_2(m) = sqrt((1 + sqrt(m))/2) (exact 5-line Cauchy-Schwarz proof).

  2) Complex Interpolation Theorem (Hadamard Three-Lines Log-Convexity in t = 1/p):
     For any 1 <= p_0 < p < p_1 <= 2, m >= 2, n >= 1, setting t = 1/p, t_k = 1/p_k,
     and theta = (t - t_1) / (t_0 - t_1) in [0, 1]:
       C_p(m) <= C_{p_1}(m)^{1 - theta} * C_{p_0}(m)^{theta}.
     Equivalently, t |-> log C_{1/t}(m) is bounded above by the piecewise-linear
     interpolation of any certified upper bounds at anchor points t_0 < ... < t_K.

  3) Version 7 Certified Dimension-Free Anchors at p in {1, 6/5, 5/4, 4/3, 3/2, 5/3, 2}:
     - p = 3/2 (m = 2, 3, 4): UPGRADED to `#114` (`continuum_operator_certificate.py`,
       signed off `#111`): exact 1-square operator-antitone + Taylor-jet / Krawczyk
       18-digit zero-float enclosures (gaps <= 1.002e-15 to 2.001e-14!):
         * m = 2: [1.036437168069726187, 1.036437168069746188]
         * m = 3: [1.063114500999618562, 1.063114500999623563]
         * m = 4: [1.084719139290542318, 1.084719139290543319]
     - p = 4/3:
         * m = 2: UB UPGRADED to `#114` Module 4 9-atom unified 1-square twin
           (`C_{4/3}(2) <= 1.018371580069016`); certified LB `1.018371575517`
           from `rigorous_iv_lower_bounds_p43.py` (gap <= 4.553e-9).
         * m = 3, 4: retained from v6 `rigorous_iv_proof_p43.py` (`Lam_cert = 9.06945`,
           `9.46060`, all-Lam bridge closed by `p43_all_m_part1/part2.py`) and
           `rigorous_iv_lower_bounds_p43.py`.
     - p = 6/5, 5/4:
         * 4 NEW WORLD RECORDS from `#139` (`joint_ncsos_gns_attack.py` Table 1,
           signed off `#138`, pure zero-float `mpmath.iv` all-n all-Lam over C^n):
             - p = 6/5, m = 2: Lam_cert = 33.4488  (2-matrix joint J2_AFF; C_UB <= 1.007407300775)
             - p = 5/4, m = 2, 3, 4: Lam_cert = 16.9064, 17.5981, 18.1761
         * p = 6/5, m = 3, 4: retained from v6 `rigorous_iv_multi_p_bounds.py`
           (`Lam_cert = 34.5515, 35.4668`).
     - p = 5/3:
         * 3 NEW WORLD RECORDS from `#179` (`p53_theorem5_certification.py` Table 1,
           signed off `#178`, degree-3 exactly-affine (A, B, C) lift + 8C5C,
           pure zero-float `mpmath.iv` all-n all-Lam over C^n):
             - m = 2: Lam_cert = 3.2515544  (C_UB <= 1.057349130150, gap <= 2.17e-07)
             - m = 3: Lam_cert = 3.5807660  (C_UB <= 1.098935945383, gap <= 3.22e-07)
             - m = 4: Lam_cert = 3.8598120  (C_UB <= 1.132422431322, gap <= 5.01e-07)
     - Certified multi-matrix Kubo-Ando lower bounds for p in {6/5, 5/4, 5/3} from `#49`
       (`rigorous_iv_multi_p_bounds.py`).
     - Prior baselines for Theorem G2:
         * Holden / Classical Prior:
             - m = 2: Holden {1, 4/3 (<= 1.01854047), 2}
             - m = 3, 4: Classical Hadamard {1, 2}, ((1 + sqrt(m))/2)^{1 - 1/p}
         * Version 6 Global Envelope (`rigorous_iv_global_interpolation.py`):
             - Same 7 anchor abscissae with prior v6 Lam_cert records.

  4) Universal Explicit m x m Matrix Lower Bound (ALL real p in [1, 2], ALL m >= 2):
     For T = diag(x, 1, ..., 1) (x > 1), DFT projections P_k = f_k f_k^*, and
     A_k = T^{a/2} P_k T^{b/2} (a > b > 0), canceling leading x^{a/2 + b} yields
     the singularity-free all-p lower bound:
       C_p(m) >= ((1 + (m-1) x^{-p(a+b)/2}) / (1 + (m-1) x^{-p b}))^{1/p}
                 * ((1 + (m-1) x^{-b}) / (1 + (m-1) x^{-a}))^{1/2}.

  5) Closed-Form Analytic Comparator C_4L(p, m) from `#143` Theorem 1(a)-(b)
     (`all_p_operator_closure.md`, all m >= 2, all n >= 1, real & complex):
     - Part (a), p in [3/2, 2) (t = 1/p in (1/2, 2/3], 2k - 3 = (3t - 2)/(1 - t) in (-1, 0]):
       Unique root x_4L(t, m) > 1 of strictly increasing
         g(t, x) := (1 + x)^{(3t - 2)/(1 - t)} (x^3 - 1) = m - 1,
       giving log C_4L(1/t, m) = t log((1 + x_4L)/2) - (t - 1/2) log(x_4L).
     - Part (b), p in [6/5, 3/2] (t = 1/p in [2/3, 5/6]):
       Exact closed form x_+ <= m^{1/3}, giving the EXACTLY AFFINE law in t:
         log C_4L(1/t, m) = (1/6) log(m) + t log((1 + m^{1/3}) / (2 m^{1/3})).

THEOREMS CERTIFIED BY THIS SCRIPT (100% PURE mpmath.iv, ZERO FLOATS):
  M0. Whole-File AST Zero-Float Purity Audit + Outward Formatter Self-Test.
  G1. Strict Log-Convexity of All 7 V7 Anchors (0 redundant anchors, strictly
      positive slope jumps across all 6 segments for m = 2, 3, 4).
  G2. Global Dominance Over BOTH Holden/Classical Prior (strict on ALL (1, 2)
      for m = 2, 3, 4) AND Version 6 Global Envelope (strict on ALL (1, 2) for
      m = 2; <= everywhere on [1, 2] and strict on (6/5, 4/3) U (4/3, 2) for
      m = 3, 4 where 6/5 & 4/3 retain v6 anchors).
  G3. Uniform Global Continuum Enclosure Gap sup_{p in [1, 2]} (U_V7(p; m) - C_p(m))
      certified across 604 crack-free contiguous iv-boxes covering [1/2, 1], with
      comparison against BOTH Prior curve error and V6 continuum worst-case gap.
  G4. Certified Two-Sided Enclosure Table at 17 rational & irrational exponents
      across (1, 2) (including sqrt(2) and phi) for m = 2, 3, 4.
  G5. Pointwise (15 exponents) AND Continuum (ALL real p in [6/5, 2)) Comparison
      Against `#143` Theorem 1(a)-(b) Closed-Form Analytic Bounds C_4L(p, m) and
      Hadamard C_Had(p, m), certifying U_V7(p; m) < C_4L(p, m) strictly for ALL
      real p in [6/5, 2) and m in {2, 3, 4} (exact affine proof on [6/5, 3/2] +
      202 contiguous iv-boxes on [3/2, 2]).
================================================================================
"""

import ast
from pathlib import Path
import time
import mpmath as mp
from mpmath import iv

mp.mp.dps = 55
iv.dps = 50


# ==============================================================================
# MODULE 0: WHOLE-FILE AST ZERO-FLOAT PURITY AUDIT & OUTWARD FORMATTERS
# ==============================================================================

ALLOWED_IMPORT_ROOTS = {"ast", "pathlib", "time", "mpmath"}
BANNED_NAMES = {"float", "complex", "numpy", "np", "scipy", "math", "sympy", "cvxpy"}
BANNED_ATTRS = {"float", "float64", "float32", "complex", "complex128"}


def run_ast_zero_float_audit():
    """Parse this entire script with Python's AST and certify ZERO floats / banned libs."""
    src_path = Path(__file__).resolve()
    source = src_path.read_text(encoding="utf-8")
    tree = ast.parse(source, filename=str(src_path))

    n_nodes = 0
    n_funcs = 0
    n_float_consts = 0
    n_banned_names = 0
    n_banned_attrs = 0
    n_banned_imports = 0

    for node in ast.walk(tree):
        n_nodes += 1
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            n_funcs += 1
        elif isinstance(node, ast.Constant):
            if type(node.value).__name__ in {"float", "complex"}:
                n_float_consts += 1
        elif isinstance(node, ast.Name):
            if node.id in BANNED_NAMES:
                n_banned_names += 1
        elif isinstance(node, ast.Attribute):
            if node.attr in BANNED_ATTRS:
                n_banned_attrs += 1
        elif isinstance(node, ast.Import):
            for alias in node.names:
                root = alias.name.split(".")[0]
                if root not in ALLOWED_IMPORT_ROOTS:
                    n_banned_imports += 1
        elif isinstance(node, ast.ImportFrom):
            mod = node.module or ""
            root = mod.split(".")[0]
            if root not in ALLOWED_IMPORT_ROOTS:
                n_banned_imports += 1

    assert n_float_consts == 0, f"AST AUDIT FAILED: {n_float_consts} float/complex literals!"
    assert n_banned_names == 0, f"AST AUDIT FAILED: {n_banned_names} banned names!"
    assert n_banned_attrs == 0, f"AST AUDIT FAILED: {n_banned_attrs} banned attributes!"
    assert n_banned_imports == 0, f"AST AUDIT FAILED: {n_banned_imports} banned imports!"

    return {
        "file": src_path.name,
        "lines": len(source.splitlines()),
        "functions": n_funcs,
        "nodes": n_nodes,
    }


def format_elapsed_ns(dt_ns):
    """Pure integer nanosecond -> 'SS.CCs' formatter (zero floats)."""
    cs_total = dt_ns // 10_000_000
    secs, cs = divmod(cs_total, 100)
    return f"{secs}.{cs:02d}s"


def ceil_fixed_str(x_mp, digits):
    """Strictly outward-rounded decimal ceiling string s with assertion iv.mpf(s).a >= x_mp."""
    ten_pow = 10 ** digits
    scale = mp.mpf(ten_pow)
    n_int = int(mp.ceil(x_mp * scale))
    for _ in range(20):
        neg = n_int < 0
        an = -n_int if neg else n_int
        q_int, r_int = divmod(an, ten_pow)
        s = ("-" if neg else "") + f"{q_int}.{r_int:0{digits}d}"
        if mp.mpf(iv.mpf(s).a) >= x_mp:
            return s
        n_int += 1
    raise AssertionError(f"ceil_fixed_str failed to bracket {x_mp}")


def floor_fixed_str(x_mp, digits):
    """Strictly outward-rounded decimal floor string s with assertion iv.mpf(s).b <= x_mp."""
    ten_pow = 10 ** digits
    scale = mp.mpf(ten_pow)
    n_int = int(mp.floor(x_mp * scale))
    for _ in range(20):
        neg = n_int < 0
        an = -n_int if neg else n_int
        q_int, r_int = divmod(an, ten_pow)
        s = ("-" if neg else "") + f"{q_int}.{r_int:0{digits}d}"
        if mp.mpf(iv.mpf(s).b) <= x_mp:
            return s
        n_int -= 1
    raise AssertionError(f"floor_fixed_str failed to bracket {x_mp}")


def ceil_sci_str(x_mp, sig_digits):
    """Strictly outward-rounded scientific ceiling string s (x_mp > 0) asserting iv.mpf(s).a >= x_mp."""
    assert x_mp > mp.mpf(0), f"ceil_sci_str requires x > 0, got {x_mp}"
    lo_lim = 10 ** (sig_digits - 1)
    hi_lim = 10 ** sig_digits
    e10 = int(mp.floor(mp.log10(x_mp)))
    m_int = int(mp.ceil(x_mp * (mp.mpf(10) ** (sig_digits - 1 - e10))))
    if m_int < lo_lim:
        e10 -= 1
        m_int = int(mp.ceil(x_mp * (mp.mpf(10) ** (sig_digits - 1 - e10))))
    for _ in range(20):
        if m_int >= hi_lim:
            m_int = (m_int + 9) // 10
            e10 += 1
        d_str = str(m_int)
        s = f"{d_str[0]}.{d_str[1:]}e{e10:+03d}" if sig_digits > 1 else f"{d_str}e{e10:+03d}"
        if mp.mpf(iv.mpf(s).a) >= x_mp:
            return s
        m_int += 1
    raise AssertionError(f"ceil_sci_str failed to bracket {x_mp}")


def floor_sci_str(x_mp, sig_digits):
    """Strictly outward-rounded scientific floor string s (x_mp > 0) asserting iv.mpf(s).b <= x_mp."""
    assert x_mp > mp.mpf(0), f"floor_sci_str requires x > 0, got {x_mp}"
    lo_lim = 10 ** (sig_digits - 1)
    hi_lim = 10 ** sig_digits
    e10 = int(mp.floor(mp.log10(x_mp)))
    m_int = int(mp.floor(x_mp * (mp.mpf(10) ** (sig_digits - 1 - e10))))
    if m_int >= hi_lim:
        e10 += 1
        m_int = int(mp.floor(x_mp * (mp.mpf(10) ** (sig_digits - 1 - e10))))
    for _ in range(20):
        if m_int < lo_lim:
            m_int = hi_lim - 1
            e10 -= 1
        d_str = str(m_int)
        s = f"{d_str[0]}.{d_str[1:]}e{e10:+03d}" if sig_digits > 1 else f"{d_str}e{e10:+03d}"
        if mp.mpf(iv.mpf(s).b) <= x_mp:
            return s
        m_int -= 1
    raise AssertionError(f"floor_sci_str failed to bracket {x_mp}")


def self_test_outward_formatters():
    """Verify outward formatters on tricky boundary values (exact powers of 10, near-carry, signs)."""
    probes = [
        mp.mpf("1e-5"),
        mp.mpf("1e-5") - mp.mpf("1e-45"),
        mp.mpf("1e-5") + mp.mpf("1e-45"),
        mp.mpf("9.999999999999999e-4"),
        mp.mpf("1.036437168069746188"),
        mp.mpf("0.000000004552016"),
    ]
    for x in probes:
        c_fix = ceil_fixed_str(x, 12)
        f_fix = floor_fixed_str(x, 12)
        c_sci = ceil_sci_str(x, 4)
        f_sci = floor_sci_str(x, 4)
        assert mp.mpf(iv.mpf(c_fix).a) >= x
        assert mp.mpf(iv.mpf(f_fix).b) <= x
        assert mp.mpf(iv.mpf(c_sci).a) >= x
        assert mp.mpf(iv.mpf(f_sci).b) <= x
    # Also test negative numbers on fixed formatters
    xn = -mp.mpf("0.1234567890123456")
    assert mp.mpf(iv.mpf(ceil_fixed_str(xn, 8)).a) >= xn
    assert mp.mpf(iv.mpf(floor_fixed_str(xn, 8)).b) <= xn


# ==============================================================================
# CERTIFIED ANCHOR TABLES (V7, V6, PRIOR) — EXACT STRINGS / RATIONALS ONLY
# ==============================================================================

INTERIOR_KEYS_BY_ASCENDING_T = ["5/3", "3/2", "4/3", "5/4", "6/5"]

EXPONENT_META = {
    # key: (p_num, p_den, k_num, k_den)
    "6/5": (6, 5, 3, 1),
    "5/4": (5, 4, 5, 2),
    "4/3": (4, 3, 2, 1),
    "3/2": (3, 2, 3, 2),
    "5/3": (5, 3, 5, 4),
}

# Version 6 baseline Lam_cert upper bounds (rigorous_iv_global_interpolation.py):
V6_LAM_UB = {
    "6/5": {2: "33.4505",  3: "34.5515",  4: "35.4668"},
    "5/4": {2: "16.9073",  3: "17.5995",  4: "18.1790"},
    "4/3": {2: "8.60430",  3: "9.06945",  4: "9.46060"},
    "3/2": {2: "4.453377", 3: "4.806190", 4: "5.105198"},
    "5/3": {2: "3.251598", 3: "3.580802", 4: "3.859845"},
}

# Version 6 certified multi-matrix lower bounds:
V6_MULTI_LB = {
    "6/5": {2: "1.007397668918", 3: "1.012830139513", 4: "1.017237089278"},
    "5/4": {2: "1.011065979791", 3: "1.019193263924", 4: "1.025787707117"},
    "4/3": {2: "1.018371575517", 3: "1.031863848072", 4: "1.042812616134"},
    "3/2": {2: "1.036437168065", 3: "1.063114500990", 4: "1.084719139101"},
    "5/3": {2: "1.057348913859", 3: "1.098935623593", 4: "1.132421930734"},
}

# Version 7 upgraded upper bounds:
# Each entry is ("lam", Lam_cert_str, provenance, ref_C_ub_str_or_None)
#            or ("C",   C_ub_str,     provenance, None)
V7_UB_SPEC = {
    "6/5": {
        2: ("lam", "33.4488",   "#139 J2_AFF", "1.007407300775"),
        3: ("lam", "34.5515",   "v6 multi_p",  None),
        4: ("lam", "35.4668",   "v6 multi_p",  None),
    },
    "5/4": {
        2: ("lam", "16.9064",   "#139 deg-8C", "1.011081656922"),
        3: ("lam", "17.5981",   "#139 deg-8C", "1.019222869118"),
        4: ("lam", "18.1761",   "#139 deg-8C", "1.025831767914"),
    },
    "4/3": {
        2: ("C",   "1.018371580069016", "#114 Mod4 twin", None),
        3: ("lam", "9.06945",           "v6 proof_p43",   None),
        4: ("lam", "9.46060",           "v6 proof_p43",   None),
    },
    "3/2": {
        2: ("C",   "1.036437168069746188", "#114 Mod3 1-sq", None),
        3: ("C",   "1.063114500999623563", "#114 Mod3 1-sq", None),
        4: ("C",   "1.084719139290543319", "#114 Mod3 1-sq", None),
    },
    "5/3": {
        2: ("lam", "3.2515544", "#179 ABC-8C5C", "1.057349130150"),
        3: ("lam", "3.5807660", "#179 ABC-8C5C", "1.098935945383"),
        4: ("lam", "3.8598120", "#179 ABC-8C5C", "1.132422431322"),
    },
}

# Version 7 certified multi-matrix lower bounds (strictly outward-rounded downward floors):
V7_MULTI_LB = {
    "6/5": {2: "1.007397668918",       3: "1.012830139513",       4: "1.017237089278"},
    "5/4": {2: "1.011065979791",       3: "1.019193263924",       4: "1.025787707117"},
    "4/3": {2: "1.018371575517",       3: "1.031863848072",       4: "1.042812616134"},
    "3/2": {2: "1.036437168069726187", 3: "1.063114500999618562", 4: "1.084719139290542318"},
    "5/3": {2: "1.057348913859",       3: "1.098935623593",       4: "1.132421930734"},
}

HOLDEN_P43_M2_UB = "1.01854047"


# ==============================================================================
# CORE PURE mpmath.iv EVALUATION HELPERS
# ==============================================================================

def iv_from_dec_str(dec_str):
    """Exact decimal string -> outward-rounded rational mpmath.iv interval (zero floats)."""
    s = dec_str.strip()
    neg = s.startswith("-")
    if neg or s.startswith("+"):
        s = s[1:]
    if "." in s:
        whole, frac = s.split(".", 1)
        num = int(whole + frac)
        den = 10 ** len(frac)
    else:
        num = int(s)
        den = 1
    if neg:
        num = -num
    return iv.mpf(num) / iv.mpf(den)


def format_exact_dec_pad(dec_str, digits):
    """Pad an exact certified decimal string with trailing zeros to `digits` decimals."""
    whole, frac = dec_str.split(".", 1)
    assert len(frac) <= digits, f"Cannot pad {dec_str} to fewer digits ({digits})"
    return f"{whole}.{frac}{'0' * (digits - len(frac))}"


def iv_C2(m):
    """Exact C_2(m) = sqrt((1 + sqrt(m))/2) in mpmath.iv."""
    return iv.sqrt((iv.mpf(1) + iv.sqrt(iv.mpf(m))) / iv.mpf(2))


def iv_C_from_Lam(Lam_str, k_num, k_den):
    """Exact C = (Lam / 2^{2k - 1})^{1/(2k)} in mpmath.iv."""
    k_iv = iv.mpf(k_num) / iv.mpf(k_den)
    two_k = iv.mpf(2) * k_iv
    return (iv_from_dec_str(Lam_str) / (iv.mpf(2) ** (two_k - iv.mpf(1)))) ** (iv.mpf(1) / two_k)


def iv_C_hadamard_t(t_iv, m):
    """Classical {1, 2} Hadamard interpolation bound C_Had(1/t, m) = C_2(m)^{2(1 - t)}."""
    return iv.exp(iv.mpf(2) * (iv.mpf(1) - t_iv) * iv.log(iv_C2(m)))


def build_anchors_in_t(m, mode="v7"):
    """
    Build anchors sorted by strictly ascending t = 1/p in [1/2, 1]:
      [(label, t_iv, p_iv, U_iv), ...]
    mode in {"v7", "v6", "prior", "hadamard"}:
      - "v7":       Version 7 upgraded 7-anchor envelope
      - "v6":       Version 6 baseline 7-anchor envelope
      - "prior":    Holden {1, 4/3 <= 1.01854047, 2} for m=2; Classical {1, 2} for m=3,4
      - "hadamard": Classical {1, 2} for all m
    """
    C2_iv = iv_C2(m)
    t_half = iv.mpf(1) / iv.mpf(2)
    one_iv = iv.mpf(1)

    if mode == "hadamard":
        return [("2", t_half, iv.mpf(2), C2_iv), ("1", one_iv, one_iv, one_iv)]

    if mode == "prior":
        anchors = [("2", t_half, iv.mpf(2), C2_iv)]
        if m == 2:
            anchors.append(("4/3", iv.mpf(3) / iv.mpf(4), iv.mpf(4) / iv.mpf(3), iv_from_dec_str(HOLDEN_P43_M2_UB)))
        anchors.append(("1", one_iv, one_iv, one_iv))
        return anchors

    anchors = [("2", t_half, iv.mpf(2), C2_iv)]
    for key in INTERIOR_KEYS_BY_ASCENDING_T:
        pn, pd, kn, kd = EXPONENT_META[key]
        t_iv = iv.mpf(pd) / iv.mpf(pn)
        p_iv = iv.mpf(pn) / iv.mpf(pd)
        if mode == "v6":
            U_iv = iv_C_from_Lam(V6_LAM_UB[key][m], kn, kd)
        elif mode == "v7":
            kind, val_str, _, ref_str = V7_UB_SPEC[key][m]
            if kind == "lam":
                U_iv = iv_C_from_Lam(val_str, kn, kd)
                if ref_str is not None:
                    # Cross-assert that Lam_cert reproduces Table 1's displayed C_UB ceiling!
                    assert mp.mpf(U_iv.b) <= mp.mpf(iv_from_dec_str(ref_str).a), (
                        f"Cross-check failed for p={key}, m={m}: U_iv.b={U_iv.b} > ref={ref_str}"
                    )
            elif kind == "C":
                U_iv = iv_from_dec_str(val_str)
            else:
                raise AssertionError(f"Unknown anchor kind {kind}")
        else:
            raise AssertionError(f"Unknown anchor mode {mode}")
        anchors.append((key, t_iv, p_iv, U_iv))
    anchors.append(("1", one_iv, one_iv, one_iv))
    return anchors


def iv_log_interp_on_segment(t_iv, t0_iv, U0_iv, t1_iv, U1_iv):
    """
    Outward-rounded mpmath.iv enclosure of log-linear interpolation in t = 1/p on [t0, t1]:
      log U(t) = (1 - theta) log U0 + theta log U1,   theta = (t - t0) / (t1 - t0) in [0, 1].
    Strictly asserts theta in [0, 1] with ZERO clamping!
    """
    theta = (t_iv - t0_iv) / (t1_iv - t0_iv)
    assert mp.mpf(theta.a) >= mp.mpf(0) and mp.mpf(theta.b) <= mp.mpf(1), (
        f"theta={theta} outside [0, 1]!"
    )
    return (iv.mpf(1) - theta) * iv.log(U0_iv) + theta * iv.log(U1_iv)


def iv_eval_envelope_t(t_iv, anchors):
    """
    Evaluate piecewise log-linear upper-bound envelope at t_iv.
    Returns U_iv enclosing U(1/t) for ALL t in t_iv.
    """
    for _, ti, _, Ui in anchors:
        if mp.mpf(ti.a) <= mp.mpf(t_iv.a) and mp.mpf(t_iv.b) <= mp.mpf(ti.b):
            return Ui
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
    ANY a > b > 0, and ANY x > 1 (ZERO 1/(2-p) singularity and ZERO x^{p b} wrapping):
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
    100% pure zero-float mpmath.iv lower bound valid for EVERY t in [t_lo, t_hi].
    Selects optimal (a, b, x) at t_mid in pure mpmath, then rigorously evaluates the
    exact fixed-(a, b, x) explicit m x m matrix formula over p_box = 1 / [t_lo, t_hi].
    """
    t_box = iv.mpf([t_lo, t_hi])
    p_box = iv.mpf(1) / t_box
    t_mid = (t_lo + t_hi) / 2
    p_mid = mp.mpf(1) / t_mid

    if t_lo >= mp.mpf("0.995"):
        return mp.mpf(1)

    if t_hi <= mp.mpf("0.51"):
        a_iv = iv.mpf(120)
        b_iv = iv.mpf(1)
        x_iv = iv.mpf(1) + iv.sqrt(iv.mpf(m))
        return max(mp.mpf(1), iv_matrix_lb_fixed_ab(p_box, m, a_iv, b_iv, x_iv))

    s_m = p_mid / (mp.mpf(2) - p_mid)
    inv_p_m = mp.mpf(1) / p_mid
    half_m = mp.mpf(1) / mp.mpf(2)
    m1_m = mp.mpf(m - 1)

    def f_pt(u):
        ex = mp.exp(u)
        return (
            ((mp.exp(s_m * u) + m1_m) ** (inv_p_m - half_m))
            * mp.sqrt(ex + m1_m)
            / ((mp.exp(p_mid * u) + m1_m) ** inv_p_m)
        )

    lo_u = mp.mpf("0.01")
    hi_u = mp.mpf("10.0")
    gr = (mp.sqrt(mp.mpf(5)) - mp.mpf(1)) / mp.mpf(2)
    for _ in range(70):
        c = hi_u - gr * (hi_u - lo_u)
        d = lo_u + gr * (hi_u - lo_u)
        if f_pt(c) > f_pt(d):
            hi_u = d
        else:
            lo_u = c
    x_opt = iv.mpf(mp.exp((lo_u + hi_u) / 2))
    a_opt = iv.mpf(s_m)
    b_opt = iv.mpf(1)
    lb = iv_matrix_lb_fixed_ab(p_box, m, a_opt, b_opt, x_opt)
    return max(mp.mpf(1), lb)


# ==============================================================================
# PURE ZERO-FLOAT mpmath.iv EVALUATOR FOR `#143` THEOREM 1(a)-(b) C_4L(p, m)
# ==============================================================================

def iv_g_4L(t_iv, x_iv):
    """
    Evaluate g_kappa(x) = (1 + x)^{2k - 3} (x^3 - 1) in terms of t = 1/p in [1/2, 2/3],
    where 2k - 3 = (3t - 2) / (1 - t) in [-1, 0] (smooth up to t = 1/2!).
    """
    exp_iv = (iv.mpf(3) * t_iv - iv.mpf(2)) / (iv.mpf(1) - t_iv)
    return iv.exp(exp_iv * iv.log(iv.mpf(1) + x_iv)) * ((x_iv ** 3) - iv.mpf(1))


def mp_solve_x_4L_point(t_mp, m):
    """Pure 55-dps mpmath Newton solver for unique root x > 1 of g(t, x) = m - 1."""
    exp_mp = (mp.mpf(3) * t_mp - mp.mpf(2)) / (mp.mpf(1) - t_mp)
    tgt = mp.mpf(m - 1)
    x = mp.mpf(m) ** (mp.mpf(1) / mp.mpf(3)) + mp.mpf("0.1")
    ten_m42 = mp.mpf(10) ** (-42)
    for _ in range(60):
        opx = mp.mpf(1) + x
        x3m1 = (x ** 3) - mp.mpf(1)
        pref = opx ** exp_mp
        fx = pref * x3m1 - tgt
        if abs(fx) < ten_m42:
            break
        dfx = pref * (exp_mp * x3m1 / opx + mp.mpf(3) * (x ** 2))
        step = fx / dfx
        cand = x - step
        while cand <= mp.mpf(1):
            step = step / mp.mpf(2)
            cand = x - step
        x = cand
        if abs(step) < ten_m42:
            break
    return x


def iv_x_4L_on_tbox(t_lo_mp, t_hi_mp, m):
    """
    Rigorous zero-float mpmath.iv enclosure [x_lo, x_hi] of the unique root x_4L(t, m)
    for ALL t in [t_lo_mp, t_hi_mp] subset [1/2, 2/3].
    Uses exact strict monotonicity:
      - g(t, x) is strictly increasing in x > 1 (since 2k x^3 + 3x^2 + (3 - 2k) > 0),
      - g(t, x) is strictly increasing in t in [1/2, 2/3] (since d/dt((3t-2)/(1-t)) = 1/(1-t)^2 > 0
        and log(1 + x) > 0).
    Therefore any x_lo, x_hi > 1 satisfying:
      g(t_hi, x_lo).b < m - 1  AND  g(t_lo, x_hi).a > m - 1
    certifies g(t, x_lo) <= g(t_hi, x_lo) < m - 1 < g(t_lo, x_hi) <= g(t, x_hi),
    hence x_4L(t, m) in (x_lo, x_hi) for EVERY t in [t_lo_mp, t_hi_mp]!
    """
    tgt = mp.mpf(m - 1)
    x_small_est = mp_solve_x_4L_point(t_hi_mp, m)
    x_large_est = mp_solve_x_4L_point(t_lo_mp, m)
    t_lo_iv = iv.mpf(t_lo_mp)
    t_hi_iv = iv.mpf(t_hi_mp)

    eps = mp.mpf(10) ** (-28)
    x_lo = None
    for _ in range(40):
        cand = x_small_est - eps
        if cand > mp.mpf(1):
            val = iv_g_4L(t_hi_iv, iv.mpf(cand))
            if mp.mpf(val.b) < tgt:
                x_lo = cand
                break
        eps = eps * mp.mpf(4)
    assert x_lo is not None, f"Failed to certify lower bracket for x_4L at t_hi={t_hi_mp}, m={m}"

    eps = mp.mpf(10) ** (-28)
    x_hi = None
    for _ in range(40):
        cand = x_large_est + eps
        val = iv_g_4L(t_lo_iv, iv.mpf(cand))
        if mp.mpf(val.a) > tgt:
            x_hi = cand
            break
        eps = eps * mp.mpf(4)
    assert x_hi is not None, f"Failed to certify upper bracket for x_4L at t_lo={t_lo_mp}, m={m}"
    assert mp.mpf(1) < x_lo < x_hi
    return iv.mpf([x_lo, x_hi])


def iv_C_4L_part_b_t(t_iv, m):
    """
    Exact closed-form Part (b) bound on p in [6/5, 3/2] (t = 1/p in [2/3, 5/6]):
      log C_4L(1/t, m) = (1/6) log(m) + t log((1 + m^{1/3}) / (2 m^{1/3})).
    """
    m_iv = iv.mpf(m)
    m_cbrt = iv.exp(iv.log(m_iv) / iv.mpf(3))
    log_c = (iv.log(m_iv) / iv.mpf(6)) + t_iv * iv.log((iv.mpf(1) + m_cbrt) / (iv.mpf(2) * m_cbrt))
    return iv.exp(log_c)


def iv_C_4L_part_a_tbox(t_lo_mp, t_hi_mp, m):
    """
    Rigorous zero-float mpmath.iv enclosure of Part (a) C_4L(1/t, m) over ALL
    t in [t_lo_mp, t_hi_mp] subset [1/2, 2/3]:
      log C_4L(1/t, m) = t log((1 + x_4L)/2) - (t - 1/2) log(x_4L).
    """
    t_box = iv.mpf([t_lo_mp, t_hi_mp])
    x_box = iv_x_4L_on_tbox(t_lo_mp, t_hi_mp, m)
    half = iv.mpf(1) / iv.mpf(2)
    log_c = t_box * iv.log((iv.mpf(1) + x_box) * half) - (t_box - half) * iv.log(x_box)
    return iv.exp(log_c)


def iv_C_4L_at_t(t_iv, m):
    """
    Rigorous mpmath.iv enclosure of `#143` Theorem 1(a)-(b) C_4L(1/t, m) at any point
    interval t_iv subset [1/2, 5/6] (p in [6/5, 2]).
    """
    t_two_thirds = iv.mpf(2) / iv.mpf(3)
    if mp.mpf(t_iv.a) >= mp.mpf(t_two_thirds.a):
        return iv_C_4L_part_b_t(t_iv, m)
    if mp.mpf(t_iv.b) <= mp.mpf(t_two_thirds.b):
        return iv_C_4L_part_a_tbox(mp.mpf(t_iv.a), mp.mpf(t_iv.b), m)
    # Exact boundary p = 3/2 (t = 2/3): Part (a) and Part (b) coincide identically!
    c_a = iv_C_4L_part_a_tbox(mp.mpf(t_iv.a), mp.mpf(t_two_thirds.b), m)
    c_b = iv_C_4L_part_b_t(t_iv, m)
    return iv.mpf([min(mp.mpf(c_a.a), mp.mpf(c_b.a)), max(mp.mpf(c_a.b), mp.mpf(c_b.b))])


# ==============================================================================
# ANCHOR SUMMARY LEDGER (FULL PRECISION AUDIT OF ALL 7 V7 ANCHORS VS V6)
# ==============================================================================

def print_anchor_upgrade_summary(m):
    anc_v7 = build_anchors_in_t(m, mode="v7")
    anc_v6 = build_anchors_in_t(m, mode="v6")
    print(f"\n[V7 ANCHOR LEDGER | m = {m}] UPGRADED ZERO-FLOAT ANCHORS VS V6:")
    print(
        f"  {'p':>4s} | {'Provenance':<15s} | {'V7 Cert LB (floor)':>20s} | "
        f"{'V7 Cert UB (ceil)':>20s} | {'V7 Gap <=':>10s} | {'V6 Gap <=':>10s} | {'Gain >=':>10s}"
    )
    print("  " + "-" * 107)
    for idx in range(1, len(anc_v7) - 1):
        key = anc_v7[idx][0]
        U7 = anc_v7[idx][3]
        U6 = anc_v6[idx][3]
        kind, val_str, prov, _ = V7_UB_SPEC[key][m]
        lb7_iv = iv_from_dec_str(V7_MULTI_LB[key][m])
        lb6_iv = iv_from_dec_str(V6_MULTI_LB[key][m])
        assert mp.mpf(lb7_iv.b) < mp.mpf(U7.a) <= mp.mpf(U7.b), f"V7 LB >= UB at p={key}, m={m}!"
        assert mp.mpf(lb6_iv.b) < mp.mpf(U6.a) <= mp.mpf(U6.b), f"V6 LB >= UB at p={key}, m={m}!"

        digs = 18 if key == "3/2" else (15 if (key == "4/3" and m == 2) else 12)
        lb7_s = format_exact_dec_pad(V7_MULTI_LB[key][m], digs)
        ub7_s = format_exact_dec_pad(val_str, digs) if kind == "C" else ceil_fixed_str(mp.mpf(U7.b), digs)

        # Guarantee displayed subtraction ub7_s - lb7_s AND true interval U7 - lb7_iv are BOTH <= g7_s!
        gap7_true_hi = mp.mpf((U7 - lb7_iv).b)
        gap7_disp_hi = mp.mpf((iv_from_dec_str(ub7_s) - iv_from_dec_str(lb7_s)).b)
        gap7_hi = max(gap7_true_hi, gap7_disp_hi)
        gap6_hi = mp.mpf((U6 - lb6_iv).b)
        gap6_lo = mp.mpf((U6 - lb6_iv).a)

        g7_s = ceil_sci_str(gap7_hi, 4)
        g6_s = ceil_sci_str(gap6_hi, 4)
        assert mp.mpf((iv.mpf(ub7_s) - iv.mpf(lb7_s)).b) <= mp.mpf(iv.mpf(g7_s).a), (
            f"Displayed gap inconsistency at p={key}, m={m}: {ub7_s} - {lb7_s} > {g7_s}"
        )

        if mp.mpf(U7.b) < mp.mpf(U6.a):
            gain_lo = mp.mpf((iv.mpf(gap6_lo) / iv.mpf(gap7_hi)).a)
            gain_s = f"{floor_sci_str(gain_lo, 3)}x" if gain_lo >= mp.mpf(1000) else f"{floor_fixed_str(gain_lo, 2)}x"
        else:
            assert U7 == U6, f"Expected exact match where V7 did not beat V6 at p={key}, m={m}"
            gain_s = "1.00x (v6)"
        print(
            f"  {key:>4s} | {prov:<15s} | {lb7_s:>20s} | {ub7_s:>20s} | "
            f"{g7_s:>10s} | {g6_s:>10s} | {gain_s:>10s}"
        )


# ==============================================================================
# THEOREM G1: STRICT LOG-CONVEXITY OF ALL 7 V7 ANCHORS (0 REDUNDANT ANCHORS!)
# ==============================================================================

def certify_theorem_G1(m):
    anchors = build_anchors_in_t(m, mode="v7")
    slopes = []
    for i in range(len(anchors) - 1):
        lbl0, t0, _, U0 = anchors[i]
        lbl1, t1, _, U1 = anchors[i + 1]
        s_iv = (iv.log(U1) - iv.log(U0)) / (t1 - t0)
        assert mp.mpf(s_iv.b) < mp.mpf(0), f"Slope not negative on [{lbl0}, {lbl1}]!"
        slopes.append((lbl0, lbl1, s_iv))

    min_jump = None
    for i in range(len(slopes) - 1):
        jump = mp.mpf((slopes[i + 1][2] - slopes[i][2]).a)
        assert jump > mp.mpf(0), f"Convexity failed at anchor {anchors[i + 1][0]}: jump={jump}"
        if min_jump is None or jump < min_jump:
            min_jump = jump

    print(
        f"\n[THEOREM G1 PASS | m = {m}] ALL 7 V7 ANCHORS STRICTLY LOG-CONVEX IN t = 1/p "
        f"(min slope jump >= +{floor_sci_str(min_jump, 4)})!"
    )
    for i in range(1, len(anchors) - 1):
        lbl, ti, _, Ui = anchors[i]
        pn, pd, _, _ = EXPONENT_META[lbl]
        t_prev, U_prev = anchors[i - 1][1], anchors[i - 1][3]
        t_next, U_next = anchors[i + 1][1], anchors[i + 1][3]
        U_nbr = iv.exp(iv_log_interp_on_segment(ti, t_prev, U_prev, t_next, U_next))
        improv = mp.mpf((U_nbr - Ui).a)
        assert improv > mp.mpf(0), f"Anchor p={lbl} did not beat neighbor interpolation!"
        u7_s = ceil_fixed_str(mp.mpf(Ui.b), 12)
        unbr_s = floor_fixed_str(mp.mpf(U_nbr.a), 12)
        imp_s = floor_sci_str(improv, 4)
        assert mp.mpf((iv.mpf(unbr_s) - iv.mpf(u7_s)).a) >= mp.mpf(iv.mpf(imp_s).b)
        print(
            f"    p = {lbl:3s} (t={pd}/{pn}): "
            f"U_V7 <= {u7_s}  vs neighbor-secant >= {unbr_s}  "
            f"(beats by >= +{imp_s})"
        )
    return min_jump


# ==============================================================================
# THEOREM G2: GLOBAL DOMINANCE OVER BOTH HOLDEN/PRIOR AND VERSION 6 ENVELOPE!
# ==============================================================================

def certify_theorem_G2(m):
    anc_v7 = build_anchors_in_t(m, mode="v7")
    anc_v6 = build_anchors_in_t(m, mode="v6")
    anc_pri = build_anchors_in_t(m, mode="prior")

    # --- G2a: V7 vs Holden / Classical Prior ---
    prior_desc = "Holden {1, 4/3<=1.01854047, 2}" if m == 2 else "Classical Hadamard {1, 2}"
    print(f"\n[THEOREM G2a PASS | m = {m}] STRICT GLOBAL DOMINANCE OF V7 OVER {prior_desc} ON ALL REAL p in (1, 2):")

    best_abs = mp.mpf(0)
    best_abs_p = ""
    best_rel = mp.mpf(0)
    best_rel_p = ""
    for i in range(1, len(anc_v7) - 1):
        lbl, ti, _, U_v7 = anc_v7[i]
        U_pri = iv_eval_envelope_t(ti, anc_pri)
        log_diff = iv.log(U_pri) - iv.log(U_v7)
        assert mp.mpf(log_diff.a) > mp.mpf(0), f"Prior dominance failed at p={lbl}!"
        abs_drop = mp.mpf((U_pri - U_v7).a)
        rel_exc_red = mp.mpf(((U_pri - U_v7) / (U_pri - iv.mpf(1))).a) * mp.mpf(100)
        assert abs_drop > mp.mpf(0) and rel_exc_red > mp.mpf(0)
        if abs_drop > best_abs:
            best_abs = abs_drop
            best_abs_p = lbl
        if rel_exc_red > best_rel:
            best_rel = rel_exc_red
            best_rel_p = lbl
        u7_s = ceil_fixed_str(mp.mpf(U_v7.b), 12)
        up_s = (
            format_exact_dec_pad(HOLDEN_P43_M2_UB, 12)
            if (m == 2 and lbl == "4/3")
            else floor_fixed_str(mp.mpf(U_pri.a), 12)
        )
        drop_s = floor_sci_str(abs_drop, 4)
        assert mp.mpf((iv.mpf(up_s) - iv.mpf(u7_s)).a) >= mp.mpf(iv.mpf(drop_s).b)
        print(
            f"    p = {lbl:3s}: U_V7 <= {u7_s}  <  "
            f"U_prior >= {up_s}  "
            f"| drop >= {drop_s}  (>= {floor_fixed_str(rel_exc_red, 2)}% of prior excess)"
        )
    print(
        f"    ==> By piecewise log-linearity in t = 1/p, U_V7(p; {m}) < U_prior(p; {m}) "
        f"STRICTLY for EVERY real p in (1, 2)!"
    )
    print(
        f"    ==> Peak anchor drop at p={best_abs_p}: >= {floor_sci_str(best_abs, 4)} | "
        f"Peak excess reduction at p={best_rel_p}: >= {floor_fixed_str(best_rel, 2)}%"
    )

    # --- G2b: V7 vs Version 6 Global Envelope ---
    strict_anchors = []
    tied_anchors = []
    print(f"\n[THEOREM G2b PASS | m = {m}] GLOBAL DOMINANCE OF V7 OVER VERSION 6 ENVELOPE:")
    for i in range(1, len(anc_v7) - 1):
        lbl, ti, _, U_v7 = anc_v7[i]
        U_v6 = anc_v6[i][3]
        if mp.mpf(U_v7.b) < mp.mpf(U_v6.a):
            log_diff = iv.log(U_v6) - iv.log(U_v7)
            assert mp.mpf(log_diff.a) > mp.mpf(0)
            drop_lo = mp.mpf((U_v6 - U_v7).a)
            assert drop_lo > mp.mpf(0)
            strict_anchors.append(lbl)
            u7_s = ceil_fixed_str(mp.mpf(U_v7.b), 12)
            u6_s = floor_fixed_str(mp.mpf(U_v6.a), 12)
            drop_s = floor_sci_str(drop_lo, 4)
            assert mp.mpf((iv.mpf(u6_s) - iv.mpf(u7_s)).a) >= mp.mpf(iv.mpf(drop_s).b)
            print(
                f"    p = {lbl:3s}: U_V7 <= {u7_s}  <  "
                f"U_V6 >= {u6_s}  "
                f"| STRICT drop >= {drop_s}"
            )
        else:
            assert U_v7 == U_v6, f"V7 > V6 regression at p={lbl}, m={m}!"
            tied_anchors.append(lbl)
            print(
                f"    p = {lbl:3s}: U_V7 == U_V6 <= {ceil_fixed_str(mp.mpf(U_v7.b), 12)}  "
                f"| IDENTICAL (retained v6 anchor)"
            )

    if len(tied_anchors) == 0:
        assert m == 2 and len(strict_anchors) == 5
        print(
            f"    ==> ALL 5/5 interior anchors STRICTLY improved: U_V7(p; {m}) < U_V6(p; {m}) "
            f"STRICTLY for EVERY real p in (1, 2)!"
        )
    else:
        assert m in (3, 4) and set(strict_anchors) == {"5/3", "3/2", "5/4"} and set(tied_anchors) == {"4/3", "6/5"}
        print(
            f"    ==> 3/5 interior anchors STRICTLY improved ({{5/4, 3/2, 5/3}}), 2/5 retained ({{6/5, 4/3}}):"
        )
        print(
            f"        By piecewise affinity of log(U_V6/U_V7) in t = 1/p, U_V7(p; {m}) <= U_V6(p; {m}) "
            f"for ALL p in [1, 2],"
        )
        print(
            f"        with STRICT improvement U_V7(p; {m}) < U_V6(p; {m}) for EVERY real "
            f"p in (6/5, 4/3) U (4/3, 2) (and exact equality on [1, 6/5] and at p = 4/3)!"
        )


# ==============================================================================
# THEOREM G3: UNIFORM GLOBAL CONTINUUM ENCLOSURE GAP OVER ALL REAL p in [1, 2]!
# ==============================================================================

def certify_theorem_G3(m, n_sub_per_seg=100):
    anc_v7 = build_anchors_in_t(m, mode="v7")
    anc_v6 = build_anchors_in_t(m, mode="v6")
    anc_pri = build_anchors_in_t(m, mode="prior")

    # Assert exact dyadic endpoints [1/2, 1] (zero endpoint seam cracks!)
    assert mp.mpf(anc_v7[0][1].a) == mp.mpf(anc_v7[0][1].b) == mp.mpf("0.5")
    assert mp.mpf(anc_v7[-1][1].a) == mp.mpf(anc_v7[-1][1].b) == mp.mpf(1)

    # Assert strict monotonicity (decreasing in t) on every segment of BOTH V7 and V6!
    for anc in (anc_v7, anc_v6):
        for seg_i in range(len(anc) - 1):
            t0_iv, U0_iv = anc[seg_i][1], anc[seg_i][3]
            t1_iv, U1_iv = anc[seg_i + 1][1], anc[seg_i + 1][3]
            s_iv = (iv.log(U1_iv) - iv.log(U0_iv)) / (t1_iv - t0_iv)
            assert mp.mpf(s_iv.b) < mp.mpf(0), f"Segment {seg_i} not strictly decreasing in t!"

    worst_v7_gap = mp.mpf(0)
    worst_v7_loc = None
    worst_v6_gap = mp.mpf(0)
    worst_v7_gap_65 = mp.mpf(0)
    worst_v7_loc_65 = None
    worst_v6_gap_65 = mp.mpf(0)
    worst_pri_err_lb = mp.mpf(0)
    worst_pri_loc = None
    max_v6_minus_v7_lb = mp.mpf(0)
    max_v6_minus_v7_p = None

    covered_boxes = []
    for seg_i in range(len(anc_v7) - 1):
        t0_iv, U0_v7 = anc_v7[seg_i][1], anc_v7[seg_i][3]
        t1_iv, U1_v7 = anc_v7[seg_i + 1][1], anc_v7[seg_i + 1][3]
        U0_v6 = anc_v6[seg_i][3]
        U1_v6 = anc_v6[seg_i + 1][3]
        in_65_to_2 = seg_i <= 4  # segments 0..4 cover t in [1/2, 5/6] <=> p in [6/5, 2]

        tA = mp.mpf(t0_iv.b)
        tB = mp.mpf(t1_iv.a)
        assert tA < tB
        edges = [tA + (tB - tA) * k / n_sub_per_seg for k in range(n_sub_per_seg + 1)]
        edges[0] = tA
        edges[-1] = tB

        for k in range(n_sub_per_seg):
            tl = edges[k]
            th = edges[k + 1]
            U_v7_hi = mp.mpf(iv.exp(iv_log_interp_on_segment(iv.mpf(tl), t0_iv, U0_v7, t1_iv, U1_v7)).b)
            U_v6_hi = mp.mpf(iv.exp(iv_log_interp_on_segment(iv.mpf(tl), t0_iv, U0_v6, t1_iv, U1_v6)).b)
            L_box_lo = iv_opt_matrix_lb_on_tbox(tl, th, m)

            gap7_ub = mp.mpf((iv.mpf(U_v7_hi) - iv.mpf(L_box_lo)).b)
            gap6_ub = mp.mpf((iv.mpf(U_v6_hi) - iv.mpf(L_box_lo)).b)
            assert gap7_ub > mp.mpf(0), f"Impossible: L_box_lo >= U_v7_hi on [{tl}, {th}]!"
            if gap7_ub > worst_v7_gap:
                worst_v7_gap = gap7_ub
                p_lo_box = mp.mpf((iv.mpf(1) / iv.mpf(th)).a)
                p_hi_box = mp.mpf((iv.mpf(1) / iv.mpf(tl)).b)
                worst_v7_loc = (p_lo_box, p_hi_box)
            if gap6_ub > worst_v6_gap:
                worst_v6_gap = gap6_ub
            if in_65_to_2:
                if gap7_ub > worst_v7_gap_65:
                    worst_v7_gap_65 = gap7_ub
                    p_lo_box = mp.mpf((iv.mpf(1) / iv.mpf(th)).a)
                    p_hi_box = mp.mpf((iv.mpf(1) / iv.mpf(tl)).b)
                    worst_v7_loc_65 = (p_lo_box, p_hi_box)
                if gap6_ub > worst_v6_gap_65:
                    worst_v6_gap_65 = gap6_ub

            tm = (tl + th) / 2
            U_pri_lo = mp.mpf(iv_eval_envelope_t(iv.mpf(tm), anc_pri).a)
            U_v7_mid_hi = mp.mpf(iv.exp(iv_log_interp_on_segment(iv.mpf(tm), t0_iv, U0_v7, t1_iv, U1_v7)).b)
            U_v6_mid_lo = mp.mpf(iv.exp(iv_log_interp_on_segment(iv.mpf(tm), t0_iv, U0_v6, t1_iv, U1_v6)).a)
            pri_err_lb = mp.mpf((iv.mpf(U_pri_lo) - iv.mpf(U_v7_mid_hi)).a)
            if pri_err_lb > worst_pri_err_lb:
                worst_pri_err_lb = pri_err_lb
                worst_pri_loc = mp.mpf(1) / tm
            v6_drop_lb = mp.mpf((iv.mpf(U_v6_mid_lo) - iv.mpf(U_v7_mid_hi)).a)
            if v6_drop_lb > max_v6_minus_v7_lb:
                max_v6_minus_v7_lb = v6_drop_lb
                max_v6_minus_v7_p = mp.mpf(1) / tm

            covered_boxes.append((tl, th))

        # Tiny seam box [t1_iv.a, t1_iv.b] for non-dyadic rational anchors (3/5, 2/3, 4/5, 5/6)
        if mp.mpf(t1_iv.a) < mp.mpf(t1_iv.b):
            tl = mp.mpf(t1_iv.a)
            th = mp.mpf(t1_iv.b)
            t_ref = tl - (mp.mpf(10) ** (-20))
            assert mp.mpf(t0_iv.b) < t_ref < tl
            U_v7_hi = mp.mpf(iv.exp(iv_log_interp_on_segment(iv.mpf(t_ref), t0_iv, U0_v7, t1_iv, U1_v7)).b)
            U_v6_hi = mp.mpf(iv.exp(iv_log_interp_on_segment(iv.mpf(t_ref), t0_iv, U0_v6, t1_iv, U1_v6)).b)
            L_box_lo = iv_opt_matrix_lb_on_tbox(tl, th, m)
            gap7_ub = mp.mpf((iv.mpf(U_v7_hi) - iv.mpf(L_box_lo)).b)
            gap6_ub = mp.mpf((iv.mpf(U_v6_hi) - iv.mpf(L_box_lo)).b)
            assert gap7_ub > mp.mpf(0)
            if gap7_ub > worst_v7_gap:
                worst_v7_gap = gap7_ub
                p_lo_box = mp.mpf((iv.mpf(1) / iv.mpf(th)).a)
                p_hi_box = mp.mpf((iv.mpf(1) / iv.mpf(tl)).b)
                worst_v7_loc = (p_lo_box, p_hi_box)
            if gap6_ub > worst_v6_gap:
                worst_v6_gap = gap6_ub
            if in_65_to_2:
                if gap7_ub > worst_v7_gap_65:
                    worst_v7_gap_65 = gap7_ub
                    p_lo_box = mp.mpf((iv.mpf(1) / iv.mpf(th)).a)
                    p_hi_box = mp.mpf((iv.mpf(1) / iv.mpf(tl)).b)
                    worst_v7_loc_65 = (p_lo_box, p_hi_box)
                if gap6_ub > worst_v6_gap_65:
                    worst_v6_gap_65 = gap6_ub
            covered_boxes.append((tl, th))

    # Also check exact interior anchors for max pointwise V6 - V7 drop!
    for idx in range(1, len(anc_v7) - 1):
        lbl, ti, pi, U7 = anc_v7[idx]
        U6 = anc_v6[idx][3]
        if mp.mpf(U7.b) < mp.mpf(U6.a):
            d_lo = mp.mpf((U6 - U7).a)
            if d_lo > max_v6_minus_v7_lb:
                max_v6_minus_v7_lb = d_lo
                max_v6_minus_v7_p = mp.mpf(pi.mid)

    # Assert 100% exact crack-free contiguous coverage of [1/2, 1]!
    assert len(covered_boxes) == 6 * n_sub_per_seg + 4
    assert covered_boxes[0][0] == mp.mpf("0.5") and covered_boxes[-1][1] == mp.mpf(1)
    for i in range(len(covered_boxes) - 1):
        assert covered_boxes[i][1] == covered_boxes[i + 1][0], (
            f"Crack between {covered_boxes[i]} and {covered_boxes[i + 1]}!"
        )
    if m == 2:
        assert worst_v7_gap < worst_v6_gap
    else:
        assert worst_v7_gap <= worst_v6_gap
    assert worst_v7_gap_65 < worst_v6_gap_65

    ratio_lb = mp.mpf((iv.mpf(worst_pri_err_lb) / iv.mpf(worst_v7_gap)).a)
    print(
        f"\n[THEOREM G3 PASS | m = {m}] CONTINUUM COVERAGE OF ALL p in [1, 2] "
        f"({len(covered_boxes)} contiguous iv-boxes, 0 cracks):"
    )
    print(
        f"    CERTIFIED V7 UNIFORM GAP [1, 2]:   sup_{{p in [1,2]}} (U_V7(p; {m}) - C_p({m})) <= {ceil_sci_str(worst_v7_gap, 5)} "
        f"(worst box p in [{floor_fixed_str(worst_v7_loc[0], 4)}, {ceil_fixed_str(worst_v7_loc[1], 4)}])"
    )
    print(
        f"    CERTIFIED V7 UNIFORM GAP [6/5, 2]: sup_{{p in [6/5,2]}} (U_V7 - C_p) <= {ceil_sci_str(worst_v7_gap_65, 5)} "
        f"< V6 ({ceil_sci_str(worst_v6_gap_65, 5)}) (worst p in [{floor_fixed_str(worst_v7_loc_65[0], 4)}, {ceil_fixed_str(worst_v7_loc_65[1], 4)}])"
    )
    print(
        f"    V6 BASELINE UNIFORM GAP [1, 2]:    sup_{{p in [1,2]}} (U_V6(p; {m}) - C_p({m})) <= {ceil_sci_str(worst_v6_gap, 5)} "
        f"| max pointwise V6->V7 drop >= {floor_sci_str(max_v6_minus_v7_lb, 4)} (at p={floor_fixed_str(max_v6_minus_v7_p, 4)})"
    )
    print(
        f"    vs PRIOR CURVE ERROR:              sup_{{p in [1,2]}} (U_prior(p; {m}) - C_p({m})) >= {floor_sci_str(worst_pri_err_lb, 5)} "
        f"(at p={floor_fixed_str(worst_pri_loc, 4)})  ==>  >= {floor_fixed_str(ratio_lb, 2)}x GLOBAL GAP REDUCTION!"
    )
    return worst_v7_gap, worst_v6_gap, worst_pri_err_lb


# ==============================================================================
# THEOREM G4: CERTIFIED TWO-SIDED ENCLOSURE TABLE AT 17 EXPONENTS ACROSS (1, 2)
# ==============================================================================

def make_test_exponents_G4():
    """Returns 17 rational & irrational exponents across (1, 2) as (label, p_iv, t_iv)."""
    specs = [
        ("1.05",    ("rat", 21, 20)),
        ("1.10",    ("rat", 11, 10)),
        ("1.15",    ("rat", 23, 20)),
        ("6/5",     ("rat",  6,  5)),
        ("5/4",     ("rat",  5,  4)),
        ("1.30",    ("rat", 13, 10)),
        ("4/3",     ("rat",  4,  3)),
        ("7/5",     ("rat",  7,  5)),
        ("sqrt(2)", ("sqrt2",)),
        ("3/2",     ("rat",  3,  2)),
        ("1.60",    ("rat",  8,  5)),
        ("phi",     ("phi",)),
        ("5/3",     ("rat",  5,  3)),
        ("7/4",     ("rat",  7,  4)),
        ("1.80",    ("rat",  9,  5)),
        ("1.90",    ("rat", 19, 10)),
        ("1.95",    ("rat", 39, 20)),
    ]
    out = []
    for lbl, spec in specs:
        if spec[0] == "rat":
            pn, pd = spec[1], spec[2]
            p_iv = iv.mpf(pn) / iv.mpf(pd)
            t_iv = iv.mpf(pd) / iv.mpf(pn)
        elif spec[0] == "sqrt2":
            p_iv = iv.sqrt(iv.mpf(2))
            t_iv = iv.mpf(1) / p_iv
        elif spec[0] == "phi":
            p_iv = (iv.mpf(1) + iv.sqrt(iv.mpf(5))) / iv.mpf(2)
            t_iv = iv.mpf(1) / p_iv
        else:
            raise AssertionError(f"Unknown spec {spec}")
        out.append((lbl, p_iv, t_iv))
    return out


def certify_table_G4(m):
    anc_v7 = build_anchors_in_t(m, mode="v7")
    anc_v6 = build_anchors_in_t(m, mode="v6")
    anc_pri = build_anchors_in_t(m, mode="prior")
    pts = make_test_exponents_G4()

    print(f"\n[THEOREM G4 | m = {m}] CERTIFIED TWO-SIDED ENCLOSURES AT 17 EXPONENTS ACROSS (1, 2) (ALL n >= 1):")
    print(
        f"  {'p':>8s} | {'Cert LB (flr)':>15s} | {'V7 UB (ceil)':>15s} | "
        f"{'Prior (flr)':>15s} | {'Gap <=':>10s} | {'vs Prior >=':>11s} | {'vs V6':>11s}"
    )
    print("  " + "-" * 102)
    for lbl, _, t_iv in pts:
        U7_iv = iv_eval_envelope_t(t_iv, anc_v7)
        U6_iv = iv_eval_envelope_t(t_iv, anc_v6)
        Up_iv = iv_eval_envelope_t(t_iv, anc_pri)
        U7_hi = mp.mpf(U7_iv.b)
        U6_lo = mp.mpf(U6_iv.a)
        Up_lo = mp.mpf(Up_iv.a)

        if lbl in V7_MULTI_LB:
            lb_str_raw = V7_MULTI_LB[lbl][m]
            LB_lo = mp.mpf(iv_from_dec_str(lb_str_raw).a)
            lb_s = lb_str_raw if len(lb_str_raw.split(".", 1)[1]) == 12 else floor_fixed_str(LB_lo, 12)
        else:
            LB_lo = iv_opt_matrix_lb_on_tbox(mp.mpf(t_iv.a), mp.mpf(t_iv.b), m)
            lb_s = floor_fixed_str(LB_lo, 12)

        assert LB_lo < U7_hi < Up_lo, f"Ordering failed at p={lbl}, m={m}!"
        gap_hi = mp.mpf((iv.mpf(U7_hi) - iv.mpf(LB_lo)).b)
        drop_pri_lo = mp.mpf((iv.mpf(Up_lo) - iv.mpf(U7_hi)).a)
        assert gap_hi > mp.mpf(0) and drop_pri_lo > mp.mpf(0)

        u7_s = ceil_fixed_str(U7_hi, 12)
        up_s = (
            format_exact_dec_pad(HOLDEN_P43_M2_UB, 12)
            if (m == 2 and lbl == "4/3")
            else floor_fixed_str(Up_lo, 12)
        )
        gap_s = ceil_sci_str(gap_hi, 3)
        drop_pri_s = floor_sci_str(drop_pri_lo, 3)

        # Assert displayed-column consistency on all rows whose gap exceeds 12-digit column resolution!
        if not (lbl == "3/2" or (lbl == "4/3" and m == 2)):
            assert mp.mpf((iv.mpf(u7_s) - iv.mpf(lb_s)).b) <= mp.mpf(iv.mpf(gap_s).a), (
                f"G4 displayed gap mismatch at p={lbl}, m={m}: {u7_s} - {lb_s} > {gap_s}"
            )
        assert mp.mpf((iv.mpf(up_s) - iv.mpf(u7_s)).a) >= mp.mpf(iv.mpf(drop_pri_s).b)

        if U7_hi < U6_lo:
            drop_v6_lo = mp.mpf((iv.mpf(U6_lo) - iv.mpf(U7_hi)).a)
            assert drop_v6_lo > mp.mpf(0)
            v6_col = f"-{floor_sci_str(drop_v6_lo, 3)}"
        else:
            # Verify this occurs ONLY on the retained region ([1, 6/5] or p=4/3 for m=3,4)
            assert m in (3, 4) and lbl in {"1.05", "1.10", "1.15", "6/5", "4/3"}, (
                f"Unexpected non-strict V7 vs V6 at p={lbl}, m={m}!"
            )
            assert U7_iv == U6_iv
            v6_col = "= V6"

        tag = "*" if lbl in V7_MULTI_LB else " "
        print(
            f"  {lbl:>7s}{tag} | {lb_s:>15s} | {u7_s:>15s} | "
            f"{up_s:>15s} | {gap_s:>10s} | "
            f"-{drop_pri_s:>10s} | {v6_col:>11s}"
        )
    print(
        "  (* Certified multi-matrix anchor; full 18-digit p=3/2 and 15-digit p=4/3 m=2 "
        "enclosures matching Gap <= appear in V7 Anchor Ledger above.)"
    )


# ==============================================================================
# THEOREM G5: COMPARISON AGAINST `#143` THEOREM 1(a)-(b) CLOSED-FORM BOUNDS
#             C_4L(p, m) ACROSS ALL p in [6/5, 2) (POINTWISE + CONTINUUM!)
# ==============================================================================

def make_test_exponents_G5():
    """Returns 15 rational & irrational exponents spanning [6/5, 2) matching `#143` Suite 0."""
    specs = [
        ("6/5",     ("rat",  6,  5), "1(b)"),
        ("5/4",     ("rat",  5,  4), "1(b)"),
        ("1.30",    ("rat", 13, 10), "1(b)"),
        ("4/3",     ("rat",  4,  3), "1(b)"),
        ("7/5",     ("rat",  7,  5), "1(b)"),
        ("sqrt(2)", ("sqrt2",),      "1(b)"),
        ("1.45",    ("rat", 29, 20), "1(b)"),
        ("3/2",     ("rat",  3,  2), "1(a=b)"),
        ("1.60",    ("rat",  8,  5), "1(a)"),
        ("phi",     ("phi",),        "1(a)"),
        ("5/3",     ("rat",  5,  3), "1(a)"),
        ("7/4",     ("rat",  7,  4), "1(a)"),
        ("1.80",    ("rat",  9,  5), "1(a)"),
        ("1.90",    ("rat", 19, 10), "1(a)"),
        ("1.95",    ("rat", 39, 20), "1(a)"),
    ]
    out = []
    for lbl, spec, part in specs:
        if spec[0] == "rat":
            pn, pd = spec[1], spec[2]
            p_iv = iv.mpf(pn) / iv.mpf(pd)
            t_iv = iv.mpf(pd) / iv.mpf(pn)
        elif spec[0] == "sqrt2":
            p_iv = iv.sqrt(iv.mpf(2))
            t_iv = iv.mpf(1) / p_iv
        elif spec[0] == "phi":
            p_iv = (iv.mpf(1) + iv.sqrt(iv.mpf(5))) / iv.mpf(2)
            t_iv = iv.mpf(1) / p_iv
        else:
            raise AssertionError(f"Unknown spec {spec}")
        out.append((lbl, p_iv, t_iv, part))
    return out


def certify_theorem_G5(m, n_sub_per_seg=100):
    anc_v7 = build_anchors_in_t(m, mode="v7")
    pts = make_test_exponents_G5()

    print(
        f"\n[THEOREM G5 | m = {m}] V7 ENVELOPE VS `#143` THEOREM 1(a)-(b) CLOSED-FORM C_4L(p, {m}) "
        f"& HADAMARD C_Had(p, {m}) ON [6/5, 2):"
    )
    print(
        f"  {'p':>7s} | {'Thm':>6s} | {'Cert LB (flr)':>14s} | {'V7 UB (ceil)':>14s} | "
        f"{'C_4L (flr)':>14s} | {'C_Had (flr)':>14s} | {'C_4L-V7 >=':>10s} | {'C_4L vs Had':>11s}"
    )
    print("  " + "-" * 112)

    for lbl, _, t_iv, part in pts:
        U7_iv = iv_eval_envelope_t(t_iv, anc_v7)
        C4L_iv = iv_C_4L_at_t(t_iv, m)
        Chad_iv = iv_C_hadamard_t(t_iv, m)

        if lbl in V7_MULTI_LB:
            LB_lo = mp.mpf(iv_from_dec_str(V7_MULTI_LB[lbl][m]).a)
        else:
            LB_lo = iv_opt_matrix_lb_on_tbox(mp.mpf(t_iv.a), mp.mpf(t_iv.b), m)

        U7_hi = mp.mpf(U7_iv.b)
        C4L_lo = mp.mpf(C4L_iv.a)
        C4L_hi = mp.mpf(C4L_iv.b)
        Chad_lo = mp.mpf(Chad_iv.a)
        Chad_hi = mp.mpf(Chad_iv.b)

        # Certify BOTH U_V7 < C_4L and U_V7 < C_Had strictly!
        assert LB_lo < U7_hi < C4L_lo, f"Failed U_V7 < C_4L at p={lbl}, m={m}!"
        assert U7_hi < Chad_lo, f"Failed U_V7 < C_Had at p={lbl}, m={m}!"

        margin_4L_lo = mp.mpf((iv.mpf(C4L_lo) - iv.mpf(U7_hi)).a)
        assert margin_4L_lo > mp.mpf(0)

        if C4L_hi < Chad_lo:
            vs_had_s = "C_4L < Had"
        elif Chad_hi < C4L_lo:
            vs_had_s = "Had < C_4L"
        else:
            raise AssertionError(f"Ambiguous C_4L vs C_Had ordering at p={lbl}, m={m}!")

        lb_s = floor_fixed_str(LB_lo, 11)
        u7_s = ceil_fixed_str(U7_hi, 11)
        c4l_s = floor_fixed_str(C4L_lo, 11)
        chad_s = floor_fixed_str(Chad_lo, 11)
        marg_s = floor_sci_str(margin_4L_lo, 3)
        assert mp.mpf((iv.mpf(c4l_s) - iv.mpf(u7_s)).a) >= mp.mpf(iv.mpf(marg_s).b)

        print(
            f"  {lbl:>7s} | {part:>6s} | {lb_s:>14s} | "
            f"{u7_s:>14s} | {c4l_s:>14s} | "
            f"{chad_s:>14s} | +{marg_s:>9s} | {vs_had_s:>11s}"
        )

    # --- CONTINUUM CERTIFICATION: U_V7(p; m) < C_4L(p, m) FOR EVERY REAL p in [6/5, 2)! ---
    # Part (b) continuum [6/5, 3/2] (t in [2/3, 5/6]):
    #   log C_4L(1/t, m) is EXACTLY AFFINE in t, while log U_V7(1/t; m) is piecewise affine
    #   with breakpoints {2/3, 3/4, 4/5, 5/6}. Therefore the global minimum of the log-margin
    #   log C_4L(1/t, m) - log U_V7(1/t; m) on ALL of [2/3, 5/6] is attained at one of the
    #   4 anchors {3/2, 4/3, 5/4, 6/5}. Since U_V7(1/t; m) >= U_V7(6/5; m) > 1 on [2/3, 5/6],
    #   C_4L(1/t, m) - U_V7(1/t; m) >= U_V7(6/5; m) * (exp(min_log_margin_b) - 1) > 0!
    min_log_margin_b = None
    for idx in (2, 3, 4, 5):  # anchors 3/2, 4/3, 5/4, 6/5
        lbl, ti, _, U7 = anc_v7[idx]
        C4L_i = iv_C_4L_part_b_t(ti, m)
        dlog = mp.mpf((iv.log(C4L_i) - iv.log(U7)).a)
        assert dlog > mp.mpf(0), f"Part (b) affine log-dominance failed at anchor p={lbl}!"
        if min_log_margin_b is None or dlog < min_log_margin_b:
            min_log_margin_b = dlog

    # Part (a) continuum [3/2, 2) (t in [1/2, 2/3], segments 0 and 1 of anc_v7):
    #   Cover [1/2, 2/3] with 2 * n_sub_per_seg + 2 crack-free contiguous iv-boxes
    #   (including the non-dyadic seams at t = 3/5 and t = 2/3) and directly enclose
    #   C_4L(1/t, m) over EVERY box [tl, th] via iv_C_4L_part_a_tbox(tl, th, m)!
    min_margin_a = None
    min_margin_a_loc = None
    boxes_a = []
    for seg_i in (0, 1):
        t0_iv, U0_v7 = anc_v7[seg_i][1], anc_v7[seg_i][3]
        t1_iv, U1_v7 = anc_v7[seg_i + 1][1], anc_v7[seg_i + 1][3]
        tA = mp.mpf(t0_iv.b)
        tB = mp.mpf(t1_iv.a)
        edges = [tA + (tB - tA) * k / n_sub_per_seg for k in range(n_sub_per_seg + 1)]
        edges[0] = tA
        edges[-1] = tB
        for k in range(n_sub_per_seg):
            tl = edges[k]
            th = edges[k + 1]
            U_v7_hi = mp.mpf(iv.exp(iv_log_interp_on_segment(iv.mpf(tl), t0_iv, U0_v7, t1_iv, U1_v7)).b)
            C4L_box = iv_C_4L_part_a_tbox(tl, th, m)
            marg_lo = mp.mpf((iv.mpf(mp.mpf(C4L_box.a)) - iv.mpf(U_v7_hi)).a)
            assert marg_lo > mp.mpf(0), f"Continuum U_V7 < C_4L failed on t in [{tl}, {th}], m={m}!"
            if min_margin_a is None or marg_lo < min_margin_a:
                min_margin_a = marg_lo
                min_margin_a_loc = (mp.mpf((iv.mpf(1) / iv.mpf(th)).a), mp.mpf((iv.mpf(1) / iv.mpf(tl)).b))
            boxes_a.append((tl, th))

        if mp.mpf(t1_iv.a) < mp.mpf(t1_iv.b):
            tl = mp.mpf(t1_iv.a)
            th = mp.mpf(t1_iv.b)
            t_ref = tl - (mp.mpf(10) ** (-20))
            assert mp.mpf(t0_iv.b) < t_ref < tl
            U_v7_hi = mp.mpf(iv.exp(iv_log_interp_on_segment(iv.mpf(t_ref), t0_iv, U0_v7, t1_iv, U1_v7)).b)
            C4L_box = iv_C_4L_part_a_tbox(tl, th, m)
            marg_lo = mp.mpf((iv.mpf(mp.mpf(C4L_box.a)) - iv.mpf(U_v7_hi)).a)
            assert marg_lo > mp.mpf(0), f"Continuum U_V7 < C_4L failed on seam [{tl}, {th}], m={m}!"
            if min_margin_a is None or marg_lo < min_margin_a:
                min_margin_a = marg_lo
                min_margin_a_loc = (mp.mpf((iv.mpf(1) / iv.mpf(th)).a), mp.mpf((iv.mpf(1) / iv.mpf(tl)).b))
            boxes_a.append((tl, th))

    # Assert exact crack-free contiguous coverage of [1/2, (2/3).b]!
    assert len(boxes_a) == 2 * n_sub_per_seg + 2
    assert boxes_a[0][0] == mp.mpf("0.5") and boxes_a[-1][1] == mp.mpf(anc_v7[2][1].b)
    for i in range(len(boxes_a) - 1):
        assert boxes_a[i][1] == boxes_a[i + 1][0], f"Crack in Part (a) boxes at index {i}!"

    # Assert U_V7(6/5; m) > 1 (monotonic lower bound of U_V7 on [2/3, 5/6]) and compute Part (b) abs margin:
    U_65_iv = anc_v7[5][3]
    assert mp.mpf(U_65_iv.a) > mp.mpf(1)
    min_margin_b_lo = mp.mpf((U_65_iv * (iv.exp(iv.mpf(min_log_margin_b)) - iv.mpf(1))).a)
    global_min_margin_lo = min(min_margin_a, min_margin_b_lo)
    assert global_min_margin_lo > mp.mpf(0)

    print(
        f"    [THEOREM G5 CONTINUUM PASS | m = {m}] U_V7(p; {m}) < C_4L(p, {m}) STRICTLY FOR ALL REAL p in [6/5, 2)!"
    )
    print(
        f"      * Part (b) [6/5, 3/2]: exact affine-in-t certification at 4 anchors -> "
        f"min log-margin >= +{floor_sci_str(min_log_margin_b, 4)} (abs margin >= +{floor_sci_str(min_margin_b_lo, 4)})"
    )
    print(
        f"      * Part (a) [3/2, 2):   {len(boxes_a)} crack-free iv-boxes covering [1/2, 2/3] -> "
        f"min abs margin >= +{floor_sci_str(min_margin_a, 4)} "
        f"(near p in [{floor_fixed_str(min_margin_a_loc[0], 4)}, {ceil_fixed_str(min_margin_a_loc[1], 4)}])"
    )
    print(
        f"      * GLOBAL [6/5, 2) MARGIN: inf_{{p in [6/5, 2)}} (C_4L(p, {m}) - U_V7(p; {m})) "
        f">= +{floor_sci_str(global_min_margin_lo, 4)} > 0!"
    )
    return global_min_margin_lo


# ==============================================================================
# MAIN EXECUTION
# ==============================================================================

if __name__ == "__main__":
    t0_ns = time.perf_counter_ns()
    audit_info = run_ast_zero_float_audit()
    self_test_outward_formatters()

    print("================================================================================")
    print("VERSION 7: 100% ZERO-FLOAT mpmath.iv GLOBAL COMPLEX-INTERPOLATION CERTIFICATION")
    print("           (ALL 1 < p < 2, m = 2, 3, 4, ALL MATRIX DIMENSIONS n >= 1)")
    print("================================================================================")
    print(
        f"[MODULE 0 PASS] Whole-File AST Zero-Float Audit: {audit_info['file']} "
        f"({audit_info['lines']} lines, {audit_info['functions']} functions, {audit_info['nodes']} AST nodes) -> "
        f"0 float/complex literals, 0 float() calls, 0 numpy/scipy/math/sympy refs! "
        f"Outward iv.mpf(s) formatters self-tested PASS (mp.dps={mp.mp.dps}, iv.dps={iv.dps})."
    )

    for m in (2, 3, 4):
        c2_iv = iv_C2(m)
        print("\n################################################################################")
        print(
            f"###  m = {m}   (C_1({m}) = 1,  "
            f"C_2({m}) in [{floor_fixed_str(mp.mpf(c2_iv.a), 15)}, {ceil_fixed_str(mp.mpf(c2_iv.b), 15)}])"
        )
        print("################################################################################")
        print_anchor_upgrade_summary(m)
        certify_theorem_G1(m)
        certify_theorem_G2(m)
        certify_theorem_G3(m, n_sub_per_seg=100)
        certify_table_G4(m)
        certify_theorem_G5(m, n_sub_per_seg=100)

    dt_ns = time.perf_counter_ns() - t0_ns
    print(
        f"\nALL VERSION 7 GLOBAL INTERPOLATION THEOREMS (M0, G1-G5) CERTIFIED WITH ZERO FLOATS! "
        f"({format_elapsed_ns(dt_ns)})"
    )
