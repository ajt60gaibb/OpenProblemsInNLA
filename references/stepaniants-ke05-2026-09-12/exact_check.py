#!/usr/bin/env python3
"""Exact transcription checks for the KE-05 rational witness.

This checks polynomial identities at the printed rational witness and
finite recurrence instances. It is not a replacement for the generic
probability proof in RESULT.md. Python standard library only.
"""

from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json


def p(a):
    if isinstance(a, (int, F)):
        return (F(a),)
    a = tuple(map(F, a))
    while len(a) > 1 and not a[-1]:
        a = a[:-1]
    return a


def add(a, b):
    return p([(a[i] if i < len(a) else F(0))
              + (b[i] if i < len(b) else F(0))
              for i in range(max(len(a), len(b)))])


def neg(a):
    return p([-v for v in a])


def sub(a, b):
    return add(a, neg(b))


def mul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return p(out)


def matrix(values):
    return [[p(values[i][j]) for j in range(2)] for i in range(2)]


def madd(a, b):
    return [[add(a[i][j], b[i][j]) for j in range(2)] for i in range(2)]


def msub(a, b):
    return [[sub(a[i][j], b[i][j]) for j in range(2)] for i in range(2)]


def mmul(a, b):
    return [[add(mul(a[i][0], b[0][j]), mul(a[i][1], b[1][j]))
             for j in range(2)] for i in range(2)]


def mscale(a, c):
    return [[mul(a[i][j], p(c)) for j in range(2)] for i in range(2)]


def det(a):
    return sub(mul(a[0][0], a[1][1]), mul(a[0][1], a[1][0]))


def adj(a):
    return [[a[1][1], neg(a[0][1])],
            [neg(a[1][0]), a[0][0]]]


def tr(a):
    return add(a[0][0], a[1][1])


def const_inv(a):
    delta = det(a)
    assert len(delta) == 1 and delta[0]
    return mscale(adj(a), 1 / delta[0])


def evaluate(a, x):
    return p(sum(coef * x**i for i, coef in enumerate(a)))


def mevaluate(a, x):
    return [[evaluate(a[i][j], x) for j in range(2)] for i in range(2)]


checks = []


def check(name, condition):
    if not condition:
        raise AssertionError(name)
    checks.append(name)


I = matrix([[1, 0], [0, 1]])
Z = matrix([[0, 0], [0, 0]])
X = matrix([[1, 0], [0, 2]])
Omega3 = matrix([[1, 2], [3, 5]])
Lambda3 = matrix([[0, 0], [0, 1]])
P = mmul(mmul(const_inv(Omega3), Lambda3), Omega3)
check("Printed P equals the exact similarity",
      P == matrix([[6, 10], [-3, -5]]))
check("P is idempotent", mmul(P, P) == P)
check("Trace and determinant of P", tr(P) == p(1) and det(P) == p(0))
check("Adjugate of P", adj(P) == msub(I, P))
Q = mmul(mmul(msub(I, P), X), P)
check("Printed Q equals (I-P)XP",
      Q == matrix([[30, 50], [-18, -30]]))
kappa = tr(mmul(msub(I, P), X))
check("Printed kappa", kappa == p(7))
N = mscale(Q, F(-1, 7))
check("Printed N", N == matrix([[F(-30, 7), F(-50, 7)],
                               [F(18, 7), F(30, 7)]]))
check("Nonzero nilpotent limit", N != Z and mmul(N, N) == Z)
frob2 = sum(N[i][j][0]**2 for i in range(2) for j in range(2))
check("Rank-one spectral norm 68/7",
      det(N) == p(0) and frob2 == F(68, 7)**2)

e = p([0, 1])
h = p([-7, 2])
S = msub(mscale(X, e), P)
Hnum = matrix([[[30, -7, 2], [50, 20]],
               [[-18, 3], [-30, -14, 4]]])
check("det S = epsilon(2epsilon-7)", det(S) == mul(e, h))
check("Printed numerator from the adjugate formula",
      Hnum == mmul(mmul(msub(mscale(adj(X), e), msub(I, P)), X), S))
check("Polynomial similarity identity S Hnum = epsilon X S h",
      mmul(S, Hnum) == mscale(mmul(mscale(X, e), S), h))
check("Trace of transformed second block",
      tr(Hnum) == mul(p([0, 3]), h))
check("Determinant of transformed second block",
      det(Hnum) == mul(p([0, 0, 2]), mul(h, h)))
check("Constant term gives the printed limit",
      mevaluate(Hnum, F(0)) == mscale(N, -7))
S13num = mmul(msub(mscale(I, mul(p(2), h)), Hnum),
              msub(mscale(I, 2), P))
d13 = mul(p(2), mul(p([2, -1]), p([2, -2])))
check("Root determinant identity as a polynomial",
      det(S13num) == mul(d13, mul(h, h)))


def recurrence(diagonals, omegas, order):
    bs = []
    for i in order:
        bs.append(mmul(mmul(const_inv(omegas[i]), diagonals[i]),
                       omegas[i]))
    hats = [None] * 3
    ss = [None] * 3
    for i in reversed(range(3)):
        s = I
        for j in range(i + 1, 3):
            s = msub(mmul(bs[i], s), mmul(s, hats[j]))
        assert det(s) != p(0)
        hats[i] = mmul(mmul(const_inv(s), bs[i]), s)
        ss[i] = s
        assert tr(hats[i]) == tr(diagonals[order[i]])
        assert det(hats[i]) == det(diagonals[order[i]])
    return hats, ss


finite = []
for denominator in (6, 7, 10, 100, 1000, 10000):
    eps = F(1, denominator)
    diagonals = [mscale(I, 2), mscale(X, eps), Lambda3]
    omegas = [I, I, Omega3]
    for k in range(3):
        order = [k] + [i for i in range(3) if i != k]
        hats, ss = recurrence(diagonals, omegas, order)
        check(f"Exact finite recurrence: epsilon=1/{denominator}, root={k+1}",
              all(det(s) != p(0) for s in ss))
        if k == 0:
            check(f"Exact root determinant: epsilon=1/{denominator}",
                  det(ss[0]) == p(2 * (2-eps) * (2-2*eps)))
            expected_hat2 = mscale(mevaluate(Hnum, eps),
                                  1 / evaluate(h, eps)[0])
            check(f"Exact hatB2 formula: epsilon=1/{denominator}",
                  hats[1] == expected_hat2)
            norm_lower_sq = sum(hats[1][i][j][0]**2
                                for i in range(2) for j in range(2)) / 2
            product_fourth_lower = norm_lower_sq**2 / (8 * (2*eps)**4)
            finite.append({
                "epsilon": str(eps),
                "lower_bound_on_product_to_fourth_power":
                    str(product_fourth_lower),
                "approximate_fourth_root_for_display_only":
                    float(product_fourth_lower)**0.25,
            })

base = Path(__file__).resolve().parent
out = {
    "verdict": "PASS",
    "scope": ("Exact rational witness and polynomial transcription checks; "
              "finite recurrence checks for all three roots at six inputs. "
              "Not a numerical or formal verification of the probability proof."),
    "source_sha256": sha256((base / "reviewed-proof.md").read_bytes()).hexdigest(),
    "checker_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
    "passed_checks": len(checks),
    "checks": checks,
    "finite_input_diagnostics": finite,
}
print(json.dumps(out, indent=2))
