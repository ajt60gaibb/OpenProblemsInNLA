"""Exact statement precheck only; none of these values is a Lean premise."""
from fractions import Fraction as F
from pathlib import Path
import json


def add(a, b):
    return [[a[i][j] + b[i][j] for j in range(2)] for i in range(2)]


def scale(c, a):
    return [[c * x for x in row] for row in a]


def mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(2)) for j in range(2)]
            for i in range(2)]


def adjoint(a):
    # Every witness entry is real; embedding in complex matrices is a Lean obligation.
    return [list(row) for row in zip(*a)]


def tr(a):
    return a[0][0] + a[1][1]


def det(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def fmt(a):
    return [[str(x) for x in row] for row in a]


t, s = F(5, 12), F(13, 12)
z, one = F(0), F(1)
ident = [[one, z], [z, one]]
zero = [[z, z], [z, z]]
p = [[one, z], [z, z]]
b = [[z, t], [z, z]]
x = add(p, b)
q = [[F(144, 169), F(60, 169)], [F(60, 169), F(25, 169)]]
r = add(p, q)
ep = scale(F(1, 26), [[F(25), F(5)], [F(5), one]])
em = scale(F(1, 26), [[one, F(-5)], [F(-5), F(25)]])
assert s * s == 1 + t * t
assert mul(p, p) == p and mul(q, q) == q
assert q == adjoint(q)
assert r[0][0] == F(313, 169) and det(r) == F(25, 169) > 0
assert add(ep, em) == ident
assert mul(ep, ep) == ep and mul(em, em) == em
assert mul(ep, em) == zero and mul(em, ep) == zero
assert r == add(scale(F(25, 13), ep), scale(F(1, 13), em))
qcomp = add(ident, scale(F(-1), p))
candidate_moduli = {
    "A": (p, p, p),
    "B": (b, scale(t, qcomp), scale(t, p)),
    "A_plus_B": (x, scale(s, q), scale(s, p)),
}
gram_data = {}
for name, (a, mr, ml) in candidate_moduli.items():
    gr, gl = mul(adjoint(a), a), mul(a, adjoint(a))
    assert mul(mr, mr) == gr and mul(ml, ml) == gl
    gram_data[name] = {"right_Gram": fmt(gr), "left_Gram": fmt(gl),
                       "candidate_right_modulus": fmt(mr),
                       "candidate_left_modulus": fmt(ml)}
left_trace = tr(scale(s, ident))
right_trace = tr(p) + tr(scale(t, ident))
assert left_trace == F(13, 6)
assert right_trace == F(11, 6)
assert right_trace - left_trace == F(-1, 3)
record = {
    "purpose": "Statement validation; no computed value is an assumed Lean premise.",
    "t": str(t), "s": str(s), "s_squared": str(s*s),
    "A": fmt(p), "B": fmt(b), "A_plus_B": fmt(x),
    "direction_projector_Q": fmt(q), "spanning_sum_R": fmt(r),
    "det_R": str(det(r)),
    "optional_R_eigenvalues": ["25/13", "1/13"],
    "optional_R_spectral_projectors": [fmt(ep), fmt(em)],
    "Gram_and_square_root_candidates": gram_data,
    "left_limit_candidate": fmt(scale(s, ident)),
    "left_trace": str(left_trace),
    "unitary_invariant_right_trace": str(right_trace),
    "right_minus_left_trace": str(right_trace - left_trace),
    "all_exact_checks_passed": True,
    "not_checked_by_Python": [
        "actual CFC identification of positive square roots",
        "actual positive-integer root-sequence convergence",
        "operator-norm topology equivalence",
        "all-complex-unitary trace invariance and PSD obstruction",
        "complete original conjecture negation",
    ],
}
destination = Path(__file__).with_name("numerical-statement-precheck.json")
destination.write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
