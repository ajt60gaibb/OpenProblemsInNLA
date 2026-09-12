#!/usr/bin/env python3
"""Independent exact SP-15 coefficient check in a Gaussian-integer polynomial ring.

This script was written from the reviewer's own three-by-three determinant
expansion. It does not read or import the author's diagnostic checker.
The all-shift Schur identity and smooth-fiber argument are audited analytically
in review.md; this code does not claim formal verification of those arguments.
"""
from itertools import permutations
from pathlib import Path
import hashlib
import json


class Poly:
    names = ("p1", "p2", "p3", "q1", "q2", "q3", "a", "b", "c", "d", "u", "s")
    zero = (0,) * len(names)

    def __init__(self, terms=None):
        self.terms = {k: v for k, v in (terms or {}).items() if v != (0, 0)}

    @classmethod
    def const(cls, real, imag=0):
        return cls({cls.zero: (real, imag)})

    @classmethod
    def variable(cls, index):
        p = list(cls.zero)
        p[index] = 1
        return cls({tuple(p): (1, 0)})

    @staticmethod
    def coerce(other):
        return other if isinstance(other, Poly) else Poly.const(other)

    def __add__(self, other):
        result = dict(self.terms)
        for k, (a, b) in self.coerce(other).terms.items():
            c, d = result.get(k, (0, 0))
            result[k] = (a + c, b + d)
        return Poly(result)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: (-a, -b) for k, (a, b) in self.terms.items()})

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) + (-self)

    def __mul__(self, other):
        result = {}
        for p, (a, b) in self.terms.items():
            for q, (c, d) in self.coerce(other).terms.items():
                k = tuple(x + y for x, y in zip(p, q))
                e, f = result.get(k, (0, 0))
                result[k] = (e + a*c - b*d, f + a*d + b*c)
        return Poly(result)

    __rmul__ = __mul__

    def __pow__(self, n):
        value = Poly.const(1)
        for _ in range(n):
            value = value * self
        return value

    def __eq__(self, other):
        return self.terms == self.coerce(other).terms


def determinant(matrix):
    result = Poly()
    for perm in permutations(range(len(matrix))):
        inversions = sum(perm[i] > perm[j] for i in range(len(perm)) for j in range(i+1, len(perm)))
        term = Poly.const((-1) ** inversions)
        for i, j in enumerate(perm):
            term = term * matrix[i][j]
        result = result + term
    return result


def main():
    p1, p2, p3, q1, q2, q3, a, b, c, d, u, s = [Poly.variable(j) for j in range(12)]
    ii = Poly.const(0, 1)
    p = [p1, p2, p3]
    q = [q1, q2, q3]
    Q = [[q1, a, b], [a, q2, c + ii*d], [b, c - ii*d, q3]]
    L = [u + s*(p[j] + q[j]) + p[j]*q[j] for j in range(3)]
    matrix = [[L[i] if i == j else (s+p[i])*Q[i][j] for j in range(3)] for i in range(3)]
    direct = determinant(matrix)
    formula = (L[0]*L[1]*L[2]
               - L[0]*(s+p2)*(s+p3)*(c**2+d**2)
               - L[1]*(s+p1)*(s+p3)*b**2
               - L[2]*(s+p1)*(s+p2)*a**2
               + 2*a*b*c*(s+p1)*(s+p2)*(s+p3))
    assert direct == formula
    assert all(imag == 0 for real, imag in direct.terms.values())
    assert max(e[-2] + e[-1] for e in direct.terms) == 3
    leading = {e: v for e, v in direct.terms.items() if e[-2] == 3}
    expected = [0] * 12
    expected[-2] = 3
    assert leading == {tuple(expected): (1, 0)}
    support = sorted({(e[-2], e[-1]) for e in direct.terms})
    assert len(support) == 10
    assert all(j >= 0 and k >= 0 and j+k <= 3 for j, k in support)
    source = Path(__file__).resolve().parents[1] / "RESULT.md"
    source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
    assert source_hash == "d992da0546924d7fbc9f1bb0e89e00b1442ec3c3045c739722c9767078ce40c1"
    output = {
        "result": "PASS",
        "source_file": "../RESULT.md",
        "source_sha256": source_hash,
        "arithmetic": "Exact Gaussian integer coefficients and nonnegative integer exponents; no floating point or external package",
        "scope": "Universal coefficient identity for the entire ten-parameter r=3 gauge family; not formal certification of the geometric proof",
        "checks": {
            "three_by_three_permutation_determinant_matches_explicit_cycle_formula": True,
            "all_coefficients_real": True,
            "maximum_total_u_s_degree": 3,
            "u_cubed_coefficient_identically_one": True,
            "u_s_monomial_support": support,
            "remaining_real_coefficient_slots": 9,
            "expanded_parameter_monomial_count": len(direct.terms),
        },
        "independence": "No author-checker code read, imported, or invoked; independent reviewer implementation",
    }
    target = Path(__file__).with_name("coefficient-check.json")
    target.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
