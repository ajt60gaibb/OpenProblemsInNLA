#!/usr/bin/env python3
"""Independent exact universal algebra checks for RA-19 (standard library).

This checks identities over Z[f,g,h,fp,gp,hp], not a finite numerical sample.
It does not import or invoke the candidate author's checker.  The geometric
and genericity arguments require the separate human-readable agent review.
"""

from itertools import permutations
from pathlib import Path
import hashlib
import json


class Poly:
    names = ("f", "g", "h", "fp", "gp", "hp")
    zero_power = (0,) * len(names)

    def __init__(self, terms=None):
        self.terms = {e: c for e, c in (terms or {}).items() if c}

    @classmethod
    def constant(cls, value):
        return cls({cls.zero_power: value})

    @classmethod
    def variable(cls, index):
        power = list(cls.zero_power)
        power[index] = 1
        return cls({tuple(power): 1})

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Poly) else Poly.constant(value)

    def __add__(self, other):
        other = self.coerce(other)
        result = dict(self.terms)
        for power, coefficient in other.terms.items():
            result[power] = result.get(power, 0) + coefficient
        return Poly(result)

    __radd__ = __add__

    def __neg__(self):
        return Poly({e: -c for e, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) + (-self)

    def __mul__(self, other):
        other = self.coerce(other)
        result = {}
        for power1, coefficient1 in self.terms.items():
            for power2, coefficient2 in other.terms.items():
                power = tuple(a + b for a, b in zip(power1, power2))
                result[power] = result.get(power, 0) + coefficient1 * coefficient2
        return Poly(result)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        assert isinstance(exponent, int) and exponent >= 0
        result = self.constant(1)
        for _ in range(exponent):
            result = result * self
        return result

    def __eq__(self, other):
        return self.terms == self.coerce(other).terms


def product_z(left, right):
    result = [Poly() for _ in range(len(left) + len(right) - 1)]
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] = result[i + j] + a * b
    return result


def determinant(matrix):
    size = len(matrix)
    result = Poly()
    for permutation in permutations(range(size)):
        inversions = sum(
            permutation[i] > permutation[j]
            for i in range(size) for j in range(i + 1, size)
        )
        term = Poly.constant((-1) ** inversions)
        for i, j in enumerate(permutation):
            term = term * matrix[i][j]
        result = result + term
    return result


def main():
    f, g, h, fp, gp, hp = (Poly.variable(i) for i in range(6))
    alpha = f**2 * (hp - f) + 4*f*g*gp - f*fp*h - 4*fp*g**2
    beta = -f**2*g - 2*f*gp*h + 2*fp*g*h
    p = [h, -2*g, -f]
    e = [-g, hp - f, -2*gp, -fp]
    quotient = [2*f*gp - 2*fp*g, f*fp]
    lhs = [f**2 * coefficient for coefficient in e]
    lhs[0] = lhs[0] - beta
    lhs[1] = lhs[1] - alpha
    rhs = product_z(quotient, p)
    reduction_checks = [a == b for a, b in zip(lhs, rhs)]
    assert len(lhs) == len(rhs) == 4 and all(reduction_checks)

    zero = Poly()
    # Standard Sylvester matrix: 3 shifted rows of the degree-2 P,
    # followed by 2 shifted rows of the degree-3 E, in descending powers.
    sylvester = [
        [-f, -2*g, h, zero, zero],
        [zero, -f, -2*g, h, zero],
        [zero, zero, -f, -2*g, h],
        [-fp, -2*gp, hp - f, -g, zero],
        [zero, -fp, -2*gp, hp - f, -g],
    ]
    resultant = determinant(sylvester)
    numerator = h*alpha**2 + 2*g*alpha*beta - f*beta**2
    assert f**2 * resultant == numerator

    source = Path(__file__).resolve().parents[1] / "RESULT.md"
    expected = "475e29760333fc215e80eed33e4729649383d112d585d7cca88a8b669b618c22"
    actual = hashlib.sha256(source.read_bytes()).hexdigest()
    assert actual == expected, "The reviewed source changed."
    output = {
        "verdict": "PASS",
        "source_file": "../RESULT.md",
        "source_sha256": actual,
        "arithmetic": "Exact integers in Z[f,g,h,fp,gp,hp]; standard library only",
        "scope": "Universal algebra identities (8)-(10), independent of n; not a formal verification of the geometric proof",
        "checks": {
            "four_z_coefficients_of_f_squared_E_minus_alpha_z_minus_beta_equal_Q_P": reduction_checks,
            "Q": "f*fp*z+2*f*gp-2*fp*g",
            "sylvester_determinant_size": 5,
            "determinant_permutations": 120,
            "resultant_expanded_term_count": len(resultant.terms),
            "numerator_expanded_term_count": len(numerator.terms),
            "f_squared_resultant_equals_h_alpha_squared_plus_2g_alpha_beta_minus_f_beta_squared": True,
        },
        "implementation_independence": "Written from the independently derived identities; no author-checker code was read, imported, or executed for these checks.",
    }
    target = Path(__file__).with_name("universal-algebra-check.json")
    target.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
