#!/usr/bin/env python3
"""Independent exact algebra checks for the MF-02 candidate.

This checks polynomial identities over Q, not sample points. It is not a formal
verification of the approximation-theoretic proof or its requested scope.
Run: python3 exact_algebra_check.py --output exact-algebra-output.json
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path


class Poly:
    """Dense rational polynomial, with coefficients in ascending order."""

    def __init__(self, *coefficients):
        data = [Fraction(c) for c in coefficients] or [Fraction(0)]
        while len(data) > 1 and data[-1] == 0:
            data.pop()
        self.coefficients = tuple(data)

    @staticmethod
    def cast(value):
        return value if isinstance(value, Poly) else Poly(value)

    def __add__(self, other):
        other = self.cast(other)
        n = max(len(self.coefficients), len(other.coefficients))
        return Poly(*(self.coefficient(i) + other.coefficient(i) for i in range(n)))

    __radd__ = __add__

    def __neg__(self):
        return Poly(*(-c for c in self.coefficients))

    def __sub__(self, other):
        return self + (-self.cast(other))

    def __rsub__(self, other):
        return self.cast(other) - self

    def __mul__(self, other):
        other = self.cast(other)
        data = [Fraction(0)] * (len(self.coefficients) + len(other.coefficients) - 1)
        for i, ci in enumerate(self.coefficients):
            for j, cj in enumerate(other.coefficients):
                data[i + j] += ci * cj
        return Poly(*data)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        if not isinstance(exponent, int) or exponent < 0:
            raise ValueError("Polynomial exponent must be a nonnegative integer")
        result = Poly(1)
        for _ in range(exponent):
            result = result * self
        return result

    def coefficient(self, index):
        return self.coefficients[index] if index < len(self.coefficients) else Fraction(0)

    def __eq__(self, other):
        return self.coefficients == self.cast(other).coefficients


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=here / "reviewed-candidate.md")
    parser.add_argument("--canonical", type=Path, default=here / "canonical-target.md")
    parser.add_argument("--output", type=Path, default=here / "exact-algebra-output.json")
    args = parser.parse_args()
    checks = []

    def identity(label, left, right):
        left, right = Poly.cast(left), Poly.cast(right)
        if left != right:
            raise ArithmeticError(f"FAILED: {label}; residual {(left-right).coefficients}")
        checks.append({"name": label, "kind": "rational polynomial identity", "pass": True})

    a = Poly(0, 1)
    A = 1 + a + a**2
    identity("critical point lies above a", A - 3*a**2, (1-a)*(1+2*a))
    identity("critical point lies below 1", 3 - A, (1-a)*(a+2))
    identity("lower endpoint numerator", a*(A-a**2), a*(1+a))
    identity("upper endpoint numerator", A-1, a*(1+a))
    identity("squared critical maximum", Fraction(1,3)*A*(Fraction(2,3)*A)**2,
             Fraction(4,27)*A**3)

    comparison_factor = Poly(11, 28, 30, 28, 11)
    identity("uniform cubic comparison (candidate equation 10)",
             27*(1+a)**2*(1+a**2)**2 - 16*A**3,
             (1-a)**2*comparison_factor)
    strict_maximum_factor = Poly(4, 20, 33, 20, 4)
    identity("strict endpoint versus interior maximum",
             4*A**3 - 27*a**2*(1+a)**2,
             (1-a)**2*strict_maximum_factor)
    for name, factor in [("comparison factor", comparison_factor),
                         ("strict maximum factor", strict_maximum_factor)]:
        if not all(c > 0 for c in factor.coefficients):
            raise ArithmeticError(f"FAILED positive coefficient check: {name}")
        checks.append({"name": name + " has positive coefficients", "kind": "exact coefficient signs", "pass": True})

    identity("Mobius ratio squaring after cross multiplication",
             (1+a**2-2*a)*(1+a)**2,
             (1+a**2+2*a)*(1-a)**2)
    e = a
    numerator, denominator = 1-e, 1+e
    identity("error-to-gap Mobius involution",
             denominator-numerator, e*(denominator+numerator))
    d = a
    identity("hyperbolic argument after clearing positive denominators",
             ((1+d)**2+(1-d)**2)*(1-d**2),
             2*(1+d**2)*(1-d)*(1+d))
    identity("strict improvement from empty composition",
             (1-d)*(1+d)**2-(1-d)**2,
             d*(1-d)*(d+3))
    identity("rescaled lower endpoint error", 2*a-(1+a), -(1-a))
    identity("rescaled upper endpoint error", 2-(1+a), 1-a)

    # The all-integer comparison follows by parity; these are identities in h.
    h = a
    identity("even m=2h uniform lower bound margin", 4*h-(2*h+1), 2*h-1)
    identity("odd m=2h+1 uniform lower bound margin", 4*h-(2*h+2), 2*h-2)

    output = {
        "verdict": "PASS",
        "independence": "Written independently by Codex agent /root/prepare_manuscripts; no author checker used.",
        "arithmetic": "Python standard-library Fraction; exact polynomial operations over Q.",
        "scope": "Algebraic identities and coefficient signs only. Full infinite-parameter and scope arguments are in the independent review.",
        "source": {"name": args.source.name, "bytes": args.source.stat().st_size, "sha256": sha256(args.source)},
        "canonical": {"name": args.canonical.name, "bytes": args.canonical.stat().st_size, "sha256": sha256(args.canonical)},
        "checker": {"name": Path(__file__).name, "sha256": sha256(Path(__file__))},
        "check_count": len(checks),
        "checks": checks,
    }
    args.output.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({"verdict": "PASS", "exact_check_count": len(checks), "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
