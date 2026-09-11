#!/usr/bin/env python3
"""Construct the exact dyadic-rational pair in proposed solution MF-12.

No floating-point arithmetic is used. The exponent must be a nonnegative rational
number, e.g. 1/2, 7/3, or 0.5. The theorem covers arbitrary real exponents, but a
finite rational input interface does not purport to encode arbitrary real numbers.

Examples:
    python rational_growth_pair.py --gamma 1/2 --output alpha_half.json
    python rational_growth_pair.py --gamma 7/3 --output gamma_seven_thirds.json

The output contains matrices as arrays of exact rational strings. The construction
is a proposed theorem, not repository-cleared or independently reviewed.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import json
from pathlib import Path
from typing import Any

Matrix = list[list[Fraction]]


def zero_matrix(rows: int, columns: int) -> Matrix:
    return [[Fraction(0) for _ in range(columns)] for _ in range(rows)]


def jordan_at_one(order: int) -> Matrix:
    if order < 1:
        raise ValueError("Jordan-block order must be positive")
    result = zero_matrix(order, order)
    for i in range(order):
        result[i][i] = Fraction(1)
        if i + 1 < order:
            result[i][i + 1] = Fraction(1)
    return result


def fractional_pair(lam: Fraction, mu: Fraction) -> tuple[Matrix, Matrix]:
    """Return exact rational A,P for alpha=1-log(mu)/log(lam) in (0,1)."""
    if not isinstance(lam, Fraction) or not isinstance(mu, Fraction):
        raise TypeError("lambda and mu must be fractions.Fraction objects")
    if not Fraction(0) < lam <= Fraction(1, 4) or not lam < mu < Fraction(1):
        raise ValueError("require 0 < lambda <= 1/4 and lambda < mu < 1")
    a = zero_matrix(6, 6)
    for i, value in enumerate((Fraction(1), lam, lam, mu, mu, Fraction(1))):
        a[i][i] = value
    a[1][2] = lam
    a[3][4] = mu
    p = zero_matrix(6, 6)
    for i in (0, 2):
        p[i][0], p[i][1], p[i][3] = Fraction(1), Fraction(-1), Fraction(1)
    for i in (4, 5):
        p[i][5] = Fraction(1)
    return a, p


def kronecker(a: Matrix, b: Matrix) -> Matrix:
    """Kronecker product of nonempty rectangular Fraction matrices."""
    if not a or not b or not a[0] or not b[0]:
        raise ValueError("matrices must be nonempty")
    if any(len(row) != len(a[0]) for row in a) or any(len(row) != len(b[0]) for row in b):
        raise ValueError("ragged matrices are not supported")
    return [[aij * bij for aij in row_a for bij in row_b]
            for row_a in a for row_b in b]


def construct(gamma: Fraction, *, max_dimension: int = 120,
              max_denominator: int = 1000) -> dict[str, Any]:
    """Return a JSON-serializable exact construction; resource guards do not round."""
    if not isinstance(gamma, Fraction):
        raise TypeError("gamma must be a fractions.Fraction object")
    if gamma < 0:
        raise ValueError("gamma must be nonnegative")
    if max_dimension < 1 or max_denominator < 1:
        raise ValueError("resource limits must be positive")
    m = gamma.numerator // gamma.denominator
    alpha = gamma - m
    dimension = m + 1 if alpha == 0 else 6 * (m + 1)
    if dimension > max_dimension:
        raise ValueError(f"dimension {dimension} exceeds limit {max_dimension}; raise --max-dimension explicitly")
    if alpha.denominator > max_denominator:
        raise ValueError(f"denominator {alpha.denominator} exceeds limit {max_denominator}; raise --max-denominator explicitly")
    jordan = jordan_at_one(m + 1)
    if alpha == 0:
        a, p = jordan, zero_matrix(m + 1, m + 1)
        parameter_data = None
    else:
        numerator, denominator = alpha.numerator, alpha.denominator
        lam = Fraction(1, 1 << denominator)
        mu = Fraction(1, 1 << (denominator - numerator))
        base_a, base_p = fractional_pair(lam, mu)
        a, p = kronecker(base_a, jordan), kronecker(base_p, jordan)
        parameter_data = {
            "alpha": str(alpha), "lambda": str(lam), "mu": str(mu),
            "base_lower_constant": "(1-exp(-1/4))*lambda**alpha/sqrt(2)",
            "base_upper_constant": "2*sqrt(6)/(1-mu)**2",
            "jordan_lower_constant": "1" if m == 0 else f"({m})**(-{m})",
            "jordan_upper_constant": str(m + 1),
        }
    return {
        "problem": "MF-12", "status": "proposed theorem; submission audit pending",
        "gamma": str(gamma), "integer_part": m, "dimension": dimension,
        "number_of_generators": 2,
        "entry_encoding": "exact rational strings; no floating-point conversion",
        "growth_claim": "c*n**gamma <= maximum spectral norm of length-n words <= C*n**gamma for all n>=1",
        "joint_spectral_radius_claim": "1",
        "construction_parameters": parameter_data,
        "A": [[str(x) for x in row] for row in a],
        "P_or_zero": [[str(x) for x in row] for row in p],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--gamma", default="1/2", help="nonnegative rational, e.g. 1/2 or 7/3")
    parser.add_argument("--output", type=Path, default=Path("rational_growth_pair.json"))
    parser.add_argument("--max-dimension", type=int, default=120)
    parser.add_argument("--max-denominator", type=int, default=1000)
    args = parser.parse_args()
    try:
        result = construct(Fraction(args.gamma), max_dimension=args.max_dimension,
                           max_denominator=args.max_denominator)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    except (ValueError, TypeError, ZeroDivisionError, OSError) as exc:
        parser.exit(1, f"error: {exc}\n")
    print(f"Wrote two exact rational matrices of order {result['dimension']} to {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
