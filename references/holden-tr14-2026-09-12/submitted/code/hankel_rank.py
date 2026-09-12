#!/usr/bin/env python3
"""Exact ranks of rational complex Hankel tensors, using Theorem 1.1.

The theorem is over C. This reference implementation accepts rational moment
entries only; it never substitutes a floating-point rank threshold for exact
linear algebra. Its output relies on the accompanying mathematical proof.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
from fractions import Fraction
import json
from pathlib import Path
from typing import Sequence, Union

import sympy as sp

RationalInput = Union[int, str, Fraction, sp.Rational]


@dataclass(frozen=True)
class HankelRankResult:
    order: int
    dimension: int
    binary_degree: int
    catalecticant_rank: int
    apolar_degree: int
    distinct_projective_roots: int
    infinity_multiplicity: int
    balanced: bool
    apolar_coefficients: list[str]
    apolar_polynomial: str
    binary_upper_bound: int
    local_upper_bound: int
    ordinary_rank: int
    symmetric_rank: int
    border_rank: int
    vandermonde_rank: int
    method: str = "Theorems 1.1 and 6.1 of TR14_solution.pdf; exact rational arithmetic"


def _rational(value: RationalInput) -> sp.Rational:
    if isinstance(value, (float, complex, bool, sp.Float)):
        raise TypeError("Use integers or exact rational strings, not floating-point values.")
    if isinstance(value, Fraction):
        return sp.Rational(value.numerator, value.denominator)
    if not isinstance(value, (int, str, sp.Rational)):
        raise TypeError(f"Unsupported input type: {type(value).__name__}")
    try:
        result = sp.Rational(value)
    except (TypeError, ValueError, ZeroDivisionError) as exc:
        raise ValueError(f"Not a finite rational moment: {value!r}") from exc
    if not result.is_finite:
        raise ValueError("Every moment must be finite.")
    return result


def exact_hankel_rank(order: int, dimension: int,
                      moments: Sequence[RationalInput]) -> HankelRankResult:
    """Return exact ordinary, symmetric, border, and Vandermonde ranks.

    Parameters
    ----------
    order : int
        Tensor order m >= 3.
    dimension : int
        Common mode dimension n >= 2.
    moments : sequence of integers or exact rational strings
        h[0], ..., h[m*(n-1)], in zero-based sum-of-indices convention.
    """
    if isinstance(order, bool) or not isinstance(order, int) or order < 3:
        raise ValueError("order must be an integer >= 3")
    if isinstance(dimension, bool) or not isinstance(dimension, int) or dimension < 2:
        raise ValueError("dimension must be an integer >= 2")
    D = order * (dimension - 1)
    if len(moments) != D + 1:
        raise ValueError(f"Expected {D + 1} moments, received {len(moments)}")
    h = [_rational(x) for x in moments]
    if all(x == 0 for x in h):
        return HankelRankResult(order, dimension, D, 0, 0, 0, 0, False,
                                [], "0", 0, 0, 0, 0, 0, 0)

    # Find the first apolar degree directly, without assuming it in advance.
    kernel = None
    r = 0
    for d in range(1, D // 2 + 2):
        C_d = sp.Matrix(D - d + 1, d + 1, lambda j, i: h[i + j])
        basis = C_d.nullspace()
        if basis:
            r, kernel = d, basis[0]
            break
    if kernel is None:
        raise ArithmeticError("No minimal apolar kernel found; this should be impossible.")

    middle = sp.Matrix(D // 2 + 1, (D + 1) // 2 + 1,
                       lambda i, j: h[i + j])
    middle_rank = int(middle.rank())
    if middle_rank != r:
        raise ArithmeticError("Minimal apolar degree and middle rank do not agree.")

    # Normalize the last nonzero coefficient, including roots at infinity.
    e = max(i for i in range(r + 1) if kernel[i] != 0)
    coefficients = [sp.cancel(kernel[i] / kernel[e]) for i in range(r + 1)]
    t, X, Y = sp.symbols("t X Y")
    g = sp.Poly(sum(coefficients[i] * t**i for i in range(r + 1)), t, domain=sp.QQ)
    gcd_degree = int(sp.gcd(g, g.diff()).degree())
    s = e - gcd_degree + int(e < r)
    infinity_multiplicity = r - e
    homogeneous = sp.expand(sum(coefficients[i] * X**(r-i) * Y**i
                                for i in range(r + 1)))
    binary_upper = D - r + 2
    local_upper = (order - 1) * r - (order - 2) * s
    rank = min(binary_upper, local_upper)
    vandermonde_rank = r if s == r else binary_upper
    return HankelRankResult(
        order, dimension, D, middle_rank, r, s, infinity_multiplicity,
        2 * r == D + 2, [str(c) for c in coefficients], str(homogeneous),
        binary_upper, local_upper, rank, rank, r, vandermonde_rank)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", "-m", type=int, required=True)
    parser.add_argument("--dimension", "-n", type=int, required=True)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--moments", help='JSON list, e.g. "[0,0,1,0,0,0,0]"')
    source.add_argument("--moments-file", type=Path, help="File containing a JSON list")
    parser.add_argument("--output", type=Path, help="Optional output JSON file")
    args = parser.parse_args()
    try:
        text = args.moments_file.read_text() if args.moments_file else args.moments
        values = json.loads(text)
        if not isinstance(values, list):
            raise ValueError("The moments JSON must be a list.")
        result = exact_hankel_rank(args.order, args.dimension, values)
        rendered = json.dumps(asdict(result), indent=2)
    except (ValueError, TypeError, OSError, json.JSONDecodeError) as exc:
        parser.error(str(exc))
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()
