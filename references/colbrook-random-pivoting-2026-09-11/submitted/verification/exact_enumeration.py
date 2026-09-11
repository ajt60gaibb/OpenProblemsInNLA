"""Exhaustively evaluate actual pivot transitions with Fraction arithmetic.

This checker does NOT use the determinant path-cancellation identity to compute
expectations. It recursively performs the rank-one updates themselves. Small
ranks are intentional: the number and size of rational branches grow rapidly.

The optimal errors are enclosed by exact bounds on lambda_min(A), obtained from
the inverse. Thus the reported ratio INTERVALS are rigorous, not rounded guesses
of an irrational eigenvalue.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from functools import lru_cache
import json
from pathlib import Path
import sys
import time

from exact_certificate import decimal_string, rational_string
from rational_linalg import family, scaled_inverse_trace_and_rayleigh

Q = Fraction
FrozenMatrix = tuple[tuple[Fraction, ...], ...]


def energy(b: FrozenMatrix) -> Fraction:
    return sum((x * x for row in b for x in row), Q(0))


def trace(b: FrozenMatrix) -> Fraction:
    return sum((b[i][i] for i in range(len(b))), Q(0))


def eliminate(b: FrozenMatrix, i: int, j: int) -> FrozenMatrix:
    pivot = b[i][j]
    if not pivot:
        raise ArithmeticError("Attempt to use a zero pivot")
    return tuple(tuple(b[a][c] - b[a][j] * b[i][c] / pivot
                       for c in range(len(b)) if c != j)
                 for a in range(len(b)) if a != i)


def exact_expectations(a: FrozenMatrix, steps: int) -> tuple[Fraction, Fraction, dict]:
    """Expected errors for a real PSD square matrix, allowing zero-probability pivots.

    Positive semidefiniteness is a caller precondition; simple impossible cases
    are detected below. Exact zero residuals cause early termination.
    """
    if not a or any(len(row) != len(a) for row in a) or steps < 0 or steps >= len(a):
        raise ValueError("Require a nonempty square matrix and 0 <= steps < dimension")

    @lru_cache(maxsize=None)
    def chol(b: FrozenMatrix, k: int) -> Fraction:
        if not k:
            return trace(b)
        normalizer = trace(b)
        if any(b[i][i] < 0 for i in range(len(b))):
            raise AssertionError("Expected a positive-semidefinite principal residual")
        if normalizer == 0:
            if any(x for row in b for x in row):
                raise AssertionError("A PSD residual with zero trace must be zero")
            return Q(0)
        probabilities = [b[i][i] / normalizer for i in range(len(b))]
        if sum(probabilities, Q(0)) != 1:
            raise AssertionError("Cholesky probabilities do not sum to one")
        return sum((p * chol(eliminate(b, i, i), k - 1)
                    for i, p in enumerate(probabilities) if p), Q(0))

    @lru_cache(maxsize=None)
    def lu(b: FrozenMatrix, k: int) -> Fraction:
        if not k:
            return energy(b)
        normalizer = energy(b)
        if normalizer == 0:
            return Q(0)
        expected = Q(0)
        probability_sum = Q(0)
        for i in range(len(b)):
            for j in range(len(b)):
                if b[i][j]:
                    p = b[i][j] ** 2 / normalizer
                    probability_sum += p
                    expected += p * lu(eliminate(b, i, j), k - 1)
        if probability_sum != 1:
            raise AssertionError("LU probabilities do not sum to one")
        return expected

    ec = chol(a, steps)
    el = lu(a, steps)
    return ec, el, {"cholesky_states": chol.cache_info().currsize,
                    "lu_states": lu.cache_info().currsize}


def interval_record(lower: Fraction, upper: Fraction) -> dict:
    if lower > upper:
        raise AssertionError("Reversed enclosure")
    return {"lower_fraction": rational_string(lower),
            "upper_fraction": rational_string(upper),
            "lower_decimal_display": decimal_string(lower),
            "upper_decimal_display": decimal_string(upper)}


def run(r: int, t: Fraction) -> dict:
    started = time.monotonic()
    a, lower, eps = family(r, t)
    frozen = tuple(tuple(row) for row in a)
    ec, el, states = exact_expectations(frozen, r)
    tr_scaled, vnorm = scaled_inverse_trace_and_rayleigh(lower, eps)
    lambda_lower = eps ** r / tr_scaled
    lambda_upper = eps ** r / vnorm
    chol_lo, chol_hi = ec / lambda_upper, ec / lambda_lower
    lu_lo, lu_hi = el / lambda_upper ** 2, el / lambda_lower ** 2
    if chol_lo > 2 ** r or lu_lo > 4 ** r:
        raise AssertionError("Exact lower enclosure violates a known universal upper bound")
    return {
        "r": r, "n": r + 1, "t": rational_string(t),
        "epsilon_exponent": (r + 1) ** 2,
        "arithmetic": "exact fractions; recursively enumerated rank-one pivot updates",
        "expected_trace_fraction": rational_string(ec),
        "expected_squared_error_fraction": rational_string(el),
        "lambda_min_enclosure": interval_record(lambda_lower, lambda_upper),
        "chol_ratio_enclosure": interval_record(chol_lo, chol_hi),
        "lu_ratio_enclosure": interval_record(lu_lo, lu_hi),
        **states, "elapsed_seconds": time.monotonic() - started,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--r", type=int, default=2)
    parser.add_argument("--t", default="1/100")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.r < 1 or args.r > 4:
        parser.error("This exhaustive checker is restricted to 1 <= r <= 4; use the certificate for larger r")
    try:
        t = Q(args.t)
        if not 0 < t < 1:
            raise ValueError("Require 0 < t < 1")
        if hasattr(sys, "set_int_max_str_digits"):
            sys.set_int_max_str_digits(0)
        result = run(args.r, t)
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    except (ValueError, ArithmeticError) as error:
        parser.exit(2, f"Enumeration failed: {error}\n")
    print(json.dumps({"r": args.r,
                      "chol_ratio_lower_display": result["chol_ratio_enclosure"]["lower_decimal_display"],
                      "lu_ratio_lower_display": result["lu_ratio_enclosure"]["lower_decimal_display"],
                      "cholesky_states": result["cholesky_states"],
                      "lu_states": result["lu_states"],
                      "elapsed_seconds": result["elapsed_seconds"]}, indent=2))


if __name__ == "__main__":
    main()
