"""Certify finite rational lower bounds near 2**r and 4**r.

This retains only the 2**r Cholesky / 4**r LU histories counted in the proof.
It computes exact maxima of their normalizers and bounds lambda_min by a
Rayleigh quotient of the inverse. It is not a Monte Carlo experiment.

Example:
    python exact_certificate.py --r 8 --t 1/100 --out results/exact_r8.json
"""
from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import sys
import time

from rational_linalg import (family, inverse, scaled_inverse_trace_and_rayleigh,
                             schur_residual, submatrix)

Q = Fraction


def rational_string(value: Fraction) -> str:
    return f"{value.numerator}/{value.denominator}"


def decimal_string(value: Fraction, digits: int = 30) -> str:
    """Display only. All comparisons/certificates use the Fraction itself."""
    with localcontext() as context:
        context.prec = digits
        return str(Decimal(value.numerator) / Decimal(value.denominator))


def certificate(r: int, t: Fraction, verbose: bool = True) -> dict:
    started = time.monotonic()
    a, lower, eps = family(r, t)
    n = r + 1
    _, vnorm = scaled_inverse_trace_and_rayleigh(lower, eps)
    trace_maxima: list[Fraction] = []
    norm_maxima: list[Fraction] = []
    blocks_checked = 0

    for s in range(r):
        # Every surviving prefix is an s-subset of {1,...,s,n} (one-based).
        domain = tuple(range(s)) + (n - 1,)
        good = [tuple(i for i in domain if i != omitted) for omitted in domain]
        max_trace = Q(0)
        max_norm = Q(0)
        for rows in good:
            b = schur_residual(a, rows, rows)
            if any(b[i][i] <= 0 for i in range(n - s)):
                raise AssertionError("A principal residual is not positive definite")
            normalized_trace = sum((b[i][i] for i in range(n - s)), Q(0)) / eps ** s
            max_trace = max(max_trace, normalized_trace)
        for rows, cols in product(good, repeat=2):
            b = schur_residual(a, rows, cols)
            normalized_norm = sum((x * x for row in b for x in row), Q(0)) / eps ** (2 * s)
            if normalized_norm <= 0:
                raise AssertionError("A retained history has zero residual norm")
            max_norm = max(max_norm, normalized_norm)
            blocks_checked += 1
        trace_maxima.append(max_trace)
        norm_maxima.append(max_norm)
        if verbose:
            print(f"r={r}, prefix={s}: max trace={decimal_string(max_trace, 12)}, "
                  f"max squared norm={decimal_string(max_norm, 12)}", file=sys.stderr, flush=True)

    # Also check all possible final retained blocks, so each last pivot is nonzero.
    final_sets = [tuple(i for i in range(n) if i != omitted) for omitted in range(n)]
    for rows, cols in product(final_sets, repeat=2):
        inverse(submatrix(a, rows, cols))
        blocks_checked += 1

    chol_lower = Q(2 ** r) * vnorm
    lu_lower = Q(4 ** r) * vnorm ** 2
    for value in trace_maxima:
        chol_lower /= value
    for value in norm_maxima:
        lu_lower /= value
    if not Q(0) < chol_lower <= Q(2 ** r) or not Q(0) < lu_lower <= Q(4 ** r):
        raise AssertionError("Certificate violates positivity or a known universal upper bound")

    return {
        "r": r, "n": n, "t": rational_string(t), "epsilon_exponent": n * n,
        "arithmetic": "exact fractions; decimal strings are for display only",
        "chol_lower_bound_decimal": decimal_string(chol_lower),
        "lu_lower_bound_decimal": decimal_string(lu_lower),
        "chol_lower_bound_fraction": rational_string(chol_lower),
        "lu_lower_bound_fraction": rational_string(lu_lower),
        "chol_sharp_supremum": 2 ** r, "lu_sharp_supremum": 4 ** r,
        "chol_above_99_percent_supremum": chol_lower > Q(99, 100) * 2 ** r,
        "lu_above_99_percent_supremum": lu_lower > Q(99, 100) * 4 ** r,
        "normalized_trace_maxima": [rational_string(x) for x in trace_maxima],
        "normalized_squared_norm_maxima": [rational_string(x) for x in norm_maxima],
        "v_norm_squared": rational_string(vnorm),
        "pivot_blocks_checked": blocks_checked,
        "elapsed_seconds": time.monotonic() - started,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--r", type=int, default=3)
    parser.add_argument("--t", default="1/100", help="Exact rational, e.g. 1/100")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    try:
        t = Q(args.t)
        if args.r < 1 or not 0 < t < 1:
            raise ValueError("Require r >= 1 and 0 < t < 1")
        if hasattr(sys, "set_int_max_str_digits"):
            sys.set_int_max_str_digits(0)  # Large exact rational certificates.
        result = certificate(args.r, t)
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    except (ValueError, ArithmeticError) as error:
        parser.exit(2, f"Certificate failed: {error}\n")
    print(json.dumps({k: result[k] for k in (
        "r", "t", "epsilon_exponent", "chol_lower_bound_decimal",
        "lu_lower_bound_decimal", "chol_above_99_percent_supremum",
        "lu_above_99_percent_supremum", "pivot_blocks_checked", "elapsed_seconds")}, indent=2))


if __name__ == "__main__":
    main()
