#!/usr/bin/env python3
"""Solve a small rational square system by the baseline exact CGLS algorithm.

This is NOT the input-sparsity algorithm requested by KE-01.  Fraction bit
sizes can grow quickly; this program is a correctness/reference implementation.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys

from exact_arithmetic import SparseMatrix, cgls_exact


def load_instance(path: Path):
    data = json.loads(path.read_text())
    n = data["n"]
    if not isinstance(n, int) or n < 1:
        raise ValueError("n must be a positive integer")
    entries = data["entries"]
    if not isinstance(entries, list):
        raise ValueError("entries must be a list of [row, column, rational] triples")
    a = SparseMatrix.from_coo(n, n, entries)
    b = [Fraction(value) for value in data["b"]]
    epsilon = Fraction(data.get("epsilon", "1/1000000"))
    cap = data.get("max_iterations", n)
    if not isinstance(cap, int) or cap < 0:
        raise ValueError("max_iterations must be a nonnegative integer")
    return a, b, epsilon, cap


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("--out", type=Path, help="Write JSON here instead of stdout")
    args = parser.parse_args()
    try:
        a, b, epsilon, cap = load_instance(args.input)
        result = cgls_exact(a, b, epsilon, max_iterations=cap)
        payload = {
            "method": "baseline_exact_CGLS_not_full_KE01",
            "converged": result.converged,
            "x": [str(value) for value in result.x],
            "iterations": result.iterations,
            "matvec_calls": result.matvec_calls,
            "residual_squared": str(result.residual_squared[-1]),
            "relative_residual_squared": str(
                result.residual_squared[-1] / result.residual_squared[0]),
            "epsilon": str(epsilon),
        }
        text = json.dumps(payload, indent=2) + "\n"
        if args.out:
            args.out.parent.mkdir(parents=True, exist_ok=True)
            args.out.write_text(text)
        else:
            print(text, end="")
        return 0 if result.converged else 2
    except (OSError, ValueError, TypeError, KeyError, ArithmeticError) as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
