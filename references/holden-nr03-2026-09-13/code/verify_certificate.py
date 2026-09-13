#!/usr/bin/env python3
"""Check an explicit NR-03 certificate without importing its construction.

The check is purely integer arithmetic: W H_scaled = C_n diag(d), d>0.
No optimization, random sampling, tolerances, or third-party packages.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import time
from typing import Any


class CertificateError(ValueError):
    """A malformed or mathematically incorrect certificate."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CertificateError(message)


def verify(certificate: dict[str, Any], require_strict: bool = True) -> dict[str, Any]:
    n, r = certificate.get("n"), certificate.get("r")
    require(type(n) is int and 1 <= n <= 12, "Expected integer n in [1,12]")
    require(type(r) is int and r > 0, "Expected a positive integer inner dimension")
    size = 1 << n
    if require_strict:
        require(r < size, "Inner dimension is not strictly smaller than 2**n")
    W, H, d = (certificate.get("W"), certificate.get("H_scaled"),
               certificate.get("denominators"))
    require(isinstance(W, list) and len(W) == size, "Wrong left-factor row count")
    require(isinstance(H, list) and len(H) == r, "Wrong right-factor row count")
    require(isinstance(d, list) and len(d) == size, "Wrong denominator count")
    for b, value in enumerate(d):
        require(type(value) is int and value > 0, f"Nonpositive/noninteger denominator at {b}")
    for name, matrix, width in (("W", W, r), ("H_scaled", H, size)):
        for i, row in enumerate(matrix):
            require(isinstance(row, list) and len(row) == width, f"Wrong row width in {name}[{i}]")
            for j, value in enumerate(row):
                require(type(value) is int and value >= 0, f"Negative/noninteger {name}[{i}][{j}]")

    positive_entries = 0
    maximum_scaled_entry = 0
    for a, row in enumerate(W):
        # This is exact sparse matrix multiplication; zero terms are skipped.
        product = [0] * size
        for coefficient, right in zip(row, H):
            if coefficient:
                for b, value in enumerate(right):
                    product[b] += coefficient * value
        for b, actual in enumerate(product):
            prescribed = (1 - (a & b).bit_count()) ** 2
            expected = prescribed * d[b]
            require(actual == expected,
                    f"Entry ({a},{b}) is wrong: product={actual}, expected={expected}")
            positive_entries += prescribed > 0
            maximum_scaled_entry = max(maximum_scaled_entry, expected)
    return {
        "n": n, "rows": size, "columns": size, "terms": r,
        "checked_entries": size * size,
        "positive_target_entries": positive_entries,
        "zero_target_entries": size * size - positive_entries,
        "maximum_scaled_target_entry": maximum_scaled_entry,
        "maximum_W_entry": max(max(row) for row in W),
        "maximum_H_scaled_entry": max(max(row) for row in H),
        "denominator_values": sorted(set(d)),
        "arithmetic": "Exact arbitrary-precision integers",
        "strict_counterexample": r < size,
        "result": "PASS",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" / "factors_n7.json")
    parser.add_argument("--allow-nonstrict", action="store_true")
    args = parser.parse_args()
    started = time.monotonic()
    with args.certificate.open(encoding="utf-8") as stream:
        certificate = json.load(stream)
    result = verify(certificate, require_strict=not args.allow_nonstrict)
    print(json.dumps(result, indent=2))
    print(f"Elapsed seconds: {time.monotonic() - started:.6f}")


if __name__ == "__main__":
    main()
