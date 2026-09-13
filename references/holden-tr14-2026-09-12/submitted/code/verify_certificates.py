#!/usr/bin/env python3
"""Exact characteristic-zero verification of implicit root decompositions."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import time

from binary_certificate import binary_certificate, verify_certificate
from verify_solution import jet_moments


def run_checks():
    cases = [
        ("single_jet", 3, 3, jet_moments(6, (3,))),
        ("two_double_points", 5, 3, jet_moments(10, (2, 2))),
        ("double_plus_simple", 5, 3, jet_moments(10, (2, 1, 1))),
        ("balanced", 5, 3, jet_moments(10, (6,))),
        ("reduced", 3, 4, jet_moments(9, (1, 1, 1, 1, 1))),
        ("mixed_three_supports", 3, 5, jet_moments(12, (3, 2, 1))),
        ("rational_unit", 3, 3, ["7/3", "-2/5", "11/7", 0, 0, 0, 0]),
        ("infinity_mixed", 3, 3, list(reversed(jet_moments(6, (2, 1))))),
        ("infinity_pure", 3, 3, [0, 0, 0, 0, 0, 0, 1]),
        ("infinity_balanced", 3, 3, list(reversed(jet_moments(6, (4,))))),
    ]
    records = []
    for name, m, n, h in cases:
        cert = binary_certificate(m, n, h)
        report = verify_certificate(cert, full_tensor=True)
        records.append({"name": name, "m": m, "n": n,
                        "shear": cert["finite_chart_shear"],
                        "ordinary_rank": cert["ranks"]["ordinary_rank"],
                        "vandermonde_rank": cert["summands"],
                        "certificate_optimal_for_ordinary_rank": cert["optimal_ordinary_and_symmetric"],
                        "verification": report})
        print("PASS", name, report, flush=True)
    return {"status": "PASS", "scope": "Exact characteristic-zero decomposition certificates; not proof of universal lower bound",
            "cases": len(records),
            "original_tensor_entries_checked": sum(x["verification"]["original_tensor_entries_checked"] for x in records),
            "records": records}


def main():
    if not __debug__:
        raise RuntimeError("Run verification without the Python -O optimization flag.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    start = time.monotonic()
    report = run_checks()
    report["elapsed_seconds"] = round(time.monotonic()-start, 2)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+"\n")
    print("PASS", report["cases"], "certificates;", report["original_tensor_entries_checked"], "tensor entries")


if __name__ == "__main__":
    main()
