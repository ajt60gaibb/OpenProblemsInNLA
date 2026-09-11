"""Check the row-replication identity with exact arithmetic on a small example.

The example has diagonal (4,1,1), so multiplicities (4,1,1) give a rational
isometric embedding. The replicated 6-by-6 matrix is unit-diagonal, PSD of
rank three, and entrywise positive. Both full pivot processes are enumerated.
This is a test of the identity, not a numerical proof of the general theorem.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import json
from pathlib import Path

from exact_certificate import rational_string
from exact_enumeration import exact_expectations, energy, trace
from rational_linalg import identity, multiply, transpose


def verify() -> dict:
    a = [[Q(x) for x in row] for row in ((4, 1, 1), (1, 1, Q(1, 2)), (1, Q(1, 2), 1))]
    p = [[Q(1, 2), Q(0), Q(0)] for _ in range(4)] + [
        [Q(0), Q(1), Q(0)], [Q(0), Q(0), Q(1)]]
    if multiply(transpose(p), p) != identity(3):
        raise AssertionError("The replication embedding is not an isometry")
    c = multiply(multiply(p, a), transpose(p))
    if any(c[i][i] != 1 for i in range(6)):
        raise AssertionError("The replica is not unit-diagonal")
    if not all(x > 0 for row in c for x in row):
        raise AssertionError("The replica is not entrywise positive")
    aa, cc = tuple(map(tuple, a)), tuple(map(tuple, c))
    if trace(aa) != trace(cc) or energy(aa) != energy(cc):
        raise AssertionError("Isometric replication changed trace or squared Frobenius norm")
    records = []
    for r in (1, 2):
        ec, el, states = exact_expectations(aa, r)
        ec_copy, el_copy, copy_states = exact_expectations(cc, r)
        if (ec, el) != (ec_copy, el_copy):
            raise AssertionError("Aggregating replica groups changed the expected error")
        records.append({"r": r, "expected_trace_fraction": rational_string(ec),
                        "expected_squared_error_fraction": rational_string(el),
                        "original_states": states, "replicated_states": copy_states})
    return {"arithmetic": "exact fractions", "source_dimension": 3,
            "replicated_dimension": 6, "multiplicities": [4, 1, 1],
            "unit_diagonal": True, "entrywise_positive": True, "rank": 3,
            "checks": records}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    result = verify()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
