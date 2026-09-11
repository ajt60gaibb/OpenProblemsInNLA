#!/usr/bin/env python3
"""Construct a triangular-negative realization for the certified finite orders."""
import argparse
import json
from pathlib import Path
from permanent import permanent, read_matrix, read_witnesses, write_matrix


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="Matrix file; its supplied claim is ignored")
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    certified = json.loads((root / "claims.json").read_text())["ac12_verified_orders"]
    a, _ = read_matrix(args.input)
    n = len(a)
    if n not in certified:
        parser.error(f"Certified orders in this package: {certified}")
    value = permanent(a)
    catalogue = read_witnesses(root / "data" / "ac12" / f"u{n}_witnesses.txt")
    b = catalogue[abs(value)]
    got = permanent(b)
    if got != value:
        b[0] = [-x for x in b[0]]
    if any(b[i][j] != 1 for i in range(n) for j in range(i)) or permanent(b) != value:
        raise RuntimeError("Catalogue realization failed verification")
    write_matrix(args.output, b, value)
    print(f"Verified realization: n={n}, permanent={value}")


if __name__ == "__main__":
    main()
