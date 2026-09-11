#!/usr/bin/env python3
"""Validate all small-order spectral witnesses and all cofactor dot certificates."""
import itertools
import json
import random
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from permanent import permanent, read_matrix, read_witnesses, write_matrix


def main() -> None:
    claims = json.loads((ROOT / "claims.json").read_text())
    total = 0
    for n in claims["ac12_verified_orders"]:
        expected = None
        for family in ("u", "o"):
            prefix = ROOT / "data" / "ac12" / f"{family}{n}"
            values = set(map(int, prefix.with_name(prefix.name + "_spectrum.txt").read_text().split()))
            witnesses = read_witnesses(prefix.with_name(prefix.name + "_witnesses.txt"))
            assert values == set(witnesses), (family, n, "catalogue mismatch")
            for value, a in witnesses.items():
                assert len(a) == n and abs(permanent(a)) == value, (family, n, value)
                if family == "u":
                    assert all(a[i][j] == 1 for i in range(n) for j in range(i))
                total += 1
            if expected is None:
                expected = values
            else:
                assert values == expected, (n, "range mismatch")
        print(f"PASS spectra and all witnesses: n={n}, absolute values={len(expected)}")
    for prefix in ("c8", "f7"):
        n = int(prefix[1:])
        witnesses = read_witnesses(ROOT / "data" / "ac12" / f"{prefix}_witnesses.txt")
        values = set(map(int, (ROOT / "data" / "ac12" / f"u{n}_spectrum.txt").read_text().split()))
        assert set(witnesses) == values
        for value, a in witnesses.items():
            assert abs(permanent(a)) == value
            total += 1
    print(f"PASS {total} spectral witness matrices checked with arbitrary-precision subset DP")
    for n in claims["ac11_verified_orders"]:
        a, value = read_matrix(ROOT / "data" / "ac11" / f"min{n}.txt")
        q = 1 << (n - ((n + 1).bit_length() - 1))
        assert len(a) == n and value == q
        tokens = (ROOT / "data" / "ac11" / f"min{n}_cofactors.txt").read_text().split()
        assert tokens[0] == "scale"
        scale, c = int(tokens[1]), list(map(int, tokens[2:]))
        assert len(c) == n and scale == 1 << ((n - 1) - (n.bit_length() - 1))
        assert scale * sum(x*y for x, y in zip(a[-1], c)) == q
        if n <= 12:
            assert permanent(a) == q
        print(f"PASS cofactor dot certificate n={n}; dot product only; full-matrix checks are separate")
    # A mathematically independent direct-permutation cross-check at small orders.
    rng = random.Random(20260911)
    verifier = ROOT / "build" / "verify_permanent"
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "matrix.txt"
        for n in range(1, 11):
            for trial in range(12):
                a = [[rng.choice((-1, 1)) for _ in range(n)] for _ in range(n)]
                value = permanent(a)
                if n <= 6:
                    brute = sum(__import__('math').prod(a[i][p[i]] for i in range(n)) for p in itertools.permutations(range(n)))
                    assert brute == value
                if verifier.exists():
                    write_matrix(path, a, value)
                    result = subprocess.run([str(verifier), str(path), str(1 + trial % 3)], capture_output=True, text=True)
                    assert result.returncode == 0, result.stdout + result.stderr
                    write_matrix(path, a, value + 2)
                    result = subprocess.run([str(verifier), str(path)], capture_output=True, text=True)
                    assert result.returncode != 0, "Checker accepted an incorrect claim"
        if verifier.exists():
            path.write_text("2 2\n1 1\n1 0\n")
            assert subprocess.run([str(verifier), str(path)], capture_output=True).returncode != 0
    print("PASS 120 random matrices, permutation cross-checks through n=6, wrong-claim tests, and input rejection")
    range_checker = ROOT / "build" / "check_range"
    if range_checker.exists():
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            for n, removed in ((4, 4), (8, 1280)):
                values = set(map(int, (ROOT / f"data/ac12/u{n}_spectrum.txt").read_text().split()))
                assert removed in values
                allowed = directory / f"incomplete{n}.txt"
                allowed.write_text("".join(f"{v}\n" for v in sorted(values - {removed})))
                result = subprocess.run([str(range_checker), str(n), str(allowed), str(directory / f"negative{n}")], capture_output=True, text=True)
                assert result.returncode == 1 and f"absolute_permanent={removed}" in result.stderr, result.stdout + result.stderr
            malformed = directory / "malformed.txt"
            malformed.write_text("33\n")
            result = subprocess.run([str(range_checker), "8", str(malformed), str(directory / "malformed_check")], capture_output=True, text=True)
            assert result.returncode == 2, result.stdout + result.stderr
        print("PASS range checker rejects omitted attainable values at orders 4 and 8 and malformed input")


if __name__ == "__main__":
    main()
