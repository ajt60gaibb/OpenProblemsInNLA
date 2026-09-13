"""Standard-library exact check of the saved positive frozen-exception example.

This verifies the returned rows/weights and every quartic moment. It is NOT
an implementation or certificate of the asymptotic discrepancy theorem.
"""
from __future__ import annotations

if not __debug__:
    raise RuntimeError("Verification requires assertions: run Python without -O or PYTHONOPTIMIZE.")

from fractions import Fraction
from pathlib import Path
import json
import sys


def exponents(dimension: int, degree: int):
    if dimension == 1:
        yield (degree,)
        return
    for j in range(degree+1):
        for rest in exponents(dimension-1, degree-j):
            yield (j,) + rest


def monomial(row, powers):
    out = 1
    for value, power in zip(row, powers):
        out *= value ** power
    return out


def check(path: Path) -> dict:
    obj = json.loads(path.read_text())
    rows = obj['rows']
    weights = [Fraction(x) for x in obj['weights']]
    n = len(rows)
    d = len(rows[0])
    assert n == len(weights) == obj['original_rows']
    assert d == obj['dimension']
    assert all(len(row) == d and all(isinstance(x, int) for x in row) for row in rows)
    assert all(w >= 0 for w in weights)
    assert sum(weights) == n
    powers = list(exponents(d, 4))
    assert len(powers) + 1 == obj['moment_count_including_mass']
    for nu in powers:
        original = sum(monomial(row, nu) for row in rows)
        weighted = sum(w*monomial(row, nu) for w,row in zip(weights,rows))
        assert weighted == original
    kept = sum(w != 0 for w in weights)
    assert kept == obj['retained_rows'] < n
    for stage in obj['stages']:
        assert 0 <= stage['full_positive'] <= stage['copies_before']//2
        assert 0 <= stage['fractional_frozen'] <= len(powers)+1
        assert Fraction(stage['common_mass']) > 0
    return {
        'passed': True,
        'arithmetic': 'Python integers and fractions.Fraction only',
        'original_rows': n,
        'retained_rows': kept,
        'dimension': d,
        'quartic_moments_checked': len(powers),
        'total_mass_preserved': True,
        'all_weights_nonnegative': True,
        'scope': 'Finite exact output certificate, not a proof-assistant formalization or an asymptotic partial-coloring implementation.'
    }


if __name__ == '__main__':
    default = Path(__file__).resolve().parents[1]/'results'/'exact_fractional_freezing.json'
    print(json.dumps(check(Path(sys.argv[1]) if len(sys.argv)>1 else default), indent=2))
