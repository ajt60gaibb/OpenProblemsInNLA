#!/usr/bin/env python3
"""Supplementary exact tests. None uses an optimization solver or float tolerance."""
from __future__ import annotations

from collections import Counter
from copy import deepcopy
import csv
from fractions import Fraction
import json
from math import comb
from pathlib import Path
import time

from factorization import build_certificate, rank_bound
from verify_certificate import CertificateError, require, verify

ROOT = Path(__file__).resolve().parents[1]

# Small exact polynomial algebra: (degree in p, degree in t) -> integer.
def add(*polys):
    out = Counter()
    for poly in polys:
        for key, value in poly.items():
            out[key] += value
    return {key: value for key, value in out.items() if value}


def scale(poly, coefficient):
    return {key: coefficient * value for key, value in poly.items() if coefficient * value}


def mul(left, right):
    out = Counter()
    for (i, j), a in left.items():
        for (k, ell), b in right.items():
            out[i + k, j + ell] += a * b
    return {key: value for key, value in out.items() if value}


def power(poly, exponent):
    out = {(0, 0): 1}
    for _ in range(exponent):
        out = mul(out, poly)
    return out


def constant(value):
    return {(0, 0): value} if value else {}


def polynomial_tests():
    p, t = {(1, 0): 1}, {(0, 1): 1}
    pm1, tm1 = add(p, constant(-1)), add(t, constant(-1))
    pmtm1 = add(p, scale(t, -1), constant(-1))
    lhs = add(mul(power(pm1, 2), power(tm1, 2)),
              scale(mul(power(tm1, 2), power(pmtm1, 2)), -1))

    def falling(k):
        out = constant(1)
        for j in range(k):
            out = mul(out, add(t, constant(-j)))
        return out

    rhs = add(scale(mul(add(p, constant(-2)), falling(2)), 2),
              scale(mul(add(p, scale(t, -1)), falling(3)), 2),
              falling(4))
    require(add(lhs, scale(rhs, -1)) == {}, "Polynomial identity failed")
    print("PASS: the bivariate polynomial identity holds coefficient by coefficient over Z.")
    # Positive-part four-set formula on its entire domain.
    for k in range(5):
        c3 = comb(k, 3) if k >= 3 else 0
        c4 = comb(k, 4) if k >= 4 else 0
        require(max(0, k - 2) == c3 - 2 * c4, "Four-set identity failed")
    print("PASS: four-set row function is 0,0,0,1,2 and is nonnegative.")

    checked = 0
    for p_int in range(201):
        for t_int in range(p_int + 1):
            c2 = comb(t_int, 2) if t_int >= 2 else 0
            c3 = comb(t_int, 3) if t_int >= 3 else 0
            c4 = comb(t_int, 4) if t_int >= 4 else 0
            d = max(1, (p_int - 1) ** 2)
            core = (t_int - 1) ** 2 * (p_int - t_int - 1) ** 2
            singleton = (1 - t_int) if p_int == 1 else 0
            pair = 4 * (p_int - 2) * c2
            four = 12 * ((p_int - t_int) * c3 + 2 * c4)
            require(min(core, singleton, pair, four) >= 0, "Negative summand")
            require(core + singleton + pair + four == d * (t_int - 1) ** 2,
                    "Integer-domain identity failed")
            checked += 1
    print(f"PASS: all {checked} integer pairs 0<=t<=p<=200, including p=0,1,2.")

    require(rank_bound(7) == 127, "Wrong n=7 count")
    for n in range(7, 1001):
        P = lambda m: m + comb(m, 2) + comb(m, 4)
        require(P(n + 1) - 2 * P(n) == 1 - comb(n, 2) + comb(n, 3) - comb(n, 4),
                "Pascal recurrence failed")
        require(rank_bound(n) < (1 << n), "Strict upper-bound test failed")
    print("PASS: base count and Pascal recurrence tests; the report proves strictness for every n>=7.")


def csv_and_rational_tests(certificate):
    def read_rows(name, parser=int):
        with (ROOT / "data" / name).open(newline="", encoding="utf-8") as stream:
            return [[parser(value) for value in row] for row in csv.reader(stream)]
    W = read_rows("W_n7.csv")
    H_scaled = read_rows("H_scaled_n7.csv")
    d_rows = read_rows("column_denominators_n7.csv")
    H = read_rows("H_n7_rational.csv", Fraction)
    require(W == certificate["W"] and H_scaled == certificate["H_scaled"],
            "CSV/JSON factor mismatch")
    require(d_rows == [certificate["denominators"]], "CSV/JSON denominator mismatch")
    d = d_rows[0]
    require(len(H) == 127 and all(len(row) == 128 for row in H), "Wrong rational shape")
    for k, row in enumerate(H):
        for b, value in enumerate(row):
            require(value == Fraction(H_scaled[k][b], d[b]), "Incorrect rational CSV value")
    for a, row in enumerate(W):
        product = [Fraction(0) for _ in range(128)]
        for k, coefficient in enumerate(row):
            if coefficient:
                for b, value in enumerate(H[k]):
                    product[b] += coefficient * value
        for b, value in enumerate(product):
            require(value == (1 - (a & b).bit_count()) ** 2, "Unscaled rational product failed")
    print("PASS: all CSV files agree with JSON; all 16384 entries of the unscaled rational W H equal C_7.")


def mutation_tests(certificate):
    def rejected(mutator, label):
        damaged = deepcopy(certificate)
        mutator(damaged)
        try:
            verify(damaged)
        except CertificateError:
            print(f"PASS: rejected damaged certificate ({label}).")
            return
        raise RuntimeError(f"Damaged certificate was accepted: {label}")
    rejected(lambda c: c["W"][0].__setitem__(0, -1), "negative factor entry")
    rejected(lambda c: c["H_scaled"][0].__setitem__(0, 2), "incorrect positive factor entry")
    rejected(lambda c: c["denominators"].__setitem__(0, 0), "zero denominator")
    rejected(lambda c: c["denominators"].__setitem__(127, 35), "wrong positive denominator")
    rejected(lambda c: c["W"][0].pop(), "truncated row")
    rejected(lambda c: c["H_scaled"][0].__setitem__(0, 1.0), "floating-point entry")


def main():
    started = time.monotonic()
    polynomial_tests()
    certificate = json.loads((ROOT / "data" / "factors_n7.json").read_text())
    require(certificate == build_certificate(7), "Stored certificate differs from closed-form generator")
    print("PASS: exact regeneration of the complete n=7 JSON certificate.")
    total = 0
    for n in range(1, 10):
        c = build_certificate(n)
        result = verify(c, require_strict=n >= 7)
        total += result["checked_entries"]
        print(f"PASS: n={n}, {result['checked_entries']} exact entries, r={c['r']}.")
    print(f"PASS: {total} complete matrix entries checked across n=1,...,9.")
    csv_and_rational_tests(certificate)
    mutation_tests(certificate)
    print("ALL SELF-TESTS PASSED.")
    print(f"Elapsed seconds: {time.monotonic() - started:.6f}")


if __name__ == "__main__":
    main()
