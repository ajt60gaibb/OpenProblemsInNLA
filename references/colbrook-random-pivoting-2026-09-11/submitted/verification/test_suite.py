"""Regression checks for the accompanying proof and rational certificates.

Run: python test_suite.py
All checks use the standard library. The rank-eight certificate is regenerated,
not merely trusted because its JSON says it passed.
"""
from __future__ import annotations

from fractions import Fraction as Q
from itertools import permutations
import json
from pathlib import Path
import sys
import unittest

from exact_certificate import certificate
from exact_enumeration import exact_expectations, run as enumerate_family
from rational_linalg import (family, identity, inverse, multiply,
                             scaled_inverse_trace_and_rayleigh, schur_residual)
from verify_ra03_2x2 import verify
from verify_replication import verify as verify_replication

ROOT = Path(__file__).resolve().parent
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def determinant(a):
    if not a:
        return Q(1)
    b = [list(row) for row in a]
    value = Q(1)
    for j in range(len(b)):
        k = next((i for i in range(j, len(b)) if b[i][j]), None)
        if k is None:
            return Q(0)
        if k != j:
            b[k], b[j] = b[j], b[k]
            value = -value
        pivot = b[j][j]
        value *= pivot
        for i in range(j + 1, len(b)):
            factor = b[i][j] / pivot
            for k in range(j + 1, len(b)):
                b[i][k] -= factor * b[j][k]
    return value


def survives(history):
    prefix = set()
    for s, next_index in enumerate(history):
        if s + 1 in prefix:
            return False
        prefix.add(next_index)
    return True


def two_choices_rule(history):
    n = len(history) + 1
    used = set()
    for position, index in enumerate(history, start=1):
        if index in used or index not in set(range(1, position + 1)) | {n}:
            return False
        used.add(index)
    return True


class VerificationTests(unittest.TestCase):
    def test_two_by_two_counterexample(self):
        record = verify()
        self.assertEqual(Q(record["expected_squared_error"]), Q(18, 5))
        ec, el, _ = exact_expectations(((Q(2), Q(1)), (Q(1), Q(2))), 1)
        self.assertEqual(ec, Q(3, 2))
        self.assertEqual(el, Q(18, 5))

    def test_zero_lu_pivots_have_zero_probability(self):
        ec, el, _ = exact_expectations(((Q(2), Q(0)), (Q(0), Q(1))), 1)
        self.assertEqual(ec, Q(4, 3))
        self.assertEqual(el, Q(8, 5))

    def test_exact_zero_residual_stops_early(self):
        a = ((Q(1), Q(0), Q(0)), (Q(0), Q(0), Q(0)), (Q(0), Q(0), Q(0)))
        ec, el, _ = exact_expectations(a, 2)
        self.assertEqual((ec, el), (Q(0), Q(0)))

    def test_unit_diagonal_replication(self):
        actual = verify_replication()
        saved = json.loads((ROOT / "results" / "replication.json").read_text())
        self.assertEqual(actual, saved)
        self.assertEqual(Q(actual["checks"][1]["expected_trace_fraction"]), Q(4, 5))
        self.assertEqual(Q(actual["checks"][1]["expected_squared_error_fraction"]), Q(7296, 6325))

    def test_family_and_inverse_scale(self):
        for r in range(1, 5):
            a, lower, eps = family(r, Q(1, 100))
            n = r + 1
            self.assertEqual(eps, Q(1, 100) ** (n * n))
            self.assertEqual(determinant(lower), 1)
            self.assertEqual(determinant(a), eps ** (r * (r + 1) // 2))
            self.assertTrue(all(x > 0 for row in a for x in row))
            ai = inverse(a)
            self.assertEqual(multiply(a, ai), identity(n))
            scaled_trace, vnorm = scaled_inverse_trace_and_rayleigh(lower, eps)
            self.assertEqual(scaled_trace, eps ** r * sum((ai[i][i] for i in range(n)), Q(0)))
            self.assertGreaterEqual(scaled_trace, vnorm)
            self.assertGreaterEqual(vnorm, 1)

    def test_count_and_equivalent_conditions(self):
        for r in range(1, 8):
            count = 0
            for history in permutations(range(1, r + 2), r):
                good = survives(history)
                self.assertEqual(good, two_choices_rule(history))
                count += int(good)
            self.assertEqual(count, 2 ** r)
            self.assertEqual(count ** 2, 4 ** r)

    def test_exact_history_cancellation_independent_of_family(self):
        a = [[Q(x) for x in row] for row in ((4, 1, 2), (1, 3, 1), (2, 1, 5))]
        r = 2
        det = determinant(a)
        self.assertEqual(det, 43)
        ec, el, _ = exact_expectations(tuple(tuple(row) for row in a), r)
        histories = list(permutations(range(3), r))
        chol_sum = Q(0)
        lu_sum = Q(0)
        for history in histories:
            term = det
            for s in range(r):
                selected = tuple(sorted(history[:s]))
                b = schur_residual(a, selected, selected)
                term /= sum((b[i][i] for i in range(len(b))), Q(0))
            chol_sum += term
        for rows in histories:
            for cols in histories:
                term = det ** 2
                for s in range(r):
                    b = schur_residual(a, tuple(sorted(rows[:s])), tuple(sorted(cols[:s])))
                    term /= sum((x * x for row in b for x in row), Q(0))
                lu_sum += term
        self.assertEqual(ec, chol_sum)
        self.assertEqual(el, lu_sum)

    def test_regenerate_small_exhaustive_records(self):
        for r in (2, 3):
            actual = enumerate_family(r, Q(1, 100))
            saved = json.loads((ROOT / "results" / f"enumeration_r{r}.json").read_text())
            for key in ("expected_trace_fraction", "expected_squared_error_fraction",
                        "lambda_min_enclosure", "chol_ratio_enclosure", "lu_ratio_enclosure"):
                self.assertEqual(actual[key], saved[key])
            self.assertGreater(Q(actual["chol_ratio_enclosure"]["lower_fraction"]), Q(99, 100) * 2 ** r)
            self.assertGreater(Q(actual["lu_ratio_enclosure"]["lower_fraction"]), Q(99, 100) * 4 ** r)

    def test_regenerate_finite_certificates(self):
        for r in (3, 8):
            actual = certificate(r, Q(1, 100), verbose=False)
            saved = json.loads((ROOT / "results" / f"exact_r{r}.json").read_text())
            for key in ("epsilon_exponent", "chol_lower_bound_fraction", "lu_lower_bound_fraction",
                        "normalized_trace_maxima", "normalized_squared_norm_maxima", "v_norm_squared",
                        "pivot_blocks_checked"):
                self.assertEqual(actual[key], saved[key])
            self.assertTrue(actual["chol_above_99_percent_supremum"])
            self.assertTrue(actual["lu_above_99_percent_supremum"])

    def test_input_validation(self):
        for r, t in ((0, Q(1, 2)), (2, Q(0)), (2, Q(1)), (True, Q(1, 2))):
            with self.assertRaises(ValueError):
                family(r, t)
        with self.assertRaises(ArithmeticError):
            inverse([[Q(1), Q(1)], [Q(1), Q(1)]])


if __name__ == "__main__":
    unittest.main(verbosity=2)
