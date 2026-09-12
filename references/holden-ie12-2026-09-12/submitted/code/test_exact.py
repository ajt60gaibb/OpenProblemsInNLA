"""Exact, finite component checks. These tests are not a formal proof.

Uses only the Python standard library. Run: python code/test_exact.py
"""
from __future__ import annotations
from fractions import Fraction as F
import itertools
import random
import unittest
from weighted_matvec import (PatternCatalogue, WeightedMatvec, choose_k,
                             dense_product, encode_pattern,
                             floor_by_comparisons, pattern_weight)


class ExactChecks(unittest.TestCase):
    def test_pattern_encoding_and_cardinality(self):
        for k in range(1, 10):
            catalogue = PatternCatalogue(k)
            codes = [encode_pattern(s, k) for s in catalogue.patterns]
            self.assertEqual(len(codes), len(set(codes)))
            self.assertLessEqual(len(codes), 4**k)
            self.assertTrue(all(pattern_weight(s) <= k for s in catalogue.patterns))
            for descriptor in catalogue.descriptors:
                self.assertEqual(descriptor.tail_code,
                                 encode_pattern(descriptor.pattern[1:], k))

    def test_all_shifted_pattern_values(self):
        vector = [F(1, 3), F(-2, 5), F(7, 11), F(13, 2), F(-17, 19)]
        for k in range(1, 8):
            catalogue = PatternCatalogue(k)
            table = catalogue.table(vector)
            for j in range(len(vector)):
                for pattern in catalogue.patterns:
                    expected = sum(F(a) * vector[j + i]
                                   for i, a in enumerate(pattern)
                                   if j + i < len(vector))
                    self.assertEqual(table[j][encode_pattern(pattern, k)], expected)

    def test_exhaustive_packing_rows(self):
        alphabet = (-4, -1, 0, 1, 4)
        for k in range(1, 7):
            catalogue = PatternCatalogue(k)
            for length in range(1, 6):
                for row in itertools.product(alphabet, repeat=length):
                    compressed = WeightedMatvec([list(row)], k, catalogue)
                    self.assertLessEqual(k * compressed.term_count,
                                         2 * compressed.weight + k)

    def test_rational_matrix_products_and_transposes(self):
        rng = random.Random(271828)
        for n in (1, 2, 3, 5, 8, 13, 21):
            for k in range(1, 8):
                catalogue = PatternCatalogue(k)
                for trial in range(3):
                    alphabet = (-10000, -3, -1, 0, 0, 0, 1, 2, 1000000)
                    Z = [[rng.choice(alphabet) for _ in range(n)] for _ in range(n)]
                    vector = [F(rng.randint(-9, 9), rng.randint(1, 11)) for _ in range(n)]
                    c = WeightedMatvec(Z, k, catalogue)
                    self.assertEqual(c.apply(vector), dense_product(Z, vector))
                    Zt = [list(column) for column in zip(*Z)]
                    ct = WeightedMatvec(Zt, k, catalogue)
                    self.assertEqual(ct.apply(vector), dense_product(Zt, vector))
                    self.assertEqual(c.weight, ct.weight)

    def test_floor_without_primitive(self):
        values = [F(p, q) for p in range(-120, 121) for q in range(1, 14)]
        values += [F(-100001, 100), F(100001, 100)]
        for value in values:
            integer = floor_by_comparisons(value)
            self.assertLessEqual(integer, value)
            self.assertLess(value, integer + 1)

    def test_dimension_and_iteration_budget_inequalities(self):
        ns = list(range(1, 2049)) + [16**j + delta for j in range(1, 101)
                                   for delta in (-1, 0, 1)]
        for n in ns:
            k = choose_k(n)
            self.assertLess(n, 16**(k + 1))
            self.assertLessEqual(k * 4**k, 4 * n)
            ell, power = 0, 1
            while power < 10**9 * (n + 1):
                ell, power = ell + 1, 2 * power
            self.assertLessEqual(ell, 39 * k)
            for epsilon in (F(1, 3), F(1, 8), F(1, 10**6)):
                eta = epsilon / 8
                value = 4 * ell / eta**2
                cap = (value.numerator + value.denominator - 1) // value.denominator
                self.assertLessEqual(cap, 10000 * k / epsilon**2)
                self.assertLessEqual(2 + 64 / epsilon, 65 / epsilon)

    def test_kernel_filter_exact_rational_instances(self):
        # Diagonal B with an additional zero column: kernel coordinate is explicit.
        # No Gaussian simulation or floating-point eigenvalue calculation is used.
        for eta in (F(1, 2), F(1, 4), F(1, 8)):
            singular_values = [F(0), eta / 2, eta, F(1, 2), F(3, 2), F(0)]
            g = [F(1), F(-2), F(3), F(4), F(-5), F(2)]
            G2, a2 = sum(x*x for x in g), g[-1]**2
            ell, power = 0, F(1)
            while power < G2 / a2:
                power *= 2
                ell += 1
            ell = max(ell, 1)
            value = 4 * ell / eta**2
            cap = (value.numerator + value.denominator - 1) // value.denominator
            z = [(1 - sigma**2 / 4)**cap * x
                 for sigma, x in zip(singular_values, g)]
            residual2 = sum(sigma**2 * value**2
                            for sigma, value in zip(singular_values, z))
            norm2 = sum(value**2 for value in z)
            self.assertLessEqual(residual2, eta**2 * norm2)
            self.assertGreaterEqual(norm2, a2)

    def test_clamping_zero_and_both_signs_exactly(self):
        epsilon = F(1, 4)
        eta = epsilon / 8
        # ||u||=||c||=1, Q=diag(1,delta), u=e_2, c=e_1.
        for delta in (F(0), eta / 8, eta / 4):
            for alpha in (F(0), eta / 8, -eta / 8, eta / 4, -eta / 4):
                self.assertLessEqual(delta**2 + alpha**2,
                                     eta**2 * (1 + alpha**2))
                alpha_prime = max(abs(alpha), eta)
                if alpha < 0:
                    alpha_prime = -alpha_prime
                self.assertNotEqual(alpha_prime, 0)
                self.assertLessEqual(abs(alpha_prime - alpha), eta)
                # A=Q here; the squared backward error after scaling is exact.
                error2 = delta**2 + alpha_prime**2
                self.assertLessEqual(error2, (5 * epsilon / 8)**2)
                for beta in (F(1, 10**30), F(1), F(10**30)):
                    x2 = (beta / alpha_prime)**2
                    residual2 = beta**2 + delta**2 * x2
                    self.assertEqual(residual2 / x2, error2)
                    self.assertLessEqual(x2, (beta / eta)**2)

    def test_error_budget_constants(self):
        for epsilon in (F(1, 1000), F(1, 4), F(499, 1000)):
            rho = eta = epsilon / 8
            ratio_bound = (2 + rho) / (1 - eta)
            self.assertLess(ratio_bound, 3)
            self.assertLessEqual(rho + eta * ratio_bound + eta, 5 * epsilon / 8)
            self.assertLess(5 * epsilon / 8, epsilon)
            self.assertLess((1 + rho)**2 + 1, 4)


if __name__ == "__main__":
    unittest.main(verbosity=2)
