"""Regression tests, including independent arithmetic and a feasible control."""
from __future__ import annotations
import copy
from itertools import combinations
import json
from pathlib import Path
import random
import unittest
import numpy as np
from geometry import (positive_span_table, canonical_cycle, enumerate_spheres,
                      enumerate_cycles, selected_patterns)
from algebra import IncidenceTest, rref, nullspace
from regular_polygon import exact_expressions, Entry
from verify_exact import verify_factors, verify_file
from verify_all import exact_control_ranks

ROOT = Path(__file__).resolve().parents[1]


def plain_rank(rows, prime):
    """Independent list-based Gaussian elimination, not the Numba routine."""
    rows = [[int(x) % prime for x in row] for row in rows]
    if not rows:
        return 0
    m, n, rank = len(rows), len(rows[0]), 0
    for col in range(n):
        pivot = next((i for i in range(rank, m) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inv = pow(rows[rank][col], -1, prime)
        rows[rank] = [(x * inv) % prime for x in rows[rank]]
        for i in range(rank + 1, m):
            scale = rows[i][col]
            rows[i] = [(x - scale * y) % prime for x, y in zip(rows[i], rows[rank])]
        rank += 1
        if rank == m:
            break
    return rank


def plain_determinant(rows, prime):
    rows = [[int(x) % prime for x in row] for row in rows]
    result = 1
    for col in range(len(rows)):
        pivot = next((i for i in range(col, len(rows)) if rows[i][col]), None)
        if pivot is None:
            return 0
        if pivot != col:
            rows[col], rows[pivot] = rows[pivot], rows[col]
            result = -result
        value = rows[col][col]
        result = result * value % prime
        for i in range(col + 1, len(rows)):
            scale = rows[i][col] * pow(value, -1, prime) % prime
            rows[i] = [(x - scale * y) % prime for x, y in zip(rows[i], rows[col])]
    return result % prime


class ProofPipelineTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spheres = json.loads((ROOT / 'data/spheres8.json').read_text())
        cls.cycles = json.loads((ROOT / 'data/shadow_cycles.json').read_text())
        cls.patterns = {n: json.loads((ROOT / f'data/patterns_n{n}.json').read_text()) for n in (17, 18, 19)}

    def test_01_catalogue_regeneration(self):
        self.assertEqual(enumerate_spheres(), self.spheres)

    def test_02_shadow_cover_regeneration(self):
        cycles, summary = enumerate_cycles(self.spheres)
        self.assertEqual(cycles, self.cycles)
        self.assertEqual(summary['total_states_checked'], 14837760)
        self.assertEqual(summary['maximum_positive_tetrahedra'], 19)

    def test_03_positive_span_independent_circuit_check(self):
        table = positive_span_table()
        for sigma in range(128):
            signs = [1] + [-1 if (sigma >> i) & 1 else 1 for i in range(7)]
            vectors = [(signs[i], signs[i] * i) for i in range(8)]
            positive_triples = []
            def det(a, b): return a[0] * b[1] - a[1] * b[0]
            for a, b, c in combinations(range(8), 3):
                coeff = (det(vectors[b], vectors[c]), -det(vectors[a], vectors[c]), det(vectors[a], vectors[b]))
                if min(coeff) > 0 or max(coeff) < 0:
                    positive_triples.append((1 << a) | (1 << b) | (1 << c))
            for mask in range(256):
                expected = any(mask & triangle == triangle for triangle in positive_triples)
                self.assertEqual(bool(table[sigma, mask]), expected)

    def test_04_cycle_canonicalization_invariance(self):
        rng = random.Random(70331)
        for item in self.cycles[::19]:
            cycle = item['cycle']
            perm = list(range(8)); rng.shuffle(perm)
            mapped = [sum(1 << perm[j] for j in range(8) if f & (1 << j)) for f in cycle]
            shift = rng.randrange(len(mapped)); mapped = mapped[shift:] + mapped[:shift]
            self.assertEqual(canonical_cycle(cycle), canonical_cycle(mapped[::-1]))

    def test_05_selected_pattern_cover(self):
        for n in (17, 18, 19):
            self.assertEqual(selected_patterns(self.cycles, n), self.patterns[n])

    def test_06_laplace_coefficients_against_determinants(self):
        rng = random.Random(19017)
        for gauge in ((0, 1, 2), (2, 7, 13)):
            tester = IncidenceTest(17, 103, gauge)
            heights = [[0, 0] if j in gauge else [rng.randrange(103), rng.randrange(103)] for j in range(17)]
            bivector = np.array([(heights[a][0] * heights[b][1] - heights[a][1] * heights[b][0]) % 103 for a, b in tester.pairs], np.int64)
            for five in rng.sample(list(combinations(range(17), 5)), 50):
                mask = sum(1 << j for j in five)
                expansion = int(tester.rows[tester.row_ids[mask]] @ bivector) % 103
                matrix = [[1, tester.t[j], pow(tester.t[j], -1, 103)] + heights[j] for j in five]
                self.assertEqual(expansion, plain_determinant(matrix, 103))

    def test_07_gaussian_elimination_independent(self):
        rng = np.random.default_rng(332)
        for m, n in ((1, 1), (7, 9), (9, 7), (12, 12)):
            for _ in range(10):
                a = rng.integers(0, 103, (m, n), dtype=np.int64)
                if m > 1: a[-1] = a[0]
                self.assertEqual(len(rref(a, 103)[0]), plain_rank(a, 103))
                basis = nullspace(a, 103)
                self.assertFalse(np.any(a @ basis % 103))

    def test_08_reduced_equations_cross_check(self):
        tester = IncidenceTest(17, 137, (2, 7, 13))
        for pattern in self.patterns[17][::211]:
            a = tester.incidence_matrix(pattern['cycle'], False)
            b = tester.incidence_matrix(pattern['cycle'], True)
            self.assertEqual(len(rref(a, 137)[0]), len(rref(b, 137)[0]))

    def test_09_known_feasible_16_gon_is_not_excluded(self):
        control = json.loads((ROOT / 'checks/release/n16_positive_control.json').read_text())
        self.assertEqual(exact_control_ranks(), (6, 5))
        result = IncidenceTest(16, 97).check(control['active_masks'])
        self.assertFalse(result['excluded_as_a_bounded_lift'])
        self.assertEqual((result['quadratic_rank'], result['quadratic_target']), (10, 11))

    def test_10_invalid_incidence_is_rejected(self):
        cycle = self.patterns[17][0]['cycle'].copy()
        cycle[1] = cycle[0]
        with self.assertRaises(ValueError):
            IncidenceTest(17, 103).check(cycle)

    def test_11_exact_upper_certificates(self):
        for n in range(17, 21):
            result = verify_file(str(ROOT / f'data/upper/n{n}_rank9.json'))
            self.assertEqual(result['factors'], 9)
            self.assertTrue(result['exact_polynomial_identity'])

    def test_12_corrupted_upper_certificate_is_rejected(self):
        w, h = exact_expressions(17)
        w = copy.deepcopy(w)
        w[0][0] = Entry('one') if w[0][0].kind == 'zero' else Entry('zero')
        with self.assertRaises(AssertionError):
            verify_factors(17, w, h)

    def test_13_release_rank_records_cover_every_pattern(self):
        total = 0
        for n, primes in ((17, (103, 137)), (18, (109, 163)), (19, (191, 229))):
            for prime in primes:
                records = json.loads((ROOT / f'checks/release/algebra_n{n}_p{prime}.json').read_text())
                self.assertEqual(len(records), len(self.patterns[n]))
                self.assertEqual([r['pattern_index'] for r in records], list(range(len(records))))
                self.assertTrue(all(r['excluded_as_a_bounded_lift'] for r in records))
                total += len(records)
        self.assertEqual(total, 13220)


if __name__ == '__main__':
    unittest.main(verbosity=2)
