"""Deterministic implementation and algebra checks; not a proof by simulation."""
import math
import unittest
import numpy as np
from re06 import (QueryPlan, theorem_parameters, make_theorem_plan,
                  make_sketch_plan, collect_answers, postprocess, approximate)


class LoggedOracle:
    def __init__(self, A):
        self.A = A
        self.log = []
    def right(self, v):
        self.log.append(("A", v.copy()))
        return self.A @ v
    def left(self, v):
        self.log.append(("AT", v.copy()))
        return self.A.T @ v


class RE06Tests(unittest.TestCase):
    def setUp(self):
        self.rng = np.random.default_rng(871)

    def test_parameter_rounding_and_bound(self):
        for M in [2, 3, 4, 17, 1000, 2**100, 2**1000]:
            for eps in [0.499, 0.2, 0.03, 1e-6]:
                p = theorem_parameters(M, eps)
                self.assertGreaterEqual(p.r**2, p.L)
                self.assertLessEqual(p.total, 4_000_000 * math.sqrt(math.log(2*M)) / eps**2)
                self.assertGreater(p.k, p.r + 1)
                self.assertGreater(p.ell, p.k + 1)

    def test_scalar_exact_case(self):
        A = np.array([[1.1]])
        family = [np.array([[0.0]]), np.array([[1.0]])]
        oracle = LoggedOracle(A)
        result = approximate(family, 1, 0.2, oracle.right, oracle.left)
        self.assertEqual(result.selected_index, 1)
        self.assertEqual(result.oracle_calls, 1)

    def test_exact_recovery_branch(self):
        n = 12
        A = self.rng.normal(size=(n,n))
        family = [self.rng.normal(size=(n,n)) for _ in range(6)]
        oracle = LoggedOracle(A)
        result = approximate(family, n, 0.25, oracle.right, oracle.left)
        exact_index = int(np.argmin([np.linalg.norm(A-b) for b in family]))
        self.assertEqual(result.selected_index, exact_index)
        np.testing.assert_array_equal(result.surrogate, A)

    def test_plan_is_independent_of_target(self):
        n = 40
        family = [np.zeros((n,n)), np.eye(n)]
        plan = make_sketch_plan(n, 3, 6, 12, seed=100)
        logs = []
        for A in family:
            oracle = LoggedOracle(A)
            answers = collect_answers(plan, oracle.right, oracle.left)
            postprocess(plan, answers, family)
            self.assertEqual(len(oracle.log), plan.query_count)
            for (side, v), (side0, v0) in zip(oracle.log, plan.queries()):
                self.assertEqual(side, side0)
                np.testing.assert_array_equal(v, v0)
            logs.append(oracle.log)
        for (s0,v0),(s1,v1) in zip(*logs):
            self.assertEqual(s0,s1)
            np.testing.assert_array_equal(v0,v1)

    def test_noiseless_candidate_in_sketch_mode(self):
        n = 32
        family = [self.rng.normal(size=(n,n)) for _ in range(5)]
        A = family[3]
        oracle = LoggedOracle(A)
        plan = make_sketch_plan(n, 4, 6, 12, seed=71)
        result = postprocess(plan, collect_answers(plan, oracle.right, oracle.left), family)
        self.assertEqual(result.warm_index, 3)
        self.assertEqual(result.selected_index, 3)
        np.testing.assert_allclose(result.surrogate, A, atol=1e-11)

    def test_exact_low_rank_residual_reconstruction(self):
        n = 36
        A = self.rng.normal(size=(n,3)) @ self.rng.normal(size=(3,n))
        # The first candidate wins by a very large margin.
        family = [np.zeros((n,n)), 1e8*np.eye(n)]
        plan = make_sketch_plan(n, 3, 7, 14, seed=11)
        oracle = LoggedOracle(A)
        result = postprocess(plan, collect_answers(plan, oracle.right, oracle.left), family)
        self.assertEqual(result.warm_index, 0)
        np.testing.assert_allclose(result.surrogate, A, rtol=1e-11, atol=1e-11)

    def test_tail_repair_can_fix_a_bad_warm_start(self):
        # G0 deliberately misses a rank-one discrepancy. This is a mechanism
        # test, not a sample from the first-sketch distribution in the theorem.
        n = 48
        A = 0.01*np.eye(n)
        bad = np.zeros((n,n)); bad[0,0] = 10.0
        family = [bad, np.zeros((n,n))]
        base = make_sketch_plan(n, 1, 10, 22, seed=51)
        g0 = np.zeros((n,1)); g0[1,0] = 1.0
        plan = QueryPlan(n, 'sketch', g0, base.G1, base.H)
        oracle = LoggedOracle(A)
        result = postprocess(plan, collect_answers(plan, oracle.right, oracle.left), family)
        self.assertEqual(result.warm_index, 0)
        self.assertEqual(result.selected_index, 1)
        self.assertGreater(np.linalg.norm(A-bad) / np.linalg.norm(A), 100.0)

    def test_low_rank_deterministic_majorant(self):
        n,r,k,ell = 25,3,9,17
        for _ in range(15):
            C = self.rng.normal(size=(n,n))
            Omega = self.rng.normal(size=(n,k))
            H = self.rng.normal(size=(n,ell))
            U,s,Vt = np.linalg.svd(C, full_matrices=True)
            Om = Vt @ Omega
            T = (s[r:,None] * Om[r:]) @ np.linalg.pinv(Om[:r])
            X = np.linalg.norm(T,'fro')**2
            Q = np.linalg.svd(C@Omega,full_matrices=False)[0]
            R = C-Q@(Q.T@C)
            Z = np.linalg.pinv(H.T@Q) @ (H.T@R)
            Chat = Q @ (np.linalg.pinv(H.T@Q) @ (H.T@C))
            tail = np.sum(s[r:]**2)
            self.assertLessEqual(np.linalg.norm(R)**2, tail+X+1e-9)
            self.assertAlmostEqual(np.linalg.norm(C-Chat)**2,
                                   np.linalg.norm(R)**2+np.linalg.norm(Z)**2, places=8)

    def test_final_triangle_bound(self):
        n = 30
        for seed in range(6):
            A = self.rng.normal(size=(n,n))
            family = [self.rng.normal(size=(n,n)) for _ in range(8)]
            plan = make_sketch_plan(n, 4, 8, 16, seed)
            oracle = LoggedOracle(A)
            result = postprocess(plan, collect_answers(plan, oracle.right, oracle.left), family)
            opt = min(np.linalg.norm(A-b) for b in family)
            lhs = np.linalg.norm(A-family[result.selected_index])
            rhs = 2*np.linalg.norm(A-result.surrogate)+opt
            self.assertLessEqual(lhs, rhs+1e-10)

    def test_probability_and_scalar_constants(self):
        p = math.exp(-8)+2*math.exp(-16)+1/128+1/524288
        self.assertLess(p, .01)
        for eta in np.linspace(1e-7, 1/8, 200):
            self.assertLessEqual((1+eta)/math.sqrt(1-eta), 1+2*eta+1e-14)

    def test_input_validation(self):
        for m,eps in [(1,.1),(2,0),(2,.5),(2,float('nan'))]:
            with self.assertRaises(ValueError): theorem_parameters(m,eps)
        with self.assertRaises(ValueError): make_sketch_plan(20,2,8,9)


if __name__ == '__main__':
    unittest.main(verbosity=2)
