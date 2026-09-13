"""Numerical and exact-symbolic checks; these are not formal proof verification."""
from __future__ import annotations
import math
import unittest
import numpy as np
import sympy as sp
from src.ra14 import (
    dense_oracle, orth, complete_basis, exact_via_columns,
    recover_promised_rank, block_krylov_lra, postprocess_symmetric,
    warm_start_pca, fejer_polynomial, sharp_overlap_instance,
    extract_padded_subspace, residual_norm, principal_overlap,
)


def inverse_sqrt(x: np.ndarray) -> np.ndarray:
    vals, vecs = np.linalg.eigh(x)
    return (vecs / np.sqrt(vals)) @ vecs.T


def valid_warm_start(n: int, k: int, eps: float,
                     rng: np.random.Generator, *, rotate: bool = True):
    """Generate a noncommuting graph satisfying the exact residual inequality."""
    top = 1 + 1.5*eps + np.linspace(0, 0.7, k)
    tail = np.linspace(-1, 1, n-k)
    tau = 1 + eps
    kk = rng.standard_normal((n-k, k))
    kk /= np.linalg.norm(kk, 2)
    graph = np.sqrt(tau*tau-tail*tail)[:, None] * kk
    graph /= np.sqrt(top*top-tau*tau)[None, :]
    z = np.vstack((np.eye(k), graph)) @ inverse_sqrt(np.eye(k)+graph.T@graph)
    eigs = np.r_[top, tail]
    a = np.diag(eigs)
    v = np.eye(n)[:, :k]
    if rotate:
        rotation = np.linalg.qr(rng.standard_normal((n, n)))[0]
        a = (rotation * eigs) @ rotation.T
        z, v = rotation @ z, rotation @ v
    return a, z, v, top, tail, graph


class OracleTests(unittest.TestCase):
    def setUp(self):
        self.rng = np.random.default_rng(7414)

    def test_individual_query_counts_and_transpose(self):
        a = self.rng.normal(size=(9, 9))
        oracle = dense_oracle(a)
        x = self.rng.normal(size=(9, 4))
        np.testing.assert_allclose(oracle.block(x), a@x)
        np.testing.assert_allclose(oracle.block(x, transpose=True), a.T@x)
        self.assertEqual(oracle.queries, 8)
        self.assertEqual(oracle.forward_queries, 4)
        self.assertEqual(oracle.transpose_queries, 4)

    def test_budget_validation_and_symmetry(self):
        oracle = dense_oracle(np.eye(4), max_queries=1)
        oracle.apply(np.ones(4))
        with self.assertRaises(RuntimeError):
            oracle.apply(np.ones(4))
        with self.assertRaises(ValueError):
            oracle.apply(np.ones(3))
        with self.assertRaises(ValueError):
            dense_oracle(np.triu(np.ones((4, 4))), symmetric=True)

    def test_exact_n_query_upper(self):
        for n, k in [(2, 1), (9, 4), (12, 11)]:
            a = self.rng.normal(size=(n, n))
            oracle = dense_oracle(a)
            z = exact_via_columns(oracle, k)
            self.assertEqual(oracle.queries, n)
            np.testing.assert_allclose(z.T@z, np.eye(k), atol=2e-12)
            optimum = np.linalg.svd(a, compute_uv=False)[k]
            self.assertAlmostEqual(residual_norm(a, z), optimum, places=10)

    def test_promised_rank_and_rank_deficiency(self):
        n, k = 15, 6
        for true_rank in [0, 1, k]:
            a = self.rng.normal(size=(n, true_rank)) @ self.rng.normal(size=(true_rank, n))
            oracle = dense_oracle(a)
            z = recover_promised_rank(oracle, k, self.rng)
            self.assertEqual(oracle.queries, k)
            self.assertLess(residual_norm(a, z), 2e-10)
            np.testing.assert_allclose(z.T@z, np.eye(k), atol=2e-12)

    def test_krylov_budget_and_accuracy(self):
        n, k, steps = 48, 3, 7
        l = np.linalg.qr(self.rng.normal(size=(n, n)))[0]
        r = np.linalg.qr(self.rng.normal(size=(n, n)))[0]
        singulars = np.r_[5, 4, 3, np.linspace(1, .05, n-k)]
        a = (l*singulars)@r.T
        oracle = dense_oracle(a)
        z = block_krylov_lra(oracle, k, steps, self.rng)
        self.assertLessEqual(oracle.queries, k*(2*steps+2))
        self.assertLessEqual(residual_norm(a, z), 1.000001)
        np.testing.assert_allclose(z.T@z, np.eye(k), atol=1e-10)

    def test_krylov_zero_input(self):
        oracle = dense_oracle(np.zeros((8, 8)))
        z = block_krylov_lra(oracle, 3, 5, self.rng)
        self.assertEqual(oracle.queries, 3)
        np.testing.assert_allclose(z.T@z, np.eye(3), atol=1e-12)

    def test_symmetric_ritz_budget(self):
        n, k, degree = 30, 2, 4
        a = self.rng.normal(size=(n, n))
        a = (a+a.T)/2
        z = np.linalg.qr(self.rng.normal(size=(n, k)))[0]
        oracle = dense_oracle(a, symmetric=True)
        result = postprocess_symmetric(oracle, z, degree)
        self.assertLessEqual(oracle.queries, k*(degree+1))
        self.assertGreaterEqual(np.trace(result.T@a@result)+1e-10, np.trace(z.T@a@z))
        np.testing.assert_allclose(result.T@result, np.eye(k), atol=1e-10)

    def test_symmetric_invariant_subspace_early_stop(self):
        a = np.diag(np.arange(1.0, 13.0))
        z = np.eye(12)[:, -3:]
        oracle = dense_oracle(a, symmetric=True)
        result = postprocess_symmetric(oracle, z, 100)
        self.assertEqual(oracle.queries, 3)
        np.testing.assert_allclose(result@result.T, z@z.T, atol=1e-12)


class MathematicalIdentityTests(unittest.TestCase):
    def setUp(self):
        self.rng = np.random.default_rng(9014)

    def test_sharp_overlap_and_pca_counterexample(self):
        for k in [1, 3, 8]:
            for eps in [1e-6, .001, .1, .49]:
                a, z, alpha2 = sharp_overlap_instance(k, eps)
                v = np.eye(2*k+1)[:, :k]
                self.assertAlmostEqual(residual_norm(a, z), 1+eps, places=11)
                self.assertAlmostEqual(principal_overlap(v, z), alpha2, places=12)
                captured = np.trace(z.T@a@z)/(k*(1+2*eps))
                self.assertAlmostEqual(captured, alpha2, places=12)

    def test_graph_residual_and_overlap(self):
        for eps in [.001, .02, .25, .49]:
            a, z, v, top, tail, graph = valid_warm_start(29, 5, eps, self.rng)
            res = residual_norm(a, z)
            self.assertLessEqual(res, 1+eps+2e-12)
            alpha2 = principal_overlap(v, z)
            self.assertGreaterEqual(alpha2+1e-12, 1-(res/top.min())**2)
            d1 = top**2-(1+eps)**2
            d2 = (1+eps)**2-tail**2
            delta = np.diag(d2)-(graph*d1)@graph.T
            self.assertGreaterEqual(np.linalg.eigvalsh(delta)[0], -1e-11)

    def test_fejer_polynomial_identity(self):
        x = sp.symbols('x')
        for m in range(1, 13):
            quotient = sp.div(sp.chebyshevt(m, x)-1, x-1)[0]
            expansion = m + 2*sum((m-j)*sp.chebyshevt(j, x) for j in range(1, m))
            self.assertEqual(sp.expand(quotient-expansion), 0)
            values = np.array([-1, -.7, 0, .2, .999, 1, 1.1])
            fn = sp.lambdify(x, quotient, 'numpy')
            np.testing.assert_allclose(fejer_polynomial(values, m), fn(values), atol=3e-9, rtol=3e-9)

    def test_fejer_bounds_on_dense_grid(self):
        x = np.linspace(-1, 1, 12001)
        for m in [1, 2, 3, 10, 37, 141]:
            p = fejer_polynomial(x, m)
            self.assertGreaterEqual(p.min(), 0)
            self.assertLessEqual(p.max(), m*m*(1+1e-12))
            self.assertTrue(np.all(p[:-1] <= 2/(1-x[:-1])+2e-9))

    def test_exact_constant_certificates(self):
        lower_cosh_minus_one = sum(sp.Rational(10**(2*j), math.factorial(2*j)) for j in range(1, 8))
        self.assertGreater(lower_cosh_minus_one, 10000)
        self.assertLess(sp.Rational(25, 2)*11**4, 200000)
        self.assertLess(sp.Rational(9, 2000), sp.Rational(1, 200))
        self.assertGreater(sp.Rational(42, 23), sp.Rational(7, 4))
        self.assertGreater(sp.Rational(76, 21), sp.Rational(3, 2))
        e = sp.symbols('e', positive=True)
        derivative_numerator = sp.expand((sp.Symbol('y')**2-sp.Symbol('t')**2)
                                         -2*sp.Symbol('y')*(sp.Symbol('y')-sp.Symbol('x')))
        claimed = sp.Symbol('x')**2-sp.Symbol('t')**2-(sp.Symbol('y')-sp.Symbol('x'))**2
        self.assertEqual(sp.expand(derivative_numerator-claimed), 0)

    def test_weighted_fejer_coefficient_bound(self):
        for eps in np.geomspace(1e-8, .49, 15):
            m = math.ceil(10/math.sqrt(eps))
            s = np.unique(np.r_[np.linspace(0, 2, 10001),
                                np.geomspace(1e-12, 2, 2000)])
            x = 1-s
            a0, tau = 1+1.5*eps, 1+eps
            p = fejer_polynomial(x, m)
            pa = float(fejer_polynomial(a0, m))
            coeff = ((a0-x)*(tau*tau-x*x)/(a0*a0-tau*tau))*(p/pa)**2
            self.assertLessEqual(coeff.max(), eps/200*(1+1e-6))

    def test_weighted_trace_bound_noncommuting(self):
        for eps in [.003, .03, .3]:
            a, z, _, top, tail, graph = valid_warm_start(32, 5, eps, self.rng, rotate=False)
            m = math.ceil(10/math.sqrt(eps))
            # Scale by the smallest head evaluation to avoid unnecessary overflow.
            ph = fejer_polynomial(top, m)
            pt = fejer_polynomial(tail, m)
            f = (pt[:, None]*graph)/ph[None, :]
            y = np.vstack((np.eye(5), f))@inverse_sqrt(np.eye(5)+f.T@f)
            deficiency = float(top.sum()-np.trace(y.T@a@y))
            weighted = float(np.sum((top[None, :]-tail[:, None])*f*f))
            self.assertLessEqual(deficiency, weighted+1e-10)
            self.assertLessEqual(weighted, eps*top.sum()/200)

    def test_warm_start_pca_theorem_on_rotated_instances(self):
        for n, k, eps in [(30, 3, .1), (85, 2, .3), (40, 5, .03), (19, 2, .49)]:
            a, z, _, top, _, _ = valid_warm_start(n, k, eps, self.rng)
            oracle = dense_oracle(a, symmetric=True)
            result = warm_start_pca(oracle, z, eps)
            self.assertLessEqual(oracle.queries, k*math.ceil(10/math.sqrt(eps)))
            actual = np.trace(result.T@a@result)
            self.assertGreaterEqual(actual+1e-9, (1-eps/200)*top.sum())
            np.testing.assert_allclose(result.T@result, np.eye(k), atol=1e-9)

    def test_padding_without_error_loss(self):
        p, r, dim_b = 3, 2, 10
        b = np.diag(np.r_[1.6, 1.5, np.linspace(1, .1, dim_b-r)])
        a = np.zeros((p+dim_b, p+dim_b))
        a[:p, :p] = 4*np.eye(p)
        a[p:, p:] = b
        for _ in range(20):
            f = .03*self.rng.normal(size=(dim_b-r, p+r))
            z = np.vstack((np.eye(p+r), f))@inverse_sqrt(np.eye(p+r)+f.T@f)
            # Rotate the output basis, so its known-block kernel is nontrivial.
            z = z@np.linalg.qr(self.rng.normal(size=(p+r, p+r)))[0]
            tau = residual_norm(a, z)
            self.assertLess(tau, 4)
            u = extract_padded_subspace(z, p)
            np.testing.assert_allclose(u.T@u, np.eye(r), atol=2e-11)
            self.assertLessEqual(residual_norm(b, u), tau+1e-11)

    def test_adaptive_gaussian_completion_identity(self):
        n, k = 13, 6
        h = self.rng.normal(size=(n, k))
        cs, xs = [], []
        last_col = np.zeros(n)
        last_row = np.zeros(k)
        for j in range(k-1):
            if j % 2 == 0:
                c = self.rng.normal(size=k) + .5*last_row
                cs.append(c)
                last_col = h@c
            else:
                x = self.rng.normal(size=n) + .5*last_col
                xs.append(x)
                last_row = h.T@x
        c = orth(np.column_stack(cs))
        x = orth(np.column_stack(xs))
        pc, px = c@c.T, x@x.T
        mean = px@h+h@pc-px@h@pc
        self.assertEqual(np.linalg.matrix_rank(x.T@h), x.shape[1])
        projections = []
        for _ in range(12):
            completion = mean+(np.eye(n)-px)@self.rng.normal(size=(n,k))@(np.eye(k)-pc)
            np.testing.assert_allclose(completion@c, h@c, atol=1e-11)
            np.testing.assert_allclose(x.T@completion, x.T@h, atol=1e-11)
            basis = orth(completion)
            projections.append(basis@basis.T)
        self.assertGreater(np.linalg.norm(projections[0]-projections[1], 2), .1)


if __name__ == '__main__':
    unittest.main(verbosity=2)
