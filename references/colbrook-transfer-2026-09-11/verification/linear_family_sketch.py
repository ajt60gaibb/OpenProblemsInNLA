"""Nonadaptive two-sided sketches for relative-error linear-family regression.

The mathematical guarantee is for exact real arithmetic. This NumPy reference
implementation is for reproducibility, not a claim of numerical backward stability.
Only the two oracle callables access the unknown matrix. All query directions
are selected before either oracle is called.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Callable
import numpy as np

Array = np.ndarray

@dataclass(frozen=True)
class Plan:
    basis: Array  # q x m x n, Frobenius-orthonormal
    left: Array   # m x r
    right: Array  # n x s, standard normal, NOT normalized
    residual_leverage: float
    epsilon_squared: float
    theoretical: bool

    @property
    def query_count(self) -> int:
        return self.left.shape[1] + self.right.shape[1]


def orthonormalize_family(basis: Array, tolerance: float = 1e-12) -> Array:
    """Return a Frobenius-orthonormal basis of the same real matrix subspace."""
    a = np.asarray(basis, dtype=float)
    if a.ndim != 3 or not np.isfinite(a).all():
        raise ValueError("basis must be a finite q-by-m-by-n array")
    q, m, n = a.shape
    if min(q, m, n) < 1:
        raise ValueError("the family and matrix dimensions must be positive")
    u, singular_values, _ = np.linalg.svd(a.reshape(q, m*n).T, full_matrices=False)
    rank = int(np.sum(singular_values > tolerance * singular_values[0]))
    if rank == 0:
        raise ValueError("the supplied family is zero-dimensional")
    return u[:, :rank].T.reshape(rank, m, n)


def make_plan(basis: Array, epsilon_squared: float = .1, seed: int = 0,
              *, practical_samples: int | None = None,
              practical_rank: int | None = None) -> Plan:
    """Choose query directions using the known family alone.

    By default the proved sample bound is used, with the best spectral split
    among all ranks. Optional practical overrides are explicitly NOT covered by
    that bound. The implementation deliberately does not replace the method by
    n full-information queries when the conservative bound exceeds n.
    """
    if not 0 < epsilon_squared < 1:
        raise ValueError("epsilon_squared must lie strictly between zero and one")
    p = orthonormalize_family(basis)
    q, m, n = p.shape
    rsum = np.einsum('imn,ikn->mk', p, p)
    eigenvalues, eigenvectors = np.linalg.eigh(rsum)
    order = np.argsort(eigenvalues)[::-1]
    eigenvalues = np.maximum(eigenvalues[order], 0)
    eigenvectors = eigenvectors[:, order]
    log_factor = np.log(20*q)

    def samples(tau: float) -> int:
        if tau == 0.0:
            return 0  # exact-support branch of the mathematical sample rule
        return int(np.ceil(max(8*(1+2*tau)*log_factor,
                               160*tau/epsilon_squared)))

    candidates = []
    for r in range(m+1):
        tau = float(eigenvalues[r]) if r < m else 0.0
        s = samples(tau)
        candidates.append((r+s, r, s, tau))
    _, r, s, tau = min(candidates)
    theoretical = practical_samples is None and practical_rank is None
    if practical_rank is not None:
        if not 0 <= practical_rank <= m:
            raise ValueError("practical_rank must be between 0 and m")
        r = practical_rank
        tau = float(eigenvalues[r]) if r < m else 0.0
        s = samples(tau)
    if practical_samples is not None:
        if practical_samples < 0:
            raise ValueError("practical_samples must be nonnegative")
        s = practical_samples
    left = eigenvectors[:, :r]
    right = np.random.default_rng(seed).standard_normal((n, s))
    return Plan(p, left, right, tau, epsilon_squared, theoretical)


def solve_from_oracles(plan: Plan, right_oracle: Callable[[Array], Array],
                       left_oracle: Callable[[Array], Array]) -> tuple[Array, Array, dict]:
    """Return (matrix estimate, coefficient estimate, numerical diagnostics).

    right_oracle(G) must return A @ G; left_oracle(U) must return A.T @ U.
    Passing a block with s columns represents s individual matvec queries.
    """
    p, u, g = plan.basis, plan.left, plan.right
    q, m, n = p.shape
    r, s = u.shape[1], g.shape[1]
    left_response = np.asarray(left_oracle(u), dtype=float) if r else np.empty((n, 0))
    right_response = np.asarray(right_oracle(g), dtype=float) if s else np.empty((m, 0))
    if left_response.shape != (n, r) or right_response.shape != (m, s):
        raise ValueError("oracle response has an incorrect shape")
    if not np.isfinite(left_response).all() or not np.isfinite(right_response).all():
        raise ValueError("oracle responses must contain only finite values")
    exact_design = np.einsum('mr,imn->irn', u, p)
    gram = np.einsum('irn,jrn->ij', exact_design, exact_design)
    rhs = np.einsum('irn,nr->i', exact_design, left_response)
    if s:
        residual_basis = p - np.einsum('mr,irn->imn', u, exact_design)
        random_design = np.einsum('imn,ns->ims', residual_basis, g)
        random_response = right_response - u @ (u.T @ right_response)
        gram += np.einsum('ims,jms->ij', random_design, random_design)/s
        rhs += np.einsum('ims,ms->i', random_design, random_response)/s
    gram = (gram + gram.T)/2
    eig = np.linalg.eigvalsh(gram)
    coefficient, _, rank, singular_values = np.linalg.lstsq(gram, rhs, rcond=None)
    estimate = np.einsum('i,imn->mn', coefficient, p)
    diagnostics = {
        'q': q, 'matrix_shape': [m, n], 'left_queries': r, 'right_queries': s,
        'total_queries': r+s, 'residual_leverage': plan.residual_leverage,
        'minimum_gram_eigenvalue': float(eig[0]),
        'maximum_gram_eigenvalue': float(eig[-1]),
        'numerical_gram_rank': int(rank), 'proved_sample_rule': plan.theoretical,
    }
    return estimate, coefficient, diagnostics


def exact_second_moment(residual_basis: Array) -> Array:
    """Compute E[(M(g).T M(g)-H)^2] by the exact Gaussian fourth-moment formula."""
    t = np.asarray(residual_basis, dtype=float)
    q = t.shape[0]
    variance = np.zeros((q, q))
    for i in range(q):
        for j in range(q):
            for ell in range(q):
                a = t[i].T @ t[ell]
                b = t[ell].T @ t[j]
                variance[i, j] += np.trace(a @ b) + np.trace(a @ b.T)
    return (variance + variance.T)/2


def median_radius_index(estimates: Array) -> int:
    """Select an estimate whose median distance to all estimates is smallest.

    If a strict majority lie within rho of a common truth, the returned estimate
    lies within 3*rho. Distances include the zero distance to the point itself.
    No knowledge of rho or the truth is used. An odd number of estimates is
    required to make the exact majority/median convention unambiguous.
    """
    x = np.asarray(estimates, dtype=float)
    if x.ndim != 2 or x.shape[0] < 1 or x.shape[0] % 2 == 0:
        raise ValueError("estimates must have a positive odd number of rows")
    if not np.isfinite(x).all():
        raise ValueError("estimates must be finite")
    distances = np.linalg.norm(x[:, None, :] - x[None, :, :], axis=2)
    radii = np.partition(distances, x.shape[0]//2, axis=1)[:, x.shape[0]//2]
    return int(np.argmin(radii))
