"""Oracle-counted numerical illustrations for the accompanying RA-14 note.

The proofs use exact real arithmetic. This module uses floating-point arithmetic;
it illustrates identities and query accounting, not universal probabilistic bounds.
All access to an input matrix inside a solver goes through MatvecOracle. Dense
matrices are permitted only in the constructor and in separate validation code.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable
import math
import numpy as np
from numpy.typing import NDArray

Array = NDArray[np.float64]


@dataclass
class MatvecOracle:
    n: int
    matvec: Callable[[Array], Array]
    rmatvec: Callable[[Array], Array]
    symmetric: bool = False
    max_queries: int | None = None
    forward_queries: int = 0
    transpose_queries: int = 0

    def __post_init__(self) -> None:
        if not isinstance(self.n, int) or self.n < 1:
            raise ValueError("n must be a positive integer")
        if self.max_queries is not None and self.max_queries < 0:
            raise ValueError("max_queries must be nonnegative")

    @property
    def queries(self) -> int:
        return self.forward_queries + self.transpose_queries

    def apply(self, x: Array, *, transpose: bool = False) -> Array:
        x = np.asarray(x, dtype=float)
        if x.shape != (self.n,) or not np.all(np.isfinite(x)):
            raise ValueError(f"query must be a finite vector of shape {(self.n,)}")
        if self.max_queries is not None and self.queries >= self.max_queries:
            raise RuntimeError("oracle query budget exhausted")
        if transpose:
            self.transpose_queries += 1
            y = self.rmatvec(x.copy())
        else:
            self.forward_queries += 1
            y = self.matvec(x.copy())
        y = np.asarray(y, dtype=float)
        if y.shape != (self.n,) or not np.all(np.isfinite(y)):
            raise ValueError("oracle returned an invalid vector")
        return y.copy()

    def block(self, x: Array, *, transpose: bool = False) -> Array:
        """Each column is explicitly counted as one vector query."""
        x = np.asarray(x, dtype=float)
        if x.ndim != 2 or x.shape[0] != self.n:
            raise ValueError("block has incompatible shape")
        if x.shape[1] == 0:
            return np.empty((self.n, 0))
        return np.column_stack([
            self.apply(x[:, j], transpose=transpose) for j in range(x.shape[1])
        ])


def dense_oracle(a: Array, *, symmetric: bool = False,
                 max_queries: int | None = None) -> MatvecOracle:
    a = np.asarray(a, dtype=float)
    if a.ndim != 2 or a.shape[0] != a.shape[1] or not np.all(np.isfinite(a)):
        raise ValueError("a must be a finite square matrix")
    if symmetric and not np.allclose(a, a.T, atol=1e-12, rtol=1e-12):
        raise ValueError("symmetric=True but the matrix is not symmetric")
    stored = a.copy()
    return MatvecOracle(a.shape[0], lambda x: stored @ x,
                        lambda x: stored.T @ x, symmetric, max_queries)


def _check_rank(n: int, k: int) -> None:
    if not isinstance(k, int) or not 1 <= k < n:
        raise ValueError("k must satisfy 1 <= k < n")


def orth(x: Array, *, against: Array | None = None,
         rtol: float = 1e-12, reference_scale: float | None = None) -> Array:
    """Twice-reorthogonalized, SVD rank-revealing basis.

    reference_scale is useful when the entire residual block is roundoff-sized;
    a purely relative threshold on that residual would create spurious vectors.
    """
    x = np.asarray(x, dtype=float)
    if x.ndim != 2:
        raise ValueError("x must be a matrix")
    if x.shape[1] == 0:
        return np.empty((x.shape[0], 0))
    y = x.copy()
    if against is not None and against.shape[1]:
        for _ in range(2):
            y -= against @ (against.T @ y)
    u, s, _ = np.linalg.svd(y, full_matrices=False)
    scale = max(float(s[0]) if s.size else 0.0,
                0.0 if reference_scale is None else float(reference_scale))
    if scale == 0:
        return np.empty((x.shape[0], 0))
    return u[:, s > rtol * scale]


def complete_basis(q: Array, k: int, *, rtol: float = 1e-12) -> Array:
    q = orth(q, rtol=rtol)
    n = q.shape[0]
    if not 0 <= k <= n:
        raise ValueError("invalid requested basis size")
    q = q[:, :k]
    for j in range(n):
        if q.shape[1] == k:
            break
        v = orth(np.eye(n)[:, j:j+1], against=q,
                 rtol=rtol, reference_scale=1.0)
        if v.shape[1]:
            q = np.column_stack((q, v[:, :1]))
    if q.shape[1] != k:
        raise ArithmeticError("could not complete an orthonormal basis")
    return q


def exact_via_columns(oracle: MatvecOracle, k: int) -> Array:
    """n-query exact-arithmetic upper bound, implemented numerically."""
    _check_rank(oracle.n, k)
    a = oracle.block(np.eye(oracle.n))
    _, _, vt = np.linalg.svd(a, full_matrices=False)
    return vt[:k].T


def recover_promised_rank(oracle: MatvecOracle, k: int,
                          rng: np.random.Generator) -> Array:
    """Use k A^T-products; guarantee requires the promise rank(A) <= k."""
    _check_rank(oracle.n, k)
    sketch = oracle.block(rng.standard_normal((oracle.n, k)), transpose=True)
    return complete_basis(orth(sketch), k)


def block_krylov_lra(oracle: MatvecOracle, k: int, steps: int,
                     rng: np.random.Generator,
                     block_size: int | None = None) -> Array:
    """Right-sided block Krylov approximation with an explicit depth.

    Uses <= b(2*steps+2) products, b=block_size, including Ritz compression.
    This function does not select a theorem-certified universal constant in the
    iteration count. An explicit depth is deliberate: numerical success is not
    a claim that a tested depth guarantees 99% success for every input.
    """
    _check_rank(oracle.n, k)
    if not isinstance(steps, int) or steps < 0:
        raise ValueError("steps must be a nonnegative integer")
    b = k if block_size is None else block_size
    if not isinstance(b, int) or not k <= b <= oracle.n:
        raise ValueError("block_size must lie between k and n")
    first = oracle.block(rng.standard_normal((oracle.n, b)), transpose=True)
    frontier = orth(first)
    blocks: list[Array] = []
    images: list[Array] = []
    q = np.empty((oracle.n, 0))
    for j in range(steps + 1):
        if frontier.shape[1] == 0:
            break
        blocks.append(frontier)
        q = np.column_stack(blocks)
        image = oracle.block(frontier)
        images.append(image)
        if j == steps or q.shape[1] == oracle.n:
            break
        candidate = oracle.block(image, transpose=True)
        frontier = orth(candidate, against=q,
                        reference_scale=np.linalg.norm(candidate, 2))
    if q.shape[1] < k:
        return complete_basis(q, k)
    aq = np.column_stack(images)
    # SVD of the already known A Q avoids squaring its condition number.
    _, _, vt = np.linalg.svd(aq, full_matrices=False)
    return q @ vt[:k].T


def postprocess_symmetric(oracle: MatvecOracle, z: Array, degree: int) -> Array:
    """Top algebraic Ritz vectors in K_degree(M,z), <= k(degree+1) products.

    No spectral bound b or gap is used by the algorithm. Such quantities occur
    only in the proof of the accompanying warm-start theorem.
    """
    if not oracle.symmetric:
        raise ValueError("a symmetric oracle is required")
    z = np.asarray(z, dtype=float)
    if z.ndim != 2 or z.shape[0] != oracle.n:
        raise ValueError("invalid starting block")
    k = z.shape[1]
    _check_rank(oracle.n, k)
    if not isinstance(degree, int) or degree < 0:
        raise ValueError("degree must be a nonnegative integer")
    if not np.allclose(z.T @ z, np.eye(k), atol=1e-9, rtol=1e-9):
        raise ValueError("z must have orthonormal columns")
    frontier = z.copy()
    blocks: list[Array] = []
    images: list[Array] = []
    q = np.empty((oracle.n, 0))
    for j in range(degree + 1):
        if frontier.shape[1] == 0:
            break
        blocks.append(frontier)
        q = np.column_stack(blocks)
        image = oracle.block(frontier)
        images.append(image)
        if j == degree or q.shape[1] == oracle.n:
            break
        frontier = orth(image, against=q,
                        reference_scale=np.linalg.norm(image, 2))
    mq = np.column_stack(images)
    h = q.T @ mq
    h = (h + h.T) / 2
    _, vectors = np.linalg.eigh(h)
    return q @ vectors[:, -k:]


def warm_start_pca(oracle: MatvecOracle, z: Array, epsilon: float) -> Array:
    """The note's Fejer-filter postprocessor, implemented through Ritz extraction.

    The theorem requires positive top k eigenvalues, tail magnitude <= b,
    lambda_k >= (1+1.5*epsilon)*b, and residual <= (1+epsilon)*b.
    These are promises, not checked using uncharged matrix access.
    """
    if not math.isfinite(epsilon) or not 0 < epsilon < 0.5:
        raise ValueError("epsilon must lie in (0, 1/2)")
    m = math.ceil(10 / math.sqrt(epsilon))
    return postprocess_symmetric(oracle, z, m - 1)


def fejer_polynomial(u: Array | float, m: int) -> Array:
    """p_m(u)=(T_m(u)-1)/(u-1), evaluated without subtraction near u=1.

    Trigonometric/hyperbolic identities are used for numerical validation.
    Large m*arcosh(u) may overflow; validation ranges keep this bounded.
    """
    if not isinstance(m, int) or m < 1:
        raise ValueError("m must be a positive integer")
    u = np.asarray(u, dtype=float)
    if np.any(u < -1) or not np.all(np.isfinite(u)):
        raise ValueError("this evaluator supports finite u >= -1")
    out = np.empty_like(u)
    inner = u <= 1
    theta = np.arccos(np.clip(u[inner], -1, 1))
    # sin(m*t/2)/sin(t/2) = m*sinc(m*t/(2*pi))/sinc(t/(2*pi)).
    out[inner] = (m * np.sinc(m * theta / (2*np.pi))
                  / np.sinc(theta / (2*np.pi))) ** 2
    h = np.arccosh(u[~inner])
    with np.errstate(over="raise", invalid="raise"):
        out[~inner] = (np.sinh(m*h/2) / np.sinh(h/2)) ** 2
    return out


def sharp_overlap_instance(k: int, epsilon: float) -> tuple[Array, Array, float]:
    if k < 1 or not 0 < epsilon < 0.5:
        raise ValueError("invalid parameters")
    a, b, tau = 1 + 2*epsilon, 1.0, 1 + epsilon
    alpha2 = 1 - (tau/a)**2
    n = 2*k + 1
    a_matrix = np.diag(np.r_[np.full(k, a), np.zeros(k), b])
    z = np.zeros((n, k))
    z[:k] = np.sqrt(alpha2) * np.eye(k)
    z[k:2*k] = np.sqrt(1-alpha2) * np.eye(k)
    return a_matrix, z, alpha2


def extract_padded_subspace(z: Array, known_rank: int) -> Array:
    """Extract S intersect {known block=0}; assumes full row rank in that block."""
    z = np.asarray(z, dtype=float)
    if z.ndim != 2 or not 0 <= known_rank < z.shape[1]:
        raise ValueError("invalid dimensions")
    c, d = z[:known_rank], z[known_rank:]
    if known_rank == 0:
        return z.copy()
    _, singulars, vt = np.linalg.svd(c, full_matrices=True)
    if singulars[-1] <= 1e-12 * max(singulars[0], 1):
        raise ValueError("known-block rows are not numerically independent")
    null_c = vt[known_rank:].T
    return d @ null_c


def residual_norm(a: Array, z: Array) -> float:
    """Validation only: this dense access is NOT part of an oracle algorithm."""
    return float(np.linalg.norm(a - (a @ z) @ z.T, 2))


def principal_overlap(v: Array, z: Array) -> float:
    return float(np.linalg.svd(v.T @ z, compute_uv=False)[-1] ** 2)
