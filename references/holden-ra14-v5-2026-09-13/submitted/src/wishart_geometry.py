"""Numerical components of the RA-14 v5 mathematical argument.

These routines use floating point.  They do not certify a universal oracle
lower bound, and they are not a new RA-14 upper-bound algorithm.
"""
from __future__ import annotations
from dataclasses import dataclass
import math
import numpy as np
from numpy.typing import NDArray

Array = NDArray[np.float64]


def orthonormalize(g: Array) -> Array:
    """Thin QR, with a fixed sign convention; requires independent columns."""
    g = np.asarray(g, dtype=float)
    if g.ndim != 2 or g.shape[0] < g.shape[1]:
        raise ValueError("Expected a tall or square two-dimensional array.")
    q, r = np.linalg.qr(g, mode="reduced")
    if np.any(np.abs(np.diag(r)) < np.finfo(float).eps):
        raise ValueError("Numerically dependent input columns.")
    return q * np.where(np.diag(r) >= 0.0, 1.0, -1.0)


def haar_frame(d: int, k: int, rng: np.random.Generator) -> Array:
    if not 0 <= k <= d:
        raise ValueError("Require 0 <= k <= d.")
    return orthonormalize(rng.standard_normal((d, k))) if k else np.empty((d, 0))


def psd_inverse_sqrt(a: Array) -> Array:
    a = np.asarray(a, dtype=float)
    w, q = np.linalg.eigh((a + a.T) / 2.0)
    if np.min(w) <= 0:
        raise ValueError("Matrix must be positive definite.")
    return (q / np.sqrt(w)) @ q.T


def logdet_spd(a: Array) -> float:
    a = np.asarray(a, dtype=float)
    chol = np.linalg.cholesky((a + a.T) / 2.0)
    return float(2.0 * np.log(np.diag(chol)).sum())


def sample_tilted_wishart(n: int, k: int, nu: int,
                           rng: np.random.Generator,
                           scale: float = 1.0) -> tuple[Array, Array]:
    """Return H and an orthonormal kernel basis for the determinant-tilted law.

    H has n-k nonzero eigenvalues distributed as scale * G G^T,
    where G has shape (n-k, n+nu) and independent N(0,1) entries.
    The returned kernel is for validation ONLY; an oracle algorithm is not
    supplied with it.
    """
    if not (n >= 2 and 1 <= k < n and isinstance(nu, int) and nu >= 0):
        raise ValueError("Require n >= 2, 1 <= k < n, integer nu >= 0.")
    if not (math.isfinite(scale) and scale > 0):
        raise ValueError("scale must be positive and finite.")
    q = haar_frame(n, n, rng)
    r = n - k
    g = rng.standard_normal((r, n + nu))
    x = q[:, :r] @ g
    h = scale * (x @ x.T)
    return (h + h.T) / 2.0, q[:, r:]


def schur_components(h: Array, v: Array) -> tuple[Array, Array, Array, Array]:
    """Express H in an orthogonal completion of the queried frame V."""
    n, t = v.shape
    if h.shape != (n, n) or not np.allclose(v.T @ v, np.eye(t), atol=1e-10):
        raise ValueError("H and V have incompatible dimensions or V is not orthonormal.")
    q, _ = np.linalg.qr(v, mode="complete")
    # QR can change signs of V.  Keep the original V and only the complement.
    w = q[:, t:]
    a = v.T @ h @ v
    b = w.T @ h @ v
    s = w.T @ h @ w - b @ np.linalg.solve(a, b.T)
    return a, b, (s + s.T) / 2.0, w


def kernel_graph(a: Array, b: Array, u: Array) -> tuple[Array, Array, Array]:
    """Return C, a graph kernel basis, and the matrix K = B A^-2 B^T.

    U is an orthonormal kernel basis of the Schur complement, supplied by a
    mathematical/validation caller, not revealed by the query model.
    """
    ab = np.linalg.solve(a, b.T)
    kmat = ab.T @ ab
    c = u.T @ kmat @ u
    z = np.vstack([-ab @ u, u]) @ psd_inverse_sqrt(np.eye(u.shape[1]) + c)
    return (c + c.T) / 2.0, z, kmat


def ridge_potential(u: Array, v: Array, alpha: float) -> float:
    if alpha <= 0:
        raise ValueError("alpha must be positive.")
    overlap = u.T @ v @ v.T @ u
    return logdet_spd(np.eye(u.shape[1]) + alpha * overlap)


def angular_quantities(u: Array, kmat: Array, v: Array, beta: float,
                       nu: float) -> tuple[float, float, float]:
    """Return (divergence, log-density directional derivative, r).

    r = v^T U (I + beta U^T K U)^-1 U^T v.
    The vector field is (I-UU^T) v v^T U (I+beta U^T K U)^-1.
    """
    d, k = u.shape
    if beta <= 0 or nu < 0 or kmat.shape != (d, d) or v.shape != (d,):
        raise ValueError("Invalid parameters or dimensions.")
    c = u.T @ kmat @ u
    f = np.linalg.inv(np.eye(k) + beta * c)
    dinv = np.linalg.inv(np.eye(k) + c)
    a = u.T @ v
    z = u.T @ kmat @ (v - u @ a)
    h = float(a @ a)
    r = float(a @ f @ a)
    trf = float(np.trace(f))
    divergence = ((1.0 - h) * trf - (d-k)*r
                  - beta * (a @ f @ f @ z + trf*(a @ f @ z)))
    score = nu * (a @ f @ dinv @ z)
    return float(divergence), float(score), r


def angular_bound(d: int, k: int, nu: float, beta: float) -> float:
    if d <= k+1 or k < 1 or nu < 0 or beta <= 0:
        raise ValueError("Require d > k+1, k >= 1, nu >= 0, beta > 0.")
    return (k + nu / beta) / (d - k - 1)


def graph_coordinate_field(y: Array, kmat: Array, v: Array, beta: float) -> Array:
    """Coordinate expression used to check the divergence derivation."""
    k = y.shape[1]
    rinv = psd_inverse_sqrt(np.eye(k) + y.T @ y)
    u = np.vstack([np.eye(k), y]) @ rinv
    f = np.linalg.inv(np.eye(k) + beta * u.T @ kmat @ u)
    a, b = v[:k], v[k:]
    return np.outer(b-y@a, a+b@y) @ rinv @ f @ np.linalg.inv(rinv)


def finite_accuracy_scale(n: int, k: int, epsilon: float) -> float:
    """F = k/sqrt(epsilon) * log(1+n*sqrt(epsilon)/k)."""
    if not (n >= 2 and 1 <= k < n and 0 < epsilon < 0.5):
        raise ValueError("Parameters are outside RA-14's domain.")
    y = n * math.sqrt(epsilon) / k
    return n * math.log1p(y) / y


@dataclass
class SymmetricOracle:
    """Counted matrix-vector interface for numerical diagnostics."""
    matrix: Array
    queries: int = 0

    def matvec(self, v: Array) -> Array:
        v = np.asarray(v, dtype=float)
        if v.ndim != 1 or v.shape[0] != self.matrix.shape[0]:
            raise ValueError("Each call must contain exactly one compatible vector.")
        self.queries += 1
        return self.matrix @ v


def adaptive_frames(oracle: SymmetricOracle, tmax: int, strategy: str,
                    rng: np.random.Generator) -> list[Array]:
    """Generate legal query frames using only previous products and fresh noise.

    Strategies: random; Krylov frontier; random vector orthogonal to both the
    queries and their replies.  The latter falls back to the query complement
    when its chosen candidate is numerically zero.  No hidden kernel, eigenbasis,
    or dense matrix operation is used to select queries.
    """
    n = oracle.matrix.shape[0]  # Dimension only; never inspect matrix entries.
    if not (0 <= tmax <= n) or strategy not in {"random", "krylov", "reply_null"}:
        raise ValueError("Invalid budget or strategy.")
    vframe = np.empty((n, 0)); replies = np.empty((n, 0))
    frames = [vframe.copy()]
    for _ in range(tmax):
        if strategy == "krylov" and replies.shape[1]:
            candidate = replies[:, -1].copy()
        else:
            candidate = rng.standard_normal(n)
        if strategy == "reply_null" and replies.shape[1]:
            q, singular, _ = np.linalg.svd(np.column_stack([vframe, replies]), full_matrices=False)
            keep = singular > 1e-11 * max(1.0, singular[0])
            candidate -= q[:, keep] @ (q[:, keep].T @ candidate)
        for _pass in range(2):
            candidate -= vframe @ (vframe.T @ candidate)
        if np.linalg.norm(candidate) < 1e-10:
            candidate = rng.standard_normal(n)
            for _pass in range(2):
                candidate -= vframe @ (vframe.T @ candidate)
        candidate /= np.linalg.norm(candidate)
        answer = oracle.matvec(candidate)
        vframe = np.column_stack([vframe, candidate])
        replies = np.column_stack([replies, answer])
        frames.append(vframe.copy())
    return frames
