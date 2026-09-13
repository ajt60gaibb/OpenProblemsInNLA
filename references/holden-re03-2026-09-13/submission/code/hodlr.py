"""Reference constructions for RE-03.

The n-query baseline is mathematically exact with exact arithmetic/SVDs.
This module uses floating point and contains the baseline and hard-instance
constructions. The proposed upper-bound references are in two_stage.py and peeling.py;
no floating-point routine in this package is a formal proof certificate.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterator
import numpy as np
from numpy.typing import NDArray

Array = NDArray[np.float64]


def depth(n: int, k: int) -> int:
    """Validate n = 2**L * k with k >= 1 and L >= 2, and return L."""
    if not isinstance(n, (int, np.integer)) or not isinstance(k, (int, np.integer)):
        raise TypeError("n and k must be integers")
    if k < 1 or n < 4 * k or n % k:
        raise ValueError("Require k >= 1 and n = 2**L * k for L >= 2")
    ratio = int(n // k)
    if ratio & (ratio - 1):
        raise ValueError("n/k must be a power of two")
    return ratio.bit_length() - 1


def _matrix(a: Array) -> Array:
    a = np.asarray(a, dtype=float)
    if a.ndim != 2 or a.shape[0] != a.shape[1]:
        raise ValueError("Expected a square matrix")
    if not np.isfinite(a).all():
        raise ValueError("Matrix entries must be finite")
    return a


def off_diagonal_blocks(n: int, k: int) -> Iterator[tuple[slice, slice]]:
    """Yield every ordered sibling block in the prescribed binary tree."""
    depth(n, k)
    def visit(lo: int, hi: int) -> Iterator[tuple[slice, slice]]:
        if hi - lo <= k:
            return
        mid = (lo + hi) // 2
        yield slice(lo, mid), slice(mid, hi)
        yield slice(mid, hi), slice(lo, mid)
        yield from visit(lo, mid)
        yield from visit(mid, hi)
    yield from visit(0, n)


def project_hodlr(a: Array, k: int) -> Array:
    """Compute a blockwise best Frobenius-norm HODLR approximation."""
    a = _matrix(a)
    n = a.shape[0]
    depth(n, k)
    b = np.array(a, copy=True)
    for rows, cols in off_diagonal_blocks(n, k):
        block = a[rows, cols]
        u, s, vt = np.linalg.svd(block, full_matrices=False)
        b[rows, cols] = (u[:, :k] * s[:k]) @ vt[:k, :]
    return b


def optimum_squared(a: Array, k: int) -> float:
    """Sum the squared singular-value tails over disjoint sibling blocks."""
    a = _matrix(a)
    depth(a.shape[0], k)
    total = 0.0
    for rows, cols in off_diagonal_blocks(a.shape[0], k):
        s = np.linalg.svd(a[rows, cols], compute_uv=False)
        total += float(s[k:] @ s[k:])
    return total


def is_hodlr(b: Array, k: int, tolerance: float = 1e-10) -> bool:
    """Numerical rank test, with scale-aware singular-value tolerance."""
    b = _matrix(b)
    depth(b.shape[0], k)
    for rows, cols in off_diagonal_blocks(b.shape[0], k):
        s = np.linalg.svd(b[rows, cols], compute_uv=False)
        if len(s) > k and s[k] > tolerance * max(1.0, float(s[0])):
            return False
    return True


@dataclass
class DenseOracle:
    """Oracle wrapper counting each vector product, including transposes."""
    matrix: Array
    queries: int = 0

    def __post_init__(self) -> None:
        self.matrix = _matrix(self.matrix).copy()
        self.queries = 0

    @property
    def n(self) -> int:
        return self.matrix.shape[0]

    def matvec(self, v: Array, transpose: bool = False) -> Array:
        v = np.asarray(v, dtype=float)
        if v.shape != (self.n,) or not np.isfinite(v).all():
            raise ValueError(f"Expected a finite vector of shape ({self.n},)")
        self.queries += 1
        return (self.matrix.T if transpose else self.matrix) @ v


def n_query_baseline(oracle: DenseOracle, k: int) -> Array:
    """Reconstruct by Ae_i, then project. Uses exactly n additional queries."""
    depth(oracle.n, k)
    a = np.empty((oracle.n, oracle.n))
    for j in range(oracle.n):
        e = np.zeros(oracle.n)
        e[j] = 1.0
        a[:, j] = oracle.matvec(e)
    return project_hodlr(a, k)


def random_projector(d: int, rank: int, rng: np.random.Generator) -> Array:
    if not 0 <= rank <= d:
        raise ValueError("Require 0 <= rank <= dimension")
    if rank == 0:
        return np.zeros((d, d))
    v = np.linalg.qr(rng.standard_normal((d, rank)), mode="reduced")[0]
    return v @ v.T


def goe(n: int, rng: np.random.Generator) -> Array:
    """GOE with off-diagonal variance 1/n and diagonal variance 2/n."""
    x = rng.standard_normal((n, n))
    return (x + x.T) / np.sqrt(2.0 * n)


def hard_instance(n: int, k: int, delta: float, rng: np.random.Generator
                  ) -> tuple[Array, Array, Array, list[Array]]:
    """Draw a numerical version of the lower-bound distribution.

    Returns A, A0, G, and the rank-k projectors. Continuous random projectors
    are used for testing; the proof instead uses a finite separated packing.
    """
    depth(n, k)
    if not 0 < delta <= 0.5:
        raise ValueError("Require 0 < delta <= 1/2")
    a0 = np.zeros((n, n))
    s = np.zeros((n, n))
    projectors = []
    ident = np.eye(2 * k)
    for lo in range(0, n, 4 * k):
        i, j = slice(lo, lo + 2*k), slice(lo + 2*k, lo + 4*k)
        p = random_projector(2*k, k, rng)
        r = 2*p - ident
        a0[i, j] = a0[j, i] = ident
        s[i, j] = s[j, i] = r
        projectors.append(p)
    g = goe(n, rng)
    return a0 + delta*s + g, a0, g, projectors
