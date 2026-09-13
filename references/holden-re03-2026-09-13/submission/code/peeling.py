"""Query-counted reference implementation of the proposed RE-03 upper bound.

The proof is for exact arithmetic. This dense NumPy implementation uses floating
point, numerical rank thresholds, and explicit dense output storage. It is not a
large-scale implementation or a formal verification of the theorem.

`approximate` uses the conservative parameters in the manuscript and the n-query
fallback. `peel_with_parameters` exposes smaller experimental parameters; those
parameters do NOT carry the manuscript's 0.99 relative-error guarantee.
"""
from __future__ import annotations

from dataclasses import dataclass
from math import ceil
from fractions import Fraction
from typing import Protocol
import numpy as np
from numpy.typing import NDArray
from hodlr import depth, project_hodlr

Array = NDArray[np.float64]


class MatvecOracle(Protocol):
    @property
    def n(self) -> int: ...
    def matvec(self, v: Array, transpose: bool = False) -> Array: ...


@dataclass(frozen=True)
class Parameters:
    right_width: int
    left_width: int
    buckets: int
    leaf_width: int

    def validate(self, k: int) -> None:
        values = (self.right_width, self.left_width, self.buckets, self.leaf_width)
        if any(not isinstance(x, (int, np.integer)) for x in values):
            raise TypeError("Sketch parameters must be integers")
        if self.right_width <= k + 1:
            raise ValueError("Require right_width > k + 1")
        if self.left_width <= self.right_width + 1:
            raise ValueError("Require left_width > right_width + 1")
        if self.buckets < 1 or self.leaf_width <= 2 * k + 1:
            raise ValueError("Require buckets >= 1 and leaf_width > 2*k + 1")

    def budget(self, n: int, k: int) -> int:
        h = depth(n, k) - 1
        return 2 * h * self.buckets * (self.right_width + self.left_width) + self.leaf_width


@dataclass
class Approximation:
    matrix: Array
    queries: int
    method: str
    parameters: Parameters | None
    budget: int
    level_queries: list[int]


def certified_parameters(n: int, k: int, epsilon: float) -> Parameters:
    """The manuscript's deliberately loose, dimension-independent constants."""
    h = depth(n, k) - 1
    if not np.isfinite(epsilon) or not 0.0 < epsilon < 0.5:
        raise ValueError("Require 0 < epsilon < 1/2")
    # Exact rational arithmetic for the supplied floating-point epsilon avoids
    # overflow/underflow when the n-query fallback is plainly preferable.
    eta = Fraction(float(epsilon)) / 2600
    s = k + 1 + ceil(Fraction(k) / eta)
    t = s + 1 + ceil(Fraction(s) / eta)
    p = 2 * k + 1 + ceil(Fraction(2 * k) / eta)
    return Parameters(s, t, h, p)


def _truncate(a: Array, k: int) -> Array:
    if a.size == 0:
        return np.zeros_like(a)
    u, s, vt = np.linalg.svd(a, full_matrices=False)
    r = min(k, len(s))
    return (u[:, :r] * s[:r]) @ vt[:r, :]


def _orth(a: Array, tolerance: float) -> Array:
    u, s, _ = np.linalg.svd(a, full_matrices=False)
    if len(s) == 0 or s[0] == 0:
        return np.empty((a.shape[0], 0))
    r = int(np.count_nonzero(s > tolerance * s[0]))
    return u[:, :r]


class _Counter:
    def __init__(self, oracle: MatvecOracle):
        self.oracle = oracle
        self.queries = 0

    def apply(self, x: Array, transpose: bool = False) -> Array:
        """Every column is submitted as one charged vector query."""
        y = np.empty((self.oracle.n, x.shape[1]))
        for j in range(x.shape[1]):
            value = np.asarray(self.oracle.matvec(x[:, j], transpose=transpose), dtype=float)
            if value.shape != (self.oracle.n,) or not np.isfinite(value).all():
                raise ValueError("Oracle returned a non-finite or incorrectly shaped result")
            y[:, j] = value
            self.queries += 1
        return y


def _blocks(n: int, level: int, reverse: bool) -> list[tuple[slice, slice]]:
    m = n // (2**level)
    blocks = []
    for lo in range(0, n, 2*m):
        left, right = slice(lo, lo+m), slice(lo+m, lo+2*m)
        blocks.append((right, left) if reverse else (left, right))
    return blocks


def peel_with_parameters(
    oracle: MatvecOracle, k: int, parameters: Parameters,
    rng: np.random.Generator | None = None, rank_tolerance: float = 1e-12,
) -> Approximation:
    """Perforated Gaussian Nyström peeling with a 2k-block diagonal finish.

    Only `oracle.n` and `oracle.matvec` are used. Sketches from the two sides,
    orientations, and levels are independent. The previous-level approximation
    is frozen until BOTH orientations at a level have been computed.
    """
    n = oracle.n
    h = depth(n, k) - 1
    parameters.validate(k)
    if not np.isfinite(rank_tolerance) or rank_tolerance < 0:
        raise ValueError("rank_tolerance must be finite and nonnegative")
    rng = np.random.default_rng() if rng is None else rng
    counter = _Counter(oracle)
    s, t, b, p = (parameters.right_width, parameters.left_width,
                  parameters.buckets, parameters.leaf_width)
    estimate = np.zeros((n, n))
    level_queries = []

    for level in range(1, h+1):
        start_count = counter.queries
        update = np.zeros_like(estimate)
        for reverse in (False, True):
            blocks = _blocks(n, level, reverse)
            m = blocks[0][0].stop - blocks[0][0].start
            count = len(blocks)
            omegas = [rng.standard_normal((m, s)) for _ in blocks]
            psis = [rng.standard_normal((m, t)) for _ in blocks]
            right_hash = rng.integers(0, b, count)
            left_hash = rng.integers(0, b, count)
            right_data: list[Array | None] = [None] * count
            left_data: list[Array | None] = [None] * count

            for bucket in range(b):
                chosen = np.flatnonzero(right_hash == bucket)
                if chosen.size:
                    vectors = np.zeros((n, s))
                    for i in chosen:
                        vectors[blocks[i][1], :] = omegas[i]
                    responses = counter.apply(vectors) - estimate @ vectors
                    for i in chosen:
                        right_data[i] = responses[blocks[i][0], :].copy()
                chosen = np.flatnonzero(left_hash == bucket)
                if chosen.size:
                    vectors = np.zeros((n, t))
                    for i in chosen:
                        vectors[blocks[i][0], :] = psis[i]
                    responses = counter.apply(vectors, transpose=True) - estimate.T @ vectors
                    for i in chosen:
                        left_data[i] = responses[blocks[i][1], :].T.copy()

            for i, (rows, cols) in enumerate(blocks):
                if right_data[i] is None or left_data[i] is None:
                    raise RuntimeError("Missing sketch data")
                q = _orth(right_data[i], rank_tolerance)
                if q.shape[1] == 0:
                    update[rows, cols] = 0.0
                else:
                    design = psis[i].T @ q
                    core = np.linalg.pinv(design, rcond=rank_tolerance) @ left_data[i]
                    update[rows, cols] = q @ _truncate(core, k)
        estimate += update
        level_queries.append(counter.queries - start_count)

    # Final size-2k diagonal blocks are unrestricted in H_{n,k}.
    omega = rng.standard_normal((n, p))
    response = counter.apply(omega) - estimate @ omega
    for lo in range(0, n, 2*k):
        block = slice(lo, lo+2*k)
        estimate[block, block] = response[block, :] @ np.linalg.pinv(
            omega[block, :], rcond=rank_tolerance)
    level_queries.append(p)
    budget = parameters.budget(n, k)
    if counter.queries > budget:
        raise AssertionError("Query count exceeds the theoretical budget")
    return Approximation(estimate, counter.queries, "perforated_peeling", parameters,
                         budget, level_queries)


def approximate(
    oracle: MatvecOracle, k: int, epsilon: float,
    rng: np.random.Generator | None = None,
) -> Approximation:
    """Use theorem parameters, or reconstruct exactly with n vector queries.

    Certification refers to the exact-arithmetic analysis, not floating-point
    error or independent verification of the proof.
    """
    params = certified_parameters(oracle.n, k, epsilon)
    budget = params.budget(oracle.n, k)
    if budget >= oracle.n:
        counter = _Counter(oracle)
        # Explicit basis queries; no privileged access to matrix entries.
        full = counter.apply(np.eye(oracle.n))
        return Approximation(project_hodlr(full, k), counter.queries, "n_query_baseline",
                             None, oracle.n, [oracle.n])
    return peel_with_parameters(oracle, k, params, rng=rng)
