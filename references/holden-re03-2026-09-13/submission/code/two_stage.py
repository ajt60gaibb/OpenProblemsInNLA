"""Two-stage HODLR approximation with a globally shared final regression.

The proposed exact-arithmetic query bound is
  O(min(n, k*L**2/epsilon + k*L/epsilon**2)).
The manuscript is unreviewed. This dense floating-point implementation is not a
proof certificate. Experimental parameters do not carry a 0.99 guarantee.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from math import ceil
import numpy as np
from numpy.typing import NDArray
from hodlr import depth, project_hodlr
from peeling import MatvecOracle, _Counter, _blocks, _orth, _truncate

Array = NDArray[np.float64]


@dataclass(frozen=True)
class Space:
    rows: slice
    columns: slice
    basis: Array


@dataclass(frozen=True)
class TwoStageParameters:
    right_width: int
    pilot_left_width: int
    buckets: int
    regression_width: int

    def validate(self, n: int, k: int) -> None:
        depth(n, k)
        values = (self.right_width, self.pilot_left_width, self.buckets, self.regression_width)
        if any(not isinstance(v, (int, np.integer)) for v in values):
            raise TypeError("Widths and bucket count must be integers")
        if self.right_width <= k+1 or self.pilot_left_width <= self.right_width+1:
            raise ValueError("Require right_width > k+1 and pilot_left_width > right_width+1")
        if self.buckets < 1 or self.regression_width < 1:
            raise ValueError("Bucket count and regression width must be positive")

    def budget(self, n: int, k: int) -> int:
        h = depth(n, k)-1
        return 2*h*self.buckets*(self.right_width+self.pilot_left_width)+self.regression_width


@dataclass
class TwoStageApproximation:
    matrix: Array
    queries: int
    method: str
    parameters: TwoStageParameters | None
    budget: int
    maximum_design_dimension: int
    pilot_queries: int
    regression_queries: int


def theorem_parameters(n: int, k: int, epsilon: float) -> TwoStageParameters:
    h = depth(n, k)-1
    if not np.isfinite(epsilon) or not 0 < epsilon < 0.5:
        raise ValueError("Require 0 < epsilon < 1/2")
    eta = Fraction(float(epsilon))/500
    s = k+1+ceil(Fraction(k)/eta)
    t = s+1+1000*s
    rbound = 2*k+s*h
    d = ceil(max(Fraction(100*k*h)/eta**2, Fraction(6*s*h+2*k)/eta))
    return TwoStageParameters(s, t, h, rbound+1+d)


def column_design(spaces: list[Space], n: int, k: int, j: int) -> Array:
    """Orthogonal block bases for one column; diagonal leaves have size 2k."""
    lo = (j//(2*k))*(2*k)
    leaf = np.zeros((n, 2*k))
    leaf[lo:lo+2*k] = np.eye(2*k)
    parts = [leaf]
    for space in spaces:
        if space.columns.start <= j < space.columns.stop:
            block = np.zeros((n, space.basis.shape[1]))
            block[space.rows] = space.basis
            parts.append(block)
    return np.column_stack(parts)


def fit_and_truncate(
    oracle: MatvecOracle, k: int, spaces: list[Space], width: int,
    rng: np.random.Generator, tolerance: float = 1e-12,
) -> tuple[Array, int, int]:
    """Fresh shared transpose sketch; proper rank-k truncation on every block.

    The spaces are supplied from the pilot in the complete algorithm. Tests may
    instead supply privileged spaces; that does not make this a stand-alone
    general-oracle solver. The cost reported here excludes acquiring the spaces.
    """
    n = oracle.n
    depth(n, k)
    designs = [column_design(spaces, n, k, j) for j in range(n)]
    rmax = max(z.shape[1] for z in designs)
    if width <= rmax+1:
        raise ValueError("Require regression width > maximum design dimension + 1")
    omega = rng.standard_normal((n, width))
    counter = _Counter(oracle)
    y = counter.apply(omega, transpose=True)
    b = np.empty((n, n))
    for j, z in enumerate(designs):
        coefficients = np.linalg.pinv(omega.T @ z, rcond=tolerance) @ y[j]
        b[:, j] = z @ coefficients
    for space in spaces:
        b[space.rows, space.columns] = _truncate(b[space.rows, space.columns], k)
    return b, counter.queries, rmax


def two_stage_with_parameters(
    oracle: MatvecOracle, k: int, parameters: TwoStageParameters,
    rng: np.random.Generator | None = None, rank_tolerance: float = 1e-12,
) -> TwoStageApproximation:
    """Use explicit experimental widths, without an automatic n-query fallback."""
    n = oracle.n
    h = depth(n, k)-1
    parameters.validate(n, k)
    if not np.isfinite(rank_tolerance) or rank_tolerance < 0:
        raise ValueError("rank_tolerance must be finite and nonnegative")
    rng = np.random.default_rng() if rng is None else rng
    counter = _Counter(oracle)
    s, t, buckets = parameters.right_width, parameters.pilot_left_width, parameters.buckets
    pilot = np.zeros((n, n))
    spaces: list[Space] = []
    for level in range(1, h+1):
        update = np.zeros((n, n))
        for reverse in (False, True):
            blocks = _blocks(n, level, reverse)
            m = blocks[0][0].stop-blocks[0][0].start
            omegas = [rng.standard_normal((m, s)) for _ in blocks]
            psis = [rng.standard_normal((m, t)) for _ in blocks]
            f = rng.integers(0, buckets, len(blocks))
            g = rng.integers(0, buckets, len(blocks))
            right_data: list[Array | None] = [None]*len(blocks)
            left_data: list[Array | None] = [None]*len(blocks)
            for a in range(buckets):
                chosen = np.flatnonzero(f == a)
                if chosen.size:
                    vectors = np.zeros((n, s))
                    for i in chosen:
                        vectors[blocks[i][1]] = omegas[i]
                    responses = counter.apply(vectors)-pilot@vectors
                    for i in chosen:
                        right_data[i] = responses[blocks[i][0]].copy()
                chosen = np.flatnonzero(g == a)
                if chosen.size:
                    vectors = np.zeros((n, t))
                    for i in chosen:
                        vectors[blocks[i][0]] = psis[i]
                    responses = counter.apply(vectors, transpose=True)-pilot.T@vectors
                    for i in chosen:
                        left_data[i] = responses[blocks[i][1]].T.copy()
            for i, (rows, cols) in enumerate(blocks):
                if right_data[i] is None or left_data[i] is None:
                    raise RuntimeError("Missing pilot sketch")
                q = _orth(right_data[i], rank_tolerance)
                spaces.append(Space(rows, cols, q))
                if q.shape[1]:
                    core = np.linalg.pinv(psis[i].T@q, rcond=rank_tolerance)@left_data[i]
                    update[rows, cols] = q@_truncate(core, k)
        pilot += update  # both orientations use the same frozen past
    b, final_queries, rmax = fit_and_truncate(
        oracle, k, spaces, parameters.regression_width, rng, rank_tolerance)
    total = counter.queries+final_queries
    budget = parameters.budget(n, k)
    assert total <= budget
    return TwoStageApproximation(b, total, "two_stage_shared_regression", parameters,
                                 budget, rmax, counter.queries, final_queries)


def approximate_two_stage(
    oracle: MatvecOracle, k: int, epsilon: float,
    rng: np.random.Generator | None = None,
) -> TwoStageApproximation:
    """Theorem widths with the n-query exact-projection fallback."""
    params = theorem_parameters(oracle.n, k, epsilon)
    budget = params.budget(oracle.n, k)
    if budget >= oracle.n:
        counter = _Counter(oracle)
        a = counter.apply(np.eye(oracle.n))
        return TwoStageApproximation(project_hodlr(a, k), counter.queries,
                                     "n_query_baseline", None, oracle.n, 0, 0, 0)
    return two_stage_with_parameters(oracle, k, params, rng)
