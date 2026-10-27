"""Nonadaptive finite-family matrix approximation for RE-06.

The mathematical guarantee is in solution.pdf / solution.tex and uses exact
real arithmetic. This is a floating-point reference implementation, not a
finite-precision certification. The theorem's conservative dimensions often
activate exact recovery. User-selected dimensions run the same sketching
procedure but do not inherit the theorem's 0.99 probability automatically.

Only collect_answers() accesses the matrix-vector oracles. Every query vector
and its side are stored in an immutable QueryPlan before that function runs.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import isqrt, isfinite, sqrt
from typing import Callable, Sequence

import numpy as np
from numpy.typing import NDArray

Array = NDArray[np.float64]
Matvec = Callable[[Array], Array]


def _ceil(x: Fraction) -> int:
    return -((-x.numerator) // x.denominator)


def _readonly(x: Array) -> Array:
    a = np.array(x, dtype=np.float64, copy=True)
    if a.ndim != 2 or not np.isfinite(a).all():
        raise ValueError("Query blocks must be finite, real two-dimensional arrays.")
    a.setflags(write=False)
    return a


@dataclass(frozen=True)
class Parameters:
    L: int
    r: int
    s: int
    k: int
    ell: int

    @property
    def total(self) -> int:
        return self.s + self.k + self.ell


def theorem_parameters(m: int, epsilon: float) -> Parameters:
    """Compute the explicit sufficient dimensions using integer arithmetic.

    Fraction avoids overflow in dimension calculations for small positive
    floating-point epsilon. It does not make the linear algebra exact.
    """
    if not isinstance(m, int) or isinstance(m, bool) or m < 2:
        raise ValueError("m must be an integer at least two.")
    if not isfinite(epsilon) or not 0.0 < epsilon < 0.5:
        raise ValueError("epsilon must be finite and lie strictly between 0 and 1/2.")
    eta = Fraction.from_float(float(epsilon)) / 4
    L = (2 * m - 1).bit_length()  # ceil(log_2(2m)), without a logarithm primitive
    r = isqrt(L)
    r += (r * r < L)
    s = _ceil(Fraction(32 * L, r) / eta + 64 / eta**2)
    k = r + 1 + _ceil(256 * r / eta)
    ell = k + 1 + _ceil(256 * k / eta)
    return Parameters(L, r, s, k, ell)


@dataclass(frozen=True)
class QueryPlan:
    n: int
    mode: str
    G0: Array  # exact mode: the identity; sketch mode: normalized first sketch
    G1: Array
    H: Array
    dimensions_are_theorem_sufficient: bool = False

    def __post_init__(self) -> None:
        if not isinstance(self.n, int) or self.n < 1:
            raise ValueError("n must be a positive integer.")
        if self.mode not in {"exact", "sketch"}:
            raise ValueError("mode must be 'exact' or 'sketch'.")
        for name in ("G0", "G1", "H"):
            block = _readonly(getattr(self, name))
            if block.shape[0] != self.n:
                raise ValueError(f"{name} has the wrong number of rows.")
            object.__setattr__(self, name, block)
        if self.mode == "exact":
            if self.G0.shape != (self.n, self.n) or not np.array_equal(self.G0, np.eye(self.n)):
                raise ValueError("Exact plans must query all standard basis vectors.")
            if self.G1.shape[1] or self.H.shape[1]:
                raise ValueError("Exact plans must not contain extra blocks.")
        elif self.G0.shape[1] < 1 or self.G1.shape[1] < 1 or self.H.shape[1] < self.G1.shape[1] + 2:
            raise ValueError("Sketch plans need s,k >= 1 and ell >= k+2.")

    @property
    def query_count(self) -> int:
        return self.G0.shape[1] + self.G1.shape[1] + self.H.shape[1]

    def queries(self) -> tuple[tuple[str, Array], ...]:
        """The complete, precommitted ordered list of query sides and vectors."""
        return tuple(
            [("A", self.G0[:, j]) for j in range(self.G0.shape[1])]
            + [("A", self.G1[:, j]) for j in range(self.G1.shape[1])]
            + [("AT", self.H[:, j]) for j in range(self.H.shape[1])]
        )


def make_sketch_plan(n: int, s: int, k: int, ell: int, seed: int = 0) -> QueryPlan:
    """Create all independent Gaussian blocks before any oracle is called.

    These user-selected dimensions are experimental, not automatically the
    conservative sufficient dimensions in the theorem.
    """
    if not all(isinstance(v, int) and v >= 1 for v in (n, s, k, ell)):
        raise ValueError("n,s,k,ell must be positive integers.")
    if ell < k + 2:
        raise ValueError("ell must be at least k+2.")
    seeds = np.random.SeedSequence(seed).spawn(3)
    rng0, rng1, rngh = (np.random.default_rng(z) for z in seeds)
    return QueryPlan(n, "sketch", rng0.standard_normal((n, s)) / sqrt(s),
                     rng1.standard_normal((n, k)), rngh.standard_normal((n, ell)))


def make_theorem_plan(n: int, m: int, epsilon: float, seed: int = 0) -> QueryPlan:
    """The proved parameter choice, with a predetermined exact-recovery branch."""
    if not isinstance(n, int) or n < 1:
        raise ValueError("n must be a positive integer.")
    p = theorem_parameters(m, epsilon)
    if n <= p.total:
        return QueryPlan(n, "exact", np.eye(n), np.empty((n, 0)),
                         np.empty((n, 0)), True)
    raw = make_sketch_plan(n, p.s, p.k, p.ell, seed)
    return QueryPlan(n, "sketch", raw.G0, raw.G1, raw.H, True)


@dataclass(frozen=True)
class Answers:
    AG0: Array
    AG1: Array
    ATH: Array
    oracle_calls: int


def collect_answers(plan: QueryPlan, matvec: Matvec, rmatvec: Matvec) -> Answers:
    """Issue exactly the stored queries, with no selection or adaptation."""
    results: list[Array] = []
    for side, vector in plan.queries():
        value = np.asarray((matvec if side == "A" else rmatvec)(vector.copy()), dtype=float)
        if value.shape != (plan.n,) or not np.isfinite(value).all():
            raise ValueError("An oracle returned a nonfinite vector or a wrong shape.")
        results.append(value.copy())
    s, k, ell = plan.G0.shape[1], plan.G1.shape[1], plan.H.shape[1]
    def block(start: int, width: int) -> Array:
        return np.column_stack(results[start:start + width]) if width else np.empty((plan.n, 0))
    return Answers(block(0, s), block(s, k), block(s + k, ell), len(results))


@dataclass(frozen=True)
class Result:
    selected_index: int
    warm_index: int | None
    surrogate: Array
    oracle_calls: int
    mode: str
    numerical_range_rank: int


def _family(family: Sequence[Array], n: int) -> list[Array]:
    if len(family) < 2:
        raise ValueError("At least two candidates are required.")
    output = []
    for b in family:
        a = np.asarray(b, dtype=float)
        if a.shape != (n, n) or not np.isfinite(a).all():
            raise ValueError("Candidates must be finite real n-by-n matrices.")
        output.append(a)
    return output


def postprocess(plan: QueryPlan, answers: Answers, family: Sequence[Array]) -> Result:
    """Reconstruct and select using stored answers only; no oracle arguments."""
    candidates = _family(family, plan.n)
    if answers.oracle_calls != plan.query_count:
        raise ValueError("The answer count does not match the precommitted plan.")
    if plan.mode == "exact":
        surrogate = np.array(answers.AG0, copy=True)
        index = min(range(len(candidates)), key=lambda i: np.linalg.norm(surrogate - candidates[i], "fro"))
        return Result(index, None, surrogate, answers.oracle_calls, "exact", plan.n)

    # This choice intentionally uses only the first sketch, never AG1 or ATH.
    first_scores = [np.linalg.norm(answers.AG0 - b @ plan.G0, "fro") for b in candidates]
    warm = int(np.argmin(first_scores))
    b0 = candidates[warm]
    Y = answers.AG1 - b0 @ plan.G1
    W = answers.ATH.T - plan.H.T @ b0
    U, singular_values, _ = np.linalg.svd(Y, full_matrices=False)
    if singular_values.size == 0 or singular_values[0] == 0:
        rank = 0
    else:
        # The proof uses exact rank; this is the usual floating-point substitute.
        tolerance = np.finfo(float).eps * max(Y.shape) * singular_values[0]
        rank = int(np.sum(singular_values > tolerance))
    if rank == 0:
        surrogate = b0.copy()
    else:
        Q = U[:, :rank]
        coefficients, _, observed_rank, _ = np.linalg.lstsq(plan.H.T @ Q, W, rcond=None)
        if observed_rank < rank:
            raise np.linalg.LinAlgError("Numerically rank-deficient regression sketch; exact-arithmetic proof does not cover this numerical failure.")
        surrogate = b0 + Q @ coefficients
    index = min(range(len(candidates)), key=lambda i: np.linalg.norm(surrogate - candidates[i], "fro"))
    return Result(index, warm, surrogate, answers.oracle_calls, "sketch", rank)


def approximate(family: Sequence[Array], n: int, epsilon: float,
                matvec: Matvec, rmatvec: Matvec, seed: int = 0) -> Result:
    """Run the theorem-parameter algorithm through matrix-vector oracles."""
    _family(family, n)
    plan = make_theorem_plan(n, len(family), epsilon, seed)
    return postprocess(plan, collect_answers(plan, matvec, rmatvec), family)
