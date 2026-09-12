"""Small-instance exact-arithmetic tools for the KE-01 research report.

These routines are verification implementations, not implementations of the
fast-matrix-multiplication or sparse-embedding asymptotic bounds in the report.
CGLS uses Fraction arithmetic and never explicitly forms A.T @ A.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable, Sequence

Q = Fraction


def dot(x: Sequence[Q], y: Sequence[Q]) -> Q:
    if len(x) != len(y):
        raise ValueError("Dot-product dimensions differ")
    return sum((a * b for a, b in zip(x, y)), Q(0))


@dataclass(frozen=True)
class SparseMatrix:
    nrows: int
    ncols: int
    entries: tuple[tuple[int, int, Q], ...]

    @classmethod
    def from_coo(cls, nrows: int, ncols: int,
                 entries: Iterable[tuple[int, int, object]]) -> "SparseMatrix":
        if (not isinstance(nrows, int) or not isinstance(ncols, int)
                or nrows < 1 or ncols < 1):
            raise ValueError("Matrix dimensions must be positive integers")
        accumulated: dict[tuple[int, int], Q] = {}
        for i, j, value in entries:
            if (not isinstance(i, int) or not isinstance(j, int)
                    or not (0 <= i < nrows and 0 <= j < ncols)):
                raise ValueError("COO index out of range")
            accumulated[i, j] = accumulated.get((i, j), Q(0)) + Q(value)
        cleaned = tuple((i, j, x) for (i, j), x in sorted(accumulated.items()) if x)
        return cls(nrows, ncols, cleaned)

    @property
    def nnz(self) -> int:
        return len(self.entries)

    def mv(self, x: Sequence[Q], transpose: bool = False) -> list[Q]:
        expected = self.nrows if transpose else self.ncols
        if len(x) != expected:
            raise ValueError("Matrix-vector dimensions differ")
        out = [Q(0)] * (self.ncols if transpose else self.nrows)
        for i, j, a in self.entries:
            if transpose:
                out[j] += a * x[i]
            else:
                out[i] += a * x[j]
        return out


@dataclass
class CGLSResult:
    x: list[Q]
    residual_squared: list[Q]
    iterations: int
    matvec_calls: int
    converged: bool


def cgls_exact(a: SparseMatrix, b: Sequence[Q], epsilon: Q = Q(0),
               max_iterations: int | None = None) -> CGLSResult:
    """Exact CGLS, with a physical relative-residual stopping test.

    epsilon=0 requests exact termination.  For the KE-01 hypotheses A is
    nonsingular and square; singular inputs may raise ArithmeticError.
    """
    if a.nrows != a.ncols or len(b) != a.nrows:
        raise ValueError("This verifier requires a square matrix and matching b")
    b = [Q(t) for t in b]
    epsilon = Q(epsilon)
    if epsilon < 0 or epsilon >= 1:
        raise ValueError("epsilon must be in [0,1)")
    b2 = dot(b, b)
    if not b2:
        raise ValueError("b must be nonzero")
    cap = a.ncols if max_iterations is None else max_iterations
    if cap < 0:
        raise ValueError("max_iterations must be nonnegative")
    x, r = [Q(0)] * a.ncols, b.copy()
    s = a.mv(r, transpose=True)
    calls = 1
    p = s.copy()
    gamma = dot(s, s)
    history = [b2]
    for step in range(cap):
        if history[-1] <= epsilon * epsilon * b2:
            return CGLSResult(x, history, step, calls, True)
        if not gamma:
            raise ArithmeticError("Normal residual vanished before physical residual")
        ap = a.mv(p)
        calls += 1
        denom = dot(ap, ap)
        if denom <= 0:
            raise ArithmeticError("Nonpositive CGLS denominator")
        alpha = gamma / denom
        x = [xx + alpha * pp for xx, pp in zip(x, p)]
        r = [rr - alpha * aa for rr, aa in zip(r, ap)]
        history.append(dot(r, r))
        if history[-1] <= epsilon * epsilon * b2:
            return CGLSResult(x, history, step + 1, calls, True)
        s = a.mv(r, transpose=True)
        calls += 1
        next_gamma = dot(s, s)
        beta = next_gamma / gamma
        p = [ss + beta * pp for ss, pp in zip(s, p)]
        gamma = next_gamma
    return CGLSResult(x, history, cap, calls,
                      history[-1] <= epsilon * epsilon * b2)


def psd_principal_basis(w):
    """Exact divide-and-conquer principal rank profile of a PSD SymPy matrix.

    This implementation uses SymPy's ordinary dense kernels.  Its recursion,
    when supplied fast matrix kernels, is the one analyzed in the report.
    """
    import sympy as sp
    if w.rows != w.cols or w != w.T:
        raise ValueError("Expected a square symmetric matrix")
    n = w.rows
    if n == 0:
        return []
    if n == 1:
        if w[0, 0] < 0:
            raise ValueError("Matrix is not PSD")
        return [0] if w[0, 0] else []
    h = n // 2
    upper, cross, lower = w[:h, :h], w[:h, h:], w[h:, h:]
    left = psd_principal_basis(upper)
    if left:
        core = upper.extract(left, left)
        link = cross.extract(left, list(range(n - h)))
        core_inv = core.inv()
        projected = upper.extract(list(range(h)), left) * core_inv * link
        if projected != cross:
            raise ValueError("Cross block is outside the range of the PSD diagonal block")
        schur = lower - link.T * core_inv * link
    else:
        if cross != sp.zeros(h, n - h):
            raise ValueError("Zero PSD diagonal block has a nonzero cross block")
        schur = lower
    right = psd_principal_basis(schur)
    return left + [h + j for j in right]


def recover_flat_shift(m, k: int):
    """Recover alpha exactly from M=alpha I+R, R PSD, rank(R)<=k.

    Requires dimension > 2*k.  Uses a (2*k+1)-order principal characteristic
    polynomial and k repeated gcd-with-derivative operations.  The routine
    does not validate the full structural promise; tests do so separately.
    """
    import sympy as sp
    if k < 0 or m.rows != m.cols or m.rows <= 2 * k:
        raise ValueError("Need a square matrix of dimension greater than 2*k")
    t = sp.Symbol("t")
    size = 2 * k + 1
    p = sp.Poly(m[:size, :size].charpoly(t).as_expr(), t)
    for _ in range(k):
        p = sp.gcd(p, p.diff()).monic()
    d = p.degree()
    if d < 1:
        raise ValueError("The flat-tail promise was not met")
    alpha = -p.nth(d - 1) / (d * p.nth(d))
    if sp.expand(p.as_expr() - (t - alpha) ** d) != 0:
        raise ValueError("No unique surviving repeated root")
    return sp.factor(alpha), d
