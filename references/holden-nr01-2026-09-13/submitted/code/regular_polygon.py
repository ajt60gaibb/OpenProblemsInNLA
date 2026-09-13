"""Regular-polygon slack matrices and a certified trigonometric fold formula.

The upper bound is due to Vandaele, Gillis, and Glineur (2017).
This is an independent, zero-aware implementation using integer angle indices.
The proof and exact verifier do not rely on floating-point residuals.
"""
from __future__ import annotations
from dataclasses import dataclass
from math import comb
from typing import Literal
import numpy as np


def require_n(n: int) -> int:
    if isinstance(n, bool) or not isinstance(n, (int, np.integer)) or n < 3:
        raise ValueError("n must be an integer at least 3")
    return int(n)


def upper_bound(n: int) -> int:
    n = require_n(n)
    k = (n - 1).bit_length()
    return 2*k - (n <= 3 * (1 << (k-2)))


def cyclic_facets(r: int, d: int) -> int:
    """Number of facets of the cyclic d-polytope with r vertices."""
    if not (2 <= d < r):
        raise ValueError("Require 2 <= d < r")
    a = d // 2
    if d % 2:
        return 2 * comb(r-a-1, a)
    return comb(r-a, a) + comb(r-a-1, a-1)


def ubt_capacity(r: int) -> int:
    if r < 3:
        return 0
    return max(cyclic_facets(r, d) for d in range(2, r))


def geometric_lower(n: int) -> int:
    """The UBT-based T(n) bound, NOT a complete best-known-rank table."""
    n = require_n(n)
    r = 3
    while ubt_capacity(r) < n:
        r += 1
    return r


def sine_index(a: np.ndarray | int, n: int) -> np.ndarray:
    """sin(a*pi/n), with mathematical zero indices set to zero exactly."""
    a = np.asarray(a, dtype=np.int64)
    b = a % (2*n)
    value = np.sin(np.pi * b / n)
    return np.where((b == 0) | (b == n), 0.0, value)


def c_index(t: np.ndarray | int, n: int) -> np.ndarray:
    """c_t = cos(pi/n)-cos((2t+1)pi/n), evaluated without cancellation."""
    t = np.asarray(t, dtype=np.int64) % n
    return 2 * sine_index(t, n) * sine_index(t+1, n)


def slack(n: int) -> np.ndarray:
    """The orientation stated in NR-01: S[i,j] = c_(i-j)."""
    n = require_n(n)
    index = np.arange(n)
    return c_index(index[:, None] - index[None, :], n)


@dataclass(frozen=True)
class Entry:
    """An exact algebraic expression: 0, 1, sin(a*pi/n), 2sin, or c_a."""
    kind: Literal["zero", "one", "sin", "2sin", "c"]
    angle: int = 0

    def numeric(self, n: int) -> float:
        if self.kind == "zero":
            return 0.0
        if self.kind == "one":
            return 1.0
        if self.kind == "c":
            return float(c_index(self.angle, n))
        value = float(sine_index(self.angle, n))
        return (2.0 if self.kind == "2sin" else 1.0) * value


ZERO = Entry("zero")
ONE = Entry("one")


def positive_sine(a: int, n: int, doubled: bool = False) -> Entry:
    # In this construction -n <= a <= n. The endpoint signs are exact.
    if not -n <= a <= n:
        raise AssertionError("Fold invariant violated: angle outside [-n,n]")
    return Entry("2sin" if doubled else "sin", a) if 0 < a < n else ZERO


def exact_expressions(n: int) -> tuple[list[list[Entry]], list[list[Entry]]]:
    """Return expressions W (n by U(n)), H (U(n) by n), with S_n=W H.

    Work first with B[i,j]=c_(j-i), then transpose the factors to match NR-01.
    No trigonometric quantities or floating-point decisions are used here.
    """
    n = require_n(n)
    rows = list(range(n))
    cols = list(range(n))
    ell = n
    left_columns: list[list[Entry]] = []
    right_rows: list[list[Entry]] = []
    while ell > 4:
        left_columns.append([positive_sine(ell-2*i, n, True) for i in rows])
        right_rows.append([positive_sine(2*j+1-ell, n) for j in cols])
        left_columns.append([positive_sine(2*i-ell, n, True) for i in rows])
        right_rows.append([positive_sine(ell-2*j-1, n) for j in cols])
        rows = [min(i, ell-i) for i in rows]
        cols = [min(j, ell-1-j) for j in cols]
        ell = (ell + 1) // 2
    for b in range(ell):
        left_columns.append([Entry("c", (b-i) % n) for i in rows])
        right_rows.append([ONE if j == b else ZERO for j in cols])
    r = len(left_columns)
    if r != upper_bound(n):
        raise AssertionError("Unexpected number of factors")
    # B = left @ right; S=B.T. Hence W=right.T, H=left.T.
    W = [[right_rows[a][i] for a in range(r)] for i in range(n)]
    H = [left_columns[a] for a in range(r)]
    return W, H


def factorization(n: int) -> tuple[np.ndarray, np.ndarray]:
    Wexp, Hexp = exact_expressions(n)
    return (np.array([[x.numeric(n) for x in row] for row in Wexp]),
            np.array([[x.numeric(n) for x in row] for row in Hexp]))


def balanced_capacity(r: int) -> int:
    """Rank-balance/UBT capacity proved in report: F(r,floor((r+1)/2))."""
    if r < 3:
        return 0
    return cyclic_facets(r, (r+1)//2)


def balanced_lower(n: int) -> int:
    """Proved rank-balance lower bound, not the full conjectured value."""
    n = require_n(n)
    r = 3
    while balanced_capacity(r) < n:
        r += 1
    return r


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("--save", type=str, help="optional output .npz")
    args = parser.parse_args()
    W, H = factorization(args.n)
    S = slack(args.n)
    print(f"n={args.n}; rank-balance lower={balanced_lower(args.n)}; known upper={W.shape[1]}")
    print(f"Comparison: unrestricted-dimension UBT lower={geometric_lower(args.n)}")
    print(f"min W={W.min():.3g}; min H={H.min():.3g}")
    print(f"max absolute residual={np.max(np.abs(S-W@H)):.3e}")
    print("Residual is a numerical cross-check, not the proof of exactness.")
    if args.save:
        np.savez_compressed(args.save, n=args.n, S=S, W=W, H=H)

