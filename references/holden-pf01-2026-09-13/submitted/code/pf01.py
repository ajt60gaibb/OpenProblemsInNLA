"""Constructive real PSD factors and proved bounds for PF-01.

The factors are an upper-bound certificate, not a minimality certificate.
Index subsets with integers 0,...,n-1.  A column J of the original matrix
uses B for K = complement(J).
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations
from math import isqrt, sqrt
from numbers import Integral
from typing import Iterable
import numpy as np
from numpy.typing import NDArray

Array = NDArray[np.float64]


def _order(n: int) -> int:
    if isinstance(n, bool) or not isinstance(n, Integral) or n < 3:
        raise ValueError("n must be an integer at least 3")
    return int(n)


def triangular_ceiling(m: int) -> int:
    """Smallest integer k for which k(k+1)/2 >= m (integer arithmetic)."""
    if m < 1:
        raise ValueError("m must be positive")
    k = max(1, (isqrt(1 + 8 * m) - 1) // 2)
    while k * (k + 1) // 2 < m:
        k += 1
    return k


def packing(d: int) -> tuple[int, int]:
    """Minimize a+b subject to a,b positive integers and ab >= d."""
    if d < 1:
        raise ValueError("d must be positive")
    k = isqrt(4 * d)
    if k * k < 4 * d:
        k += 1
    a, b = k // 2, k - k // 2
    assert a * b >= d
    assert (k - 1) ** 2 // 4 < d
    return a, b


def proved_bounds(n: int) -> tuple[int, int]:
    """Bounds for the canonical range n >= 5.

    The lower bound 4 at n=5 uses Colbrook's cited result.  The strict
    triangular bound and the upper bound are proved in the included paper.
    """
    n = _order(n)
    if n < 5:
        raise ValueError("The canonical PF-01 range is n >= 5")
    return max(4, triangular_ceiling(n + 1)), sum(packing(n - 2))


def prior_upper(n: int) -> int:
    n = _order(n)
    return sum(packing(2 * ((n - 1) // 2)))


@dataclass(frozen=True)
class Factor:
    subset: tuple[int, ...]
    lam: float
    transverse: Array
    A: Array
    B: Array


class FactorFactory:
    """On-demand factors without enumerating the exponentially many subsets."""

    def __init__(self, n: int):
        self.n = _order(n)
        self.r = n // 2
        self.radius = sqrt(self.r * (n - self.r) / n)
        self.a, self.b = packing(n - 2)
        self.size = self.a + self.b
        # Helmert coordinates h_2,...,h_{n-1}; h_1 is the pole direction.
        H = np.zeros((n - 2, n), dtype=float)
        for row, j in enumerate(range(2, n)):
            H[row, :j] = 1.0 / sqrt(j * (j + 1))
            H[row, j] = -j / sqrt(j * (j + 1))
        self.H = H

    def subset(self, subset: Iterable[int]) -> tuple[int, ...]:
        values = tuple(subset)
        if any(isinstance(i, bool) or not isinstance(i, Integral) for i in values):
            raise ValueError("Subset indices must be integers")
        values = tuple(sorted(int(i) for i in values))
        if len(values) != self.r or len(set(values)) != self.r:
            raise ValueError(f"Expected {self.r} distinct indices")
        if values[0] < 0 or values[-1] >= self.n:
            raise ValueError("Subset index out of range")
        return values

    def factors(self, subset: Iterable[int]) -> Factor:
        indices = self.subset(subset)
        x = np.zeros(self.n, dtype=float)
        x[list(indices)] = 1.0
        t = (x[0] - x[1]) / sqrt(2.0)
        lam = self.radius - t
        if not lam > 0:
            raise ArithmeticError("The selected stereographic chart is singular")
        y = self.H @ x
        Y = np.zeros(self.a * self.b, dtype=float)
        Y[: self.n - 2] = y
        Y = Y.reshape(self.a, self.b)
        # A = lam [Z;I_b][Z^T,I_b], B = lam/2 [I_a;-Z^T][I_a,-Z].
        Z = Y / lam
        R = np.vstack((Z, np.eye(self.b)))
        S = np.vstack((np.eye(self.a), -Z.T))
        A = lam * (R @ R.T)
        B = (lam / 2.0) * (S @ S.T)
        return Factor(indices, lam, Y, A, B)

    def column_factor(self, column: Iterable[int]) -> Array:
        values = tuple(column)
        if any(isinstance(i, bool) or not isinstance(i, Integral) for i in values):
            raise ValueError("Column indices must be integers")
        values = tuple(int(i) for i in values)
        if (len(values) != self.n - self.r or len(set(values)) != len(values)
                or min(values) < 0 or max(values) >= self.n):
            raise ValueError("Invalid column subset")
        return self.factors(set(range(self.n)).difference(values)).B

    def enumerate(self) -> tuple[list[tuple[int, ...]], Array, Array]:
        """Enumerate all factors. Memory is exponential in n; use only small n."""
        subsets = list(combinations(range(self.n), self.r))
        values = [self.factors(s) for s in subsets]
        return subsets, np.stack([v.A for v in values]), np.stack([v.B for v in values])


def distance_matrix(subsets: list[tuple[int, ...]], n: int) -> NDArray[np.int64]:
    X = np.zeros((len(subsets), n), dtype=np.int64)
    for i, subset in enumerate(subsets):
        X[i, list(subset)] = 1
    return n // 2 - X @ X.T


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, nargs="?", default=7)
    parser.add_argument("--save", help="Write all factors to this .npz file (small n only)")
    args = parser.parse_args()
    factory = FactorFactory(args.n)
    print(f"n={args.n}, factor size={factory.size}, packing=({factory.a},{factory.b})")
    if args.n >= 5:
        print("Proved lower and upper bounds:", proved_bounds(args.n))
    if args.save:
        if args.n > 14:
            parser.error("Refusing exponential enumeration for n>14; use FactorFactory.factors")
        subsets, A, B = factory.enumerate()
        np.savez_compressed(args.save, subsets=np.asarray(subsets), A=A, B=B)
        print(f"Saved {len(subsets)} row and complemented-column factors to {args.save}")
