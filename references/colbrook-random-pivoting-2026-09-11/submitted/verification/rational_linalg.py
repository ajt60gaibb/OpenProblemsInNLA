"""Small exact linear algebra helpers. Python 3.10+, standard library only.

These routines favor transparent arithmetic over speed. All entries are Fractions;
there is no conversion to binary floating point in a mathematical check.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence

Q = Fraction
Matrix = list[list[Fraction]]


def identity(n: int) -> Matrix:
    return [[Q(int(i == j)) for j in range(n)] for i in range(n)]


def transpose(a: Sequence[Sequence[Fraction]]) -> Matrix:
    return [list(column) for column in zip(*a)]


def multiply(a: Matrix, b: Matrix) -> Matrix:
    if not a or not b or len(a[0]) != len(b):
        raise ValueError("Incompatible or empty matrix dimensions")
    return [[sum((x * y for x, y in zip(row, col)), Q(0))
             for col in zip(*b)] for row in a]


def inverse(a: Matrix) -> Matrix:
    n = len(a)
    if not n or any(len(row) != n for row in a):
        raise ValueError("Expected a nonempty square matrix")
    aug = [list(row) + unit for row, unit in zip(a, identity(n))]
    for j in range(n):
        pivot = next((i for i in range(j, n) if aug[i][j]), None)
        if pivot is None:
            raise ArithmeticError("Singular matrix")
        aug[j], aug[pivot] = aug[pivot], aug[j]
        d = aug[j][j]
        aug[j] = [x / d for x in aug[j]]
        for i in range(n):
            if i != j and aug[i][j]:
                coefficient = aug[i][j]
                aug[i] = [x - coefficient * y for x, y in zip(aug[i], aug[j])]
    return [row[n:] for row in aug]


def submatrix(a: Matrix, rows: Sequence[int], cols: Sequence[int]) -> Matrix:
    return [[a[i][j] for j in cols] for i in rows]


def schur_residual(a: Matrix, rows: tuple[int, ...], cols: tuple[int, ...]) -> Matrix:
    """Return only the non-eliminated block of the interpolatory residual."""
    if len(rows) != len(cols):
        raise ValueError("Row and column pivot counts must agree")
    n = len(a)
    remaining_rows = tuple(i for i in range(n) if i not in rows)
    remaining_cols = tuple(j for j in range(n) if j not in cols)
    b = submatrix(a, remaining_rows, remaining_cols)
    if rows:
        update = multiply(
            multiply(submatrix(a, remaining_rows, cols),
                     inverse(submatrix(a, rows, cols))),
            submatrix(a, rows, remaining_cols),
        )
        b = [[x - y for x, y in zip(row, correction)]
             for row, correction in zip(b, update)]
    return b


def family(r: int, t: Fraction) -> tuple[Matrix, Matrix, Fraction]:
    """A = L diag(1, eps, ..., eps**r) L.T; eps = t**(r+1)**2.

    Mathematical indices in the note are one-based:
    L_ii = 1; L_ij = t**j / (i+j) for i>j; L_ij = 0 for i<j.
    """
    if not isinstance(r, int) or isinstance(r, bool) or r < 1:
        raise ValueError("r must be a positive integer")
    if not isinstance(t, Fraction) or not Q(0) < t < Q(1):
        raise ValueError("t must be a Fraction strictly between 0 and 1")
    n = r + 1
    eps = t ** (n * n)
    lower = identity(n)
    for i in range(n):
        for j in range(i):
            lower[i][j] = t ** (j + 1) / Q(i + j + 2)
    ld = [[entry * eps ** j for j, entry in enumerate(row)] for row in lower]
    return multiply(ld, transpose(lower)), lower, eps


def scaled_inverse_trace_and_rayleigh(lower: Matrix, eps: Fraction) -> tuple[Fraction, Fraction]:
    """Return exact bounds vnorm <= lambda_max(eps**r A^-1) <= tr_scaled.

    Consequently eps**r/tr_scaled <= lambda_min(A) <= eps**r/vnorm.
    Here vnorm = ||L^-T e_n||_2**2, not its square root.
    """
    li = inverse(lower)
    r = len(lower) - 1
    row_norms = [sum((x * x for x in row), Q(0)) for row in li]
    tr_scaled = sum((eps ** (r - i) * value for i, value in enumerate(row_norms)), Q(0))
    return tr_scaled, row_norms[-1]
