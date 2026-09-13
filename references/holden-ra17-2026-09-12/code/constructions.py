"""Explicit real-linear measurement and admissible-kernel constructions.

Matrices and identities are exact (SymPy integers/rationals). Row-major
vectorization is used throughout. These routines are illustrative algebraic
constructions, not a numerically optimized reconstruction algorithm.
"""
from __future__ import annotations
from math import comb
from pathlib import Path
import json
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]

def validate(d: int, r: int) -> None:
    if not isinstance(d, int) or not isinstance(r, int) or d < 2 or not 1 <= r <= d // 2:
        raise ValueError('require integers d >= 2 and 1 <= r <= floor(d/2)')

def antidiagonal_measurements(d: int, r: int) -> tuple[sp.Matrix, sp.Matrix]:
    """Return (W,B) with W of size m0 x d^2 and B of size d^2 x (d-2r)^2.

    W contains consecutive finite differences on long anti-diagonals and
    coordinate measurements on short ones. B evaluates low-degree polynomials.
    The first-nonzero-anti-diagonal proof in the paper certifies minimum rank.
    """
    validate(d, r)
    k = 2 * r
    rows, columns = [], []
    for diagonal in range(2 * d - 1):
        positions = [(i, diagonal - i) for i in range(d) if 0 <= diagonal - i < d]
        length = len(positions)
        if length <= k:
            for i, j in positions:
                row = [0] * (d * d); row[d * i + j] = 1; rows.append(row)
        else:
            dimension = length - k
            for degree in range(dimension):
                column = [0] * (d * d)
                for index, (i, j) in enumerate(positions):
                    column[d * i + j] = (index + 1) ** degree
                columns.append(column)
            for shift in range(k):
                row = [0] * (d * d)
                for offset in range(dimension + 1):
                    i, j = positions[shift + offset]
                    row[d * i + j] = (-1) ** offset * comb(dimension, offset)
                rows.append(row)
    W = sp.Matrix(rows)
    B = sp.Matrix.hstack(*(sp.Matrix(x) for x in columns)) if columns else sp.zeros(d*d, 0)
    return W, B

def quaternion_product(x: list, y: list) -> list:
    a, b, c, d = x; e, f, g, h = y
    return [a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f, a*h+b*g-c*f+d*e]

def conjugate(x: list) -> list:
    return [x[0]] + [-u for u in x[1:]]

def octonion_product(x: list, y: list) -> list:
    """Cayley-Dickson convention (a,b)(c,d)=(ac-conj(d)b, da+b conj(c))."""
    a, b, c, d = x[:4], x[4:], y[:4], y[4:]
    ac = quaternion_product(a, c)
    db = quaternion_product(conjugate(d), b)
    da = quaternion_product(d, a)
    bc = quaternion_product(b, conjugate(c))
    return [u-v for u,v in zip(ac,db)] + [u+v for u,v in zip(da,bc)]

def left_multiplication_basis(size: int) -> list[sp.Matrix]:
    if size not in (4, 8):
        raise ValueError('size must be 4 (quaternions) or 8 (octonions)')
    product = quaternion_product if size == 4 else octonion_product
    units = [[int(i == j) for i in range(size)] for j in range(size)]
    return [sp.Matrix.hstack(*(sp.Matrix(product(x, y)) for y in units)) for x in units]

def hurwitz_basis(d: int) -> list[sp.Matrix]:
    """A rho(d)-dimensional space with X(x)^T X(x)=||x||^2 I_d.

    A real Clifford-periodicity construction: each 16-fold size increase adds
    eight anti-commuting skew generators. Dense output can be large for large d.
    """
    if not isinstance(d, int) or d < 1:
        raise ValueError('d must be a positive integer')
    odd, valuation = d, 0
    while odd % 2 == 0:
        odd //= 2; valuation += 1
    periods, residue = divmod(valuation, 4)
    if residue == 0:
        generators, size = [], 1
    elif residue == 1:
        generators, size = [sp.Matrix([[0,-1],[1,0]])], 2
    else:
        size = 2 ** residue
        generators = left_multiplication_basis(size)[1:]
    if periods:
        octonions = left_multiplication_basis(8)
        zero = sp.zeros(8)
        clifford8 = [zero.row_join(O).col_join(O.row_join(zero)) for O in octonions[1:]]
        clifford8.append(zero.row_join(sp.eye(8)).col_join((-sp.eye(8)).row_join(zero)))
        grading = sp.eye(16)
        for A in clifford8: grading = grading * A
        for _ in range(periods):
            generators = ([sp.kronecker_product(G, grading) for G in generators]
                          + [sp.kronecker_product(sp.eye(size), A) for A in clifford8])
            size *= 16
    basis = [sp.eye(size)] + generators
    return [sp.kronecker_product(sp.eye(odd), B) for B in basis]

def xu_kernel_basis(variant: str = 'paper') -> list[sp.Matrix]:
    if variant not in ('paper', 'website'):
        raise ValueError('variant must be paper or website')
    data = json.loads((ROOT/'certificates'/f'measurements_{variant}.json').read_text())
    W = sp.Matrix(data['measurement_rows'])
    return [sp.Matrix(4, 4, v) for v in W.nullspace()]

def xu_octonion_lift(d: int, variant: str = 'paper') -> list[sp.Matrix]:
    """Five-dimensional kernel of minimum rank d-1 when d = 4 modulo 8."""
    if not isinstance(d, int) or d < 4 or d % 8 != 4:
        raise ValueError('require d >= 4 and d = 4 modulo 8')
    B, O = xu_kernel_basis(variant), left_multiplication_basis(8)
    copies = (d - 4) // 8
    return [sp.diag(B[i], *([O[i]] * copies)) for i in range(5)]

def annihilating_measurements(kernel: list[sp.Matrix]) -> sp.Matrix:
    """Convert a listed kernel basis into independent row-major measurements."""
    if not kernel or len({A.shape for A in kernel}) != 1:
        raise ValueError('provide a nonempty list of equally sized basis matrices')
    nrows, ncols = kernel[0].shape
    B = sp.Matrix.hstack(*(A.reshape(nrows*ncols, 1) for A in kernel))
    if B.rank() != len(kernel):
        raise ValueError('kernel matrices are not linearly independent')
    return sp.Matrix.vstack(*(v.T for v in B.T.nullspace()))
