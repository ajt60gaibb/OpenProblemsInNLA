"""Reference constructions and diagnostic algorithms for the NLA submissions.

Exact constructions use SymPy rationals. Functions ending in _float use
floating-point optimization and are NOT implementations of the exact
polynomial-bit algorithms asserted in the manuscripts.
"""
from __future__ import annotations
from itertools import product
from math import isqrt
from typing import Iterable, Sequence
import numpy as np
import sympy as sp
from scipy.optimize import linprog


def signs(n: int):
    return product((-1, 1), repeat=n)


def inverse_m_exact(A: sp.Matrix) -> bool:
    if A.rows != A.cols:
        raise ValueError('A must be square')
    if any(a < 0 for a in A):
        return False
    if A.det() == 0:
        return False
    B = A.inv()
    return all(B[i, j] <= 0 for i in range(A.rows)
               for j in range(A.cols) if i != j)


def inverse_m_vertices_exact(C: sp.Matrix, R: sp.Matrix) -> bool:
    if C.shape != R.shape or C.rows != C.cols or any(r < 0 for r in R):
        raise ValueError('Expected square center and nonnegative radius')
    n = C.rows
    for i in range(n):
        zi = sp.diag(*[-1 if k == i else 1 for k in range(n)])
        for j in range(n):
            zj = sp.diag(*[-1 if k == j else 1 for k in range(n)])
            if not inverse_m_exact(C - zi * R * zj):
                return False
    return True


def entry_vertices(C: sp.Matrix, R: sp.Matrix):
    positions = [(i, j) for i in range(C.rows) for j in range(C.cols)
                 if R[i, j] != 0]
    for ss in signs(len(positions)):
        A = C.copy()
        for (i, j), s in zip(positions, ss):
            A[i, j] += s * R[i, j]
        yield A


def partition_tridiagonal(weights: Sequence[int], gates: Sequence[int] | None = None):
    """Return (center, radius, threshold, delta), with independent gate entries."""
    if not weights or any(type(w) is not int or w <= 0 for w in weights):
        raise ValueError('weights must be a nonempty sequence of positive integers')
    m, W = len(weights), sum(weights)
    delta = sp.Rational(1, 10 * W * W)
    layers = []
    for i, w in enumerate(weights):
        t = delta * w
        c, s = (1 - t*t)/(1 + t*t), 2*t/(1 + t*t)
        layers.extend([(s, -c, False), (-s/c, -1/c, False)])
        if i < m - 1:
            layers.extend([(sp.Integer(0), sp.Integer(0), True),
                           (sp.Integer(0), sp.Integer(-1), False)])
    n = len(layers)
    C, R = sp.zeros(n), sp.zeros(n)
    gate_index = 0
    for j, (a, beta, uncertain) in enumerate(layers):
        C[j, j] = a
        if j < n - 1:
            C[j, j+1] = 1
        if j:
            C[j, j-1] = beta
            if uncertain:
                R[j, j-1] = 1
                if gates is not None:
                    if len(gates) != m - 1 or any(q not in (-1, 1) for q in gates):
                        raise ValueError('gates must contain m-1 signs')
                    C[j, j-1] = gates[gate_index]
                    R[j, j-1] = 0
                gate_index += 1
    return C, R, 1 - delta*delta/2, delta


def continuant(T: sp.Matrix):
    if T.rows != T.cols:
        raise ValueError('T must be square')
    p0, p1 = sp.Integer(0), sp.Integer(1)
    for j in range(T.rows):
        beta = 0 if j == 0 else T[j, j-1] * T[j-1, j]
        p0, p1 = p1, sp.cancel(T[j, j] * p1 - beta * p0)
    return p1


def maxcut_matrix(v: int, edges: Sequence[tuple[int, int]], k: int):
    if v < 2 or not edges or not 1 <= k <= len(edges):
        raise ValueError('Require v>=2, a nonempty simple graph, and 1<=k<=m')
    if any(not (0 <= p < q < v) for p, q in edges) or len(set(edges)) != len(edges):
        raise ValueError('Edges must be distinct ordered pairs 0<=p<q<v')
    m, N = len(edges), 1 + v + len(edges)
    K = 12 * N * N
    B = sp.zeros(v, m)
    for e, (p, q) in enumerate(edges):
        B[p, e], B[q, e] = 1, -1
    A = 2 * sp.eye(N)
    A[0, 1:1+v] = K * sp.ones(1, v)
    A[1:1+v, 1+v:N] = K * B
    q = isqrt(144*N*N*k)
    return A, 8*N**3*q, B, K


def positive_definite_exact(H: sp.Matrix) -> bool:
    """Exact unpivoted LDL positive-definiteness test for symmetric rationals."""
    if H.rows != H.cols or H != H.T:
        raise ValueError('H must be symmetric and square')
    n = H.rows
    L, d = sp.eye(n), []
    for j in range(n):
        pivot = sp.cancel(H[j, j] - sum(L[j, k]**2*d[k] for k in range(j)))
        if pivot <= 0:
            return False
        d.append(pivot)
        for i in range(j+1, n):
            L[i, j] = sp.cancel((H[i, j] - sum(L[i, k]*L[j, k]*d[k]
                                                  for k in range(j))) / pivot)
    return True


def inverse_norm_certificate_exact(A: sp.Matrix, threshold, ss: Sequence[int]) -> bool:
    if len(ss) != A.rows or any(s not in (-1, 1) for s in ss):
        raise ValueError('Need one sign for each diagonal coordinate')
    M = A - sp.diag(*ss)
    if M.det() == 0:
        raise ValueError('Certificate matrix is singular')
    if threshold <= 0:
        return True
    return not positive_definite_exact(threshold**2 * M.T * M - sp.eye(A.rows))


def inverse_m_float(A, tol: float = 1e-10) -> bool:
    A = np.asarray(A, dtype=float)
    if np.min(A) < -tol:
        return False
    try:
        B = np.linalg.inv(A)
    except np.linalg.LinAlgError:
        return False
    n = A.shape[0]
    return bool(np.all(np.diag(B) > tol) and
                np.max(B - np.diag(np.diag(B))) <= tol)


def inverse_m_vertices_float(C, R, tol: float = 1e-10) -> bool:
    C, R = np.asarray(C, float), np.asarray(R, float)
    n = len(C)
    for i in range(n):
        zi = np.ones(n); zi[i] = -1
        for j in range(n):
            zj = np.ones(n); zj[j] = -1
            if not inverse_m_float(C - zi[:, None]*R*zj[None, :], tol):
                return False
    return True


def _feasible_float(A_ub, b_ub, A_eq, b_eq, bounds):
    res = linprog(np.zeros(A_ub.shape[1]), A_ub=A_ub, b_ub=b_ub,
                  A_eq=A_eq, b_eq=b_eq, bounds=bounds, method='highs',
                  options={'presolve': False})
    if res.status == 0:
        return True
    if res.status == 2:
        return False
    raise RuntimeError(f'LP status {res.status}: {res.message}')


def av01_recognize_float(A, b) -> bool:
    """Diagnostic n+1-LP algorithm, not a certified rational LP solver."""
    A, b = np.asarray(A, float), np.asarray(b, float)
    if A.ndim != 2 or A.shape[0] != A.shape[1] or b.shape != (len(A),):
        raise ValueError('Incompatible square matrix and vector dimensions')
    n = len(A)
    if np.any(b <= 0):
        return False
    G = np.vstack((A + np.eye(n), A - np.eye(n)))
    # Normalization implies ||r||_1 <= 1; the box is mathematically redundant.
    if _feasible_float(G, np.zeros(2*n), -A.sum(axis=0)[None, :],
                       np.array([1.]), [(-1., 1.)]*n):
        return False
    for i in range(n):
        if _feasible_float(G, np.tile(b, 2), A[i:i+1], b[i:i+1],
                           [(None, None)]*n):
            return False
    return True


def inverse_m_ave_float(C, R, sigma, b):
    C, R, sigma, b = map(lambda a: np.asarray(a, float), (C, R, sigma, b))
    n = len(b)
    P, Q = C - sigma[:, None]*R, C + sigma[:, None]*R
    X, Y = np.linalg.inv(Q), np.linalg.inv(P)
    res = linprog(np.ones(n), A_ub=np.vstack((-X, -Y)),
                  b_ub=np.r_[np.zeros(n), Y @ b], bounds=[(0., None)]*n,
                  method='highs')
    if not res.success:
        raise RuntimeError(f'Inverse-M LP failed: {res.message}')
    u, v = Y @ (res.x + b), X @ res.x
    return u-v, u, v


def inverse_m_hull_float(C, R, bc, br):
    n = len(bc)
    lower, upper = np.empty(n), np.empty(n)
    for i in range(n):
        sigma = -np.ones(n); sigma[i] = 1
        upper[i] = inverse_m_ave_float(C, R, sigma, bc + sigma*br)[0][i]
        sigma = -sigma
        lower[i] = inverse_m_ave_float(C, R, sigma, bc + sigma*br)[0][i]
    return lower, upper
