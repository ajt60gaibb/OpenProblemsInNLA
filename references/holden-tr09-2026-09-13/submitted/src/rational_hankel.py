#!/usr/bin/env python3
"""Exact rational 2r-1-term CP recovery benchmark.

This is an ALGEBRAIC comparator, NOT an admissible solution of TR-09.
It accepts only tensor slices and a rank bound. Unknown true factors are not
arguments. The correctness theorem assumes two full-column-rank factor modes
and pairwise noncollinear columns in the third mode.

The reference implementation uses SymPy rational matrices and finite-grid
random sketches. Its arithmetic complexity is polynomial, but rational bit
sizes and practical running times need not be polynomial in n and r alone.
"""
from __future__ import annotations
from dataclasses import dataclass
import random
from typing import Sequence
import sympy as sp


@dataclass
class Recovery:
    success: bool
    reason: str
    x: sp.Matrix | None = None
    y: sp.Matrix | None = None
    z: sp.Matrix | None = None
    grid_size: int = 0
    random_entries: int = 0


def represented_slices(x: sp.Matrix, y: sp.Matrix, z: sp.Matrix) -> list[sp.Matrix]:
    if x.cols != y.cols or y.cols != z.cols:
        raise ValueError('Factor widths must agree')
    return [x * sp.diag(*list(z.row(i))) * y.T for i in range(z.rows)]


def recover(slices: Sequence[sp.Matrix], rank: int, seed: int | None = None,
            grid_size: int | None = None, verify: bool = True) -> Recovery:
    """One bounded finite-grid trial; returns an explicit failure on bad sketches.

    For each fixed promised input, the theoretical success probability is at
    least 1-(rank**2+4*rank)/grid_size. A fixed pseudorandom seed is for
    reproducibility only; the theorem concerns independent uniform draws.
    """
    if not isinstance(rank, int) or rank < 1:
        raise ValueError('rank must be a positive integer')
    t = [sp.Matrix(a) for a in slices]
    n = len(t)
    if n < rank or any(a.shape != (n, n) for a in t):
        raise ValueError('Expected n cubic-tensor slices, n >= rank')
    if any(v.is_Rational is not True for a in t for v in a):
        raise ValueError('This reference implementation requires rational entries')
    degree_budget = rank*rank+4*rank
    m = 1 << ((4*degree_budget-1).bit_length()) if grid_size is None else grid_size
    if not isinstance(m, int) or m < 1:
        raise ValueError('grid_size must be a positive integer')
    rng = random.SystemRandom() if seed is None else random.Random(seed)
    count = 0
    def draw(rows: int, cols: int) -> sp.Matrix:
        nonlocal count
        count += rows*cols
        if m & (m-1) == 0:
            bits = (m-1).bit_length()
            values = [rng.getrandbits(bits)+1 for _ in range(rows*cols)]
        else:
            values = [rng.randint(1,m) for _ in range(rows*cols)]
        return sp.Matrix(rows, cols, values)
    # All sketches are sampled before any tensor-dependent computation.
    u, v, g, h, p, q = draw(n,rank), draw(n,rank), draw(n,1), draw(n,1), draw(rank,1), draw(rank,1)
    def fail(reason: str) -> Recovery:
        return Recovery(False, reason, grid_size=m, random_entries=count)
    mg = sum((g[i]*t[i] for i in range(n)), sp.zeros(n))
    mh = sum((h[i]*t[i] for i in range(n)), sp.zeros(n))
    m0, m1 = u.T*mg*v, u.T*mh*v
    if m0.det() == 0:
        return fail('singular contracted compression')
    inv0 = m0.inv()
    pa, pb = m1*inv0, m1.T*inv0.T
    def row_krylov(row: sp.Matrix, a: sp.Matrix) -> sp.Matrix:
        rows=[]
        for _ in range(rank):
            rows.append(row)
            row = row*a
        return sp.Matrix.vstack(*rows)
    ka, kb = row_krylov(p.T,pa), row_krylov(q.T,pb)
    if ka.det() == 0 or kb.det() == 0:
        return fail('singular row-Krylov matrix')
    compressed = [u.T*a*v for a in t]
    hs = [ka*a*kb.T for a in compressed]
    k = 2*rank-1
    moments = sp.zeros(k,n)
    for idx,a in enumerate(hs):
        for power in range(k):
            i=min(power,rank-1); j=power-i
            moments[power,idx]=a[i,j]
        if verify and any(a[i,j] != moments[i+j,idx] for i in range(rank) for j in range(rank)):
            return fail('Hankel identity failed: promise or sketch condition violated')
    nodes = list(range(k))
    vz = sp.Matrix(rank,k,lambda i,j: sp.Integer(nodes[j])**i)
    wz = sp.Matrix(k,k,lambda i,j: sp.Integer(nodes[j])**i)
    zz = (wz.inv()*moments).T
    la, lb = mg*v*inv0, mg.T*u*inv0.T
    xx, yy = la*ka.inv()*vz, lb*kb.inv()*vz
    if verify and represented_slices(xx,yy,zz) != t:
        return fail('exact reconstruction failed: promise or sketch condition violated')
    return Recovery(True, 'exact tensor reconstruction', xx, yy, zz, m, count)
