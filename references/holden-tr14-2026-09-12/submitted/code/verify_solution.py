#!/usr/bin/env python3
"""Reproducibility checks for TR-14. These tests are not a formal proof checker."""
from __future__ import annotations

import argparse
from dataclasses import asdict
from itertools import product
import json
from math import comb, lcm
from pathlib import Path
import platform
from random import Random
import time

import numpy as np
import sympy as sp

from hankel_rank import exact_hankel_rank


def rref_mod(matrix: np.ndarray, p: int) -> tuple[np.ndarray, list[int]]:
    a = np.array(matrix, dtype=np.int64, copy=True) % p
    rows, cols = a.shape
    pivots: list[int] = []
    row = 0
    for col in range(cols):
        candidates = np.flatnonzero(a[row:, col])
        if not len(candidates):
            continue
        pivot = row + int(candidates[0])
        a[[row, pivot]] = a[[pivot, row]]
        a[row] = (a[row] * pow(int(a[row, col]), -1, p)) % p
        factors = a[:, col].copy()
        factors[row] = 0
        a = (a - factors[:, None] * a[row][None, :]) % p
        pivots.append(col)
        row += 1
        if row == rows:
            break
    return a, pivots


def rank_mod(matrix: np.ndarray, p: int) -> int:
    return len(rref_mod(matrix, p)[1])


def row_basis(matrix: np.ndarray, p: int) -> np.ndarray:
    a, pivots = rref_mod(matrix, p)
    return a[:len(pivots)]


def nullspace_mod(matrix: np.ndarray, p: int) -> np.ndarray:
    a, pivots = rref_mod(matrix, p)
    cols = a.shape[1]
    free = [j for j in range(cols) if j not in pivots]
    basis = np.zeros((cols, len(free)), dtype=np.int64)
    for k, j in enumerate(free):
        basis[j, k] = 1
        for i, pivot in enumerate(pivots):
            basis[pivot, k] = -a[i, j] % p
    return basis


def jet_moments(D: int, multiplicities: tuple[int, ...],
                roots: tuple[int, ...] | None = None) -> list[int]:
    roots = roots if roots is not None else tuple(range(len(multiplicities)))
    h = []
    for j in range(D + 1):
        value = 0
        for alpha, ell in zip(roots, multiplicities):
            d = ell - 1
            if j >= d:
                value += comb(j, d) * alpha**(j-d)
        h.append(value)
    return h


def integer_partitions(n: int, minimum: int = 1):
    if n == 0:
        yield ()
        return
    for first in range(minimum, n + 1):
        for tail in integer_partitions(n-first, first):
            yield (first,) + tail


def test_rank_algorithm() -> dict:
    records = []
    # Multiplicity profiles, including reduced, local, mixed, and balanced cases.
    for m, n in [(3, 2), (3, 3), (3, 4), (4, 3), (5, 3), (5, 4), (7, 3)]:
        D = m * (n - 1)
        for r in range(1, min(D // 2 + 1, 6) + 1):
            for profile in integer_partitions(r):
                h = jet_moments(D, profile)
                expected = min(D-r+2, (m-1)*r-(m-2)*len(profile))
                out = exact_hankel_rank(m, n, h)
                assert out.apolar_degree == r, (m, n, profile, out)
                assert out.ordinary_rank == expected, (m, n, profile, out)
                if not out.balanced:
                    assert out.distinct_projective_roots == len(profile)
                records.append({"m": m, "n": n, "profile": profile,
                                "expected_rank": expected, "result": asdict(out)})
        # Reversal creates roots at infinity; it must preserve the exact rank.
        for profile in [(2,), (2, 1), (3,), (2, 2)]:
            if sum(profile) > D // 2 + 1:
                continue
            h = jet_moments(D, profile)
            direct = exact_hankel_rank(m, n, h)
            reverse = exact_hankel_rank(m, n, list(reversed(h)))
            assert direct.ordinary_rank == reverse.ordinary_rank
            assert reverse.apolar_degree == sum(profile)
            records.append({"m": m, "n": n, "profile": profile,
                            "reversed": True, "result": asdict(reverse)})
    zero = exact_hankel_rank(3, 2, [0, 0, 0, 0])
    assert zero.ordinary_rank == zero.symmetric_rank == zero.border_rank == 0
    try:
        exact_hankel_rank(3, 2, [0.0, 0, 0, 0])
        raise AssertionError("Floating-point input was not rejected")
    except TypeError:
        pass
    return {"cases": len(records), "zero_case": "PASS",
            "float_rejection": "PASS", "records": records}


def test_fourier_indices() -> dict:
    count = 0
    for m in range(2, 10):
        for ell in range(1, 13):
            N = (m-1)*(ell-1)+1
            hits = [d for d in range(m*(ell-1)+1) if (d-ell+1) % N == 0]
            assert hits == [ell-1], (m, ell, N, hits)
            count += 1
    return {"cases": count, "arithmetic": "exact integer congruences"}


def convolution_truncated(a: list[int], b: list[int], ell: int) -> list[int]:
    c = [0]*ell
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if i+j < ell:
                c[i+j] += x*y
    return c


def local_decomposition(m: int, n: int, profile: tuple[int, ...]):
    D = m*(n-1)
    periods = [(m-1)*(ell-1)+1 for ell in profile]
    common = lcm(*periods)
    mult = max(1, 1000 // common)
    while not sp.isprime(mult*common+1):
        mult += 1
    p = int(mult*common+1)
    assert p < 1000000  # keeps all numpy products safely inside signed int64
    generator = int(sp.primitive_root(p))
    factors, weights = [], []
    h = [0]*(D+1)
    for alpha, ell, N in zip(range(len(profile)), profile, periods):
        # A nontrivial unit w; lambda has u=w^m modulo z^ell.
        w = [1] + [(-1)**k*(k+1) for k in range(1, ell)]
        u = [1]+[0]*(ell-1)
        for _ in range(m):
            u = convolution_truncated(u, w, ell)
        for j in range(D+1):
            for d in range(min(j, ell-1)+1):
                h[j] += u[ell-1-d]*comb(j, d)*alpha**(j-d)
        root = pow(generator, (p-1)//N, p)
        for a in range(N):
            zeta = pow(root, a, p)
            vector = []
            for i in range(n):
                poly = [comb(i, d)*alpha**(i-d) if d <= i else 0 for d in range(ell)]
                f = convolution_truncated(w, poly, ell)
                vector.append(sum(c*pow(zeta, d, p) for d, c in enumerate(f)) % p)
            factors.append(vector)
            weights.append(pow(N, -1, p)*pow(zeta, -(ell-1), p) % p)
    for index in product(range(n), repeat=m):
        value = sum(weight * np.prod([vector[i] for i in index], dtype=object)
                    for vector, weight in zip(factors, weights)) % p
        assert value == h[sum(index)] % p, (m, n, profile, index, value, h[sum(index)] % p)
    return {"m": m, "n": n, "profile": profile, "prime": p,
            "summands": len(weights), "entries_checked": n**m,
            "nonconstant_local_units": True}


def test_decompositions() -> dict:
    cases = [(3, 3, (3,)), (5, 3, (2, 1, 1)), (5, 3, (2, 2)),
             (4, 4, (3, 1)), (3, 5, (3, 2, 1)), (7, 3, (2, 1))]
    records = [local_decomposition(*case) for case in cases]
    return {"cases": len(records), "arithmetic": "exact finite fields, primes recorded",
            "entries_checked": sum(x["entries_checked"] for x in records), "records": records}


def test_koszul() -> dict:
    rng = Random(14)
    p = 1009
    count, records = 0, []
    for m in (3, 5, 7, 9):
        for n in range(2, 10):
            q = n-1
            k = (m-1)//2
            a, b, c = k*q+1, q//2, (q+1)//2
            p1, p2 = a+b, a+c
            D = m*q
            E = np.zeros((3*a, p1+p2), dtype=np.int64)
            for i in range(a):
                E[i, i+b] = 1
                E[a+i, i] = -1
                E[a+i, p1+i+c] = 1
                E[2*a+i, p1+i] = -1
            assert rank_mod(E, p) == p1+p2
            patterns = {
                "random": [rng.randint(-4, 4) for _ in range(D+1)],
                "terminal": [int(j == min(q+1, D//2)) for j in range(D+1)],
                "mixed": [int(j == 1)+1+pow(2, j, p) for j in range(D+1)],
                "zero": [0]*(D+1),
            }
            for name, h in patterns.items():
                C = np.array([[h[i+j] for j in range(p2)] for i in range(p1)], dtype=np.int64)
                J = np.zeros((p1+p2, p1+p2), dtype=np.int64)
                J[:p1, p1:] = C
                J[p1:, :p1] = -C.T
                M = lambda shift: np.array([[h[u+v+shift] for v in range(a)] for u in range(a)], dtype=np.int64)
                K = np.zeros((3*a, 3*a), dtype=np.int64)
                K[:a, a:2*a] = M(q)
                K[:a, 2*a:] = -M(b)
                K[a:2*a, :a] = -M(q)
                K[a:2*a, 2*a:] = M(0)
                K[2*a:, :a] = M(b)
                K[2*a:, a:2*a] = -M(0)
                # Integer equality, not a floating-point or modular equality.
                assert np.array_equal(E @ J @ E.T, K), (m, n, name)
                cr, kr = rank_mod(C, p), rank_mod(K, p)
                assert kr == 2*cr, (m, n, name, cr, kr)
                count += 1
                records.append({"m": m, "n": n, "pattern": name,
                                "middle_rank_mod_p": cr, "koszul_rank_mod_p": kr})
    return {"cases": count, "identity": "exact integer matrices",
            "rank_checks": f"exact arithmetic over F_{p}", "records": records}


def test_mixed_graph() -> dict:
    # Example 7.4: dual root at 0, simple roots 1 and 2, and seven CP terms.
    p = 101
    gen = int(sp.primitive_root(p))
    z = pow(gen, 20, p)
    roots = [pow(z, i, p) for i in range(5)]
    vectors = [[1, a, 0] for a in roots] + [[1, 1, 1], [1, 2, 4]]
    weights = [pow(5, -1, p)*pow(a, -1, p) % p for a in roots] + [1, 1]
    N = 11

    def multiply(a, b):
        out = (a*b) % p
        out[1] = (a[0]*b[1]+a[1]*b[0]) % p
        return out

    A_images = [[1, 0, 1, 1], [0, 1, 1, 2], [0, 0, 1, 4]]
    U = np.array([A_images[i] + [v[i] for v in vectors] for i in range(3)], dtype=np.int64)
    W = row_basis(U, p)
    growth = [len(W)]
    for k in range(2, 6):
        W = row_basis(np.array([multiply(a, b) for a in W for b in U]), p)
        growth.append(len(W))
        if k == 4:
            assert rank_mod(W[:, :4], p) == 4
    lam = np.array([0, 1, 1, 1] + [-w for w in weights], dtype=np.int64) % p
    assert np.all((W @ lam) % p == 0)
    assert rank_mod(W[:, 4:], p) == 7
    assert len(W) == 8

    orthogonal = nullspace_mod(W, p).T
    standard = np.eye(N, dtype=np.int64)
    equations = []
    for w in W:
        M_w = np.column_stack([multiply(e, w) for e in standard])
        equations.append((orthogonal @ M_w) % p)
    stabilizer = nullspace_mod(np.vstack(equations), p)
    assert stabilizer.shape[1] == 3
    ids = [np.array([1, 0, 0, 0]+[1]*5+[0, 0], dtype=np.int64),
           np.array([0, 0, 1, 0]+[0]*5+[1, 0], dtype=np.int64),
           np.array([0, 0, 0, 1]+[0]*5+[0, 1], dtype=np.int64)]
    dimensions = []
    for e in ids:
        assert np.array_equal(multiply(e, e), e)
        block = np.array([multiply(e, w) for w in W])
        assert rank_mod(np.vstack([W, block]), p) == len(W)
        dimensions.append(rank_mod(block, p))
    assert dimensions == [6, 1, 1]
    return {"prime": p, "algebra_dimension": N, "product_dimensions": growth,
            "all_but_one_projection_rank": 4, "cp_projection_rank": 7,
            "stabilizer_dimension": 3, "block_product_dimensions": dimensions,
            "apolar_block_lengths": [2, 1, 1], "cp_block_lengths": [5, 1, 1]}


def main():
    if not __debug__:
        raise RuntimeError("Run verification without the Python -O optimization flag.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--suite", choices=["all", "ranks", "identities"], default="all")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    start = time.perf_counter()
    out = {"status": "PASS", "scope": "Computational checks, not formal proof verification",
           "python_version": platform.python_version(), "sympy_version": sp.__version__,
           "numpy_version": np.__version__, "suite": args.suite}
    if args.suite in ("all", "ranks"):
        out["rank_algorithm"] = test_rank_algorithm()
        print("PASS exact rank/apolar regression cases", out["rank_algorithm"]["cases"], flush=True)
    if args.suite in ("all", "identities"):
        out["fourier_indices"] = test_fourier_indices()
        print("PASS Fourier index checks", out["fourier_indices"]["cases"], flush=True)
        out["symmetric_reconstructions"] = test_decompositions()
        print("PASS full tensor reconstruction entries", out["symmetric_reconstructions"]["entries_checked"], flush=True)
        out["koszul_identity"] = test_koszul()
        print("PASS Koszul identities", out["koszul_identity"]["cases"], flush=True)
        out["mixed_graph_algebra"] = test_mixed_graph()
        print("PASS mixed-root graph algebra and support partition", flush=True)
    out["elapsed_seconds"] = round(time.perf_counter()-start, 3)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(out, indent=2)+"\n")
    print(json.dumps({k: v for k, v in out.items() if not isinstance(v, dict)}, indent=2))


if __name__ == "__main__":
    main()
