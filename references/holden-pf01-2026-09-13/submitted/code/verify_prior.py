"""Reproducible exact algebra checks and numerical checks for the paper.

These checks supplement, but do not formally verify, the all-n proofs.
No optimization or failed factor search is used as a lower-bound certificate.
"""
from __future__ import annotations
from itertools import combinations
from math import comb, lcm
from pathlib import Path
import json
import platform
import sys
import time
import numpy as np
import sympy as sp
from pf01 import FactorFactory, distance_matrix, packing, proved_bounds, prior_upper

ROOT = Path(__file__).resolve().parents[1]
LOG: dict = {"scope": "Exact algebra/finite tests plus floating-point construction tests; not formal verification",
             "python": sys.version.split()[0], "numpy": np.__version__, "sympy": sp.__version__,
             "platform": platform.platform()}


def record(name: str, result):
    LOG[name] = result
    print(name + ": " + json.dumps(result), flush=True)


def symbolic_graph():
    R, t, u, g = sp.symbols("R t u g", real=True)
    tr = ((R-u)*(R+t)+(R-t)*(R+u))/2-g
    assert sp.expand(tr-(R**2-t*u-g)) == 0
    dimensions = [(1, 1), (1, 2), (2, 2), (2, 3), (3, 3)]
    for a, b in dimensions:
        Z = sp.Matrix(a, b, sp.symbols(f"z0:{a*b}"))
        W = sp.Matrix(a, b, sp.symbols(f"w0:{a*b}"))
        F = Z.col_join(sp.eye(b))
        G = sp.eye(a).col_join(-W.T)
        product = sp.trace((F*F.T)*(G*G.T))
        assert sp.expand(product-sum(x*x for x in Z-W)) == 0
    return {"stereographic_trace_identity": "PASS", "graph_sizes": dimensions}


def exact_gram(n: int):
    r = n // 2
    subsets = list(combinations(range(n), r))
    X = np.zeros((len(subsets), n), dtype=np.int64)
    for row, I in enumerate(subsets):
        X[row, list(I)] = 1
    den = lcm(n, 2, *[j*(j+1) for j in range(2, n)])
    # Every entry below is an integer; no radicals or floating-point arithmetic.
    G = np.full((len(X), len(X)), (r*(n-r)*den)//n, dtype=np.int64)
    delta = X[:, 0]-X[:, 1]
    G -= np.outer(delta, delta)*(den//2)
    for j in range(2, n):
        numer = X[:, :j].sum(axis=1)-j*X[:, j]
        G -= np.outer(numer, numer)*(den//(j*(j+1)))
    assert np.array_equal(G, den*(r-X@X.T))
    # Upper bound on all intermediate absolute values, proving int64 safety.
    bound = den * (r*(n-r)//n + 2 + sum(4*r*r for _ in range(n-2)))
    assert bound < 2**63
    return {"n": n, "pairs": len(X)**2, "common_denominator": den, "status": "PASS"}


def numerical_factors(n: int):
    F = FactorFactory(n)
    subsets, A, B = F.enumerate()
    target = distance_matrix(subsets, n)
    product = np.einsum("iab,jab->ij", A, B, optimize=True)
    error = float(np.max(np.abs(product-target)))
    eig_a = float(np.linalg.eigvalsh(A).min())
    eig_b = float(np.linalg.eigvalsh(B).min())
    assert error < 2e-10
    assert eig_a > -2e-10 and eig_b > -2e-10
    assert np.all(np.linalg.matrix_rank(A, tol=1e-9) == F.b)
    assert np.all(np.linalg.matrix_rank(B, tol=1e-9) == F.a)
    return {"n": n, "N": len(subsets), "size": F.size, "pairs": len(subsets)**2,
            "max_abs_trace_error": error, "min_eigenvalue_A": eig_a,
            "min_eigenvalue_B": eig_b, "row_factor_rank": F.b, "column_factor_rank": F.a}


def modular_rank(matrix, prime=1000003):
    """Rank over F_p, with exact integer modular arithmetic (p^2 < 2^63)."""
    A = np.array(matrix, dtype=np.int64) % prime
    row, pivots = 0, []
    for col in range(A.shape[1]):
        options = np.flatnonzero(A[row:, col])
        if not len(options):
            continue
        pivot = row + int(options[0])
        A[[row, pivot]] = A[[pivot, row]]
        A[row, col:] = (A[row, col:]*pow(int(A[row, col]), -1, prime)) % prime
        for start in range(row+1, A.shape[0], 128):
            stop = min(start+128, A.shape[0])
            A[start:stop, col:] = (A[start:stop, col:]
                    - A[start:stop, col, None]*A[None, row, col:]) % prime
        pivots.append(col)
        row += 1
        if row == A.shape[0]:
            break
    return row, pivots


def quadratic_slice(n: int, r: int):
    pairs = list(combinations(range(n), 2))
    subsets = list(combinations(range(n), r))
    E = []
    for I in subsets:
        I = set(I)
        E.append([int(i in I) for i in range(n)] +
                 [int(i in I and j in I) for i, j in pairs])
    E = np.asarray(E, dtype=np.int64)
    K = np.zeros((n+len(pairs), n), dtype=np.int64)
    K[:n] = (r-1)*np.eye(n, dtype=np.int64)
    for row, (i, j) in enumerate(pairs, start=n):
        K[row, i] = K[row, j] = -1
    assert np.all(E@K == 0)
    rank, pivots = modular_rank(E)
    assert rank == len(pairs)
    # K has n independent columns, and the modular rank certifies a matching
    # rational lower bound. Hence the exact rational nullity is n.
    return {"n": n, "r": r, "rows": len(E), "columns": len(E[0]),
            "exact_rational_nullity": n, "prime": 1000003,
            "modular_pivots": pivots, "status": "PASS"}


def symmetric_basis(k: int):
    E = []
    D = []
    for i in range(k):
        M = sp.zeros(k)
        M[i, i] = 1
        E.append(M); D.append(M)
    for i, j in combinations(range(k), 2):
        M = sp.zeros(k)
        M[i, j] = M[j, i] = 1
        E.append(M); D.append(M/2)
    return E, D


def dual_basis(k: int):
    E, D = symmetric_basis(k)
    n = len(E)
    P = sp.eye(n)
    for i in range(n-1):
        P[i, i+1] = (i % 3)-1
    PinvT = P.inv().T
    X = [sum((P[j, i]*E[j] for j in range(n)), sp.zeros(k)) for i in range(n)]
    Y = [sum((PinvT[j, i]*D[j] for j in range(n)), sp.zeros(k)) for i in range(n)]
    assert all(sp.trace(X[i]*Y[j]) == int(i == j) for i in range(n) for j in range(n))
    assert sum((X[i]*Y[i] for i in range(n)), sp.zeros(k)) == sp.Rational(k+1, 2)*sp.eye(k)
    return {"k": k, "basis_dimension": n, "nonorthonormal_dual_basis_identity": "PASS"}


def conditional_coefficients():
    n, r = sp.symbols("n r", integer=True)
    p = (r-1)/(n-1)
    q = (r-1)*(r-2)/((n-1)*(n-2))
    scale = (n-r)/((n-1)*(n-2))
    expressions = [1-2*p+q, -1+3*p-2*q, -(p-q)]
    targets = [scale*(n-r-1), -scale*(n-2*r), -scale*(r-1)]
    assert all(sp.factor(a-b) == 0 for a, b in zip(expressions, targets))
    V, W = sp.symbols("V W", commutative=False)
    E = (r-1)*(V*W+W*V)+V**2+W**2-V-W
    U = V**2*W-W*V**2
    Z = V*W**2-W**2*V
    C = V*W-W*V
    assert sp.expand(V*E-E*V-((r-1)*U+Z-C)) == 0
    assert sp.expand(E*W-W*E-(U+(r-1)*Z-C)) == 0
    assert sp.expand(((r-1)*U+Z-C)-(U+(r-1)*Z-C)-(r-2)*(U-Z)) == 0
    return {"conditional_averaging_coefficients": "PASS", "free_algebra_commutators": "PASS"}


def commuting_maps(k: int):
    E_sym, _ = symmetric_basis(k)
    E = np.asarray([np.array(X).astype(np.int64) for X in E_sym])
    n = len(E)
    parameters = [(a, b) for a in range(n) for b in range(a, n)]
    # Self-adjoint maps parameterized as sum C_ab |E_a><E_b|, C symmetric.
    matrices = []
    points = list(E) + [E[i]+E[j] for i, j in combinations(range(n), 2)]
    upper = list(combinations(range(k), 2))
    for X in points:
        inner = np.einsum("iab,ab->i", E, X)
        block = np.zeros((len(upper), len(parameters)), dtype=np.int64)
        for col, (a, b) in enumerate(parameters):
            image = inner[a]*E[b]
            if a != b:
                image = image+inner[b]*E[a]
            C = X@image-image@X
            block[:, col] = [C[i, j] for i, j in upper]
        matrices.append(block)
    matrix = np.vstack(matrices)
    rank, _ = modular_rank(matrix)
    assert rank == len(parameters)-2
    # Identity and trace maps give two exact independent kernel vectors.
    ident, trace = [], []
    norms = [int((X*X).sum()) for X in E]
    traces = [int(np.trace(X)) for X in E]
    for a, b in parameters:
        ident.append(2//norms[a] if a == b else 0)  # twice identity
        trace.append(traces[a]*traces[b])
    assert np.all(matrix@np.asarray(ident) == 0)
    assert np.all(matrix@np.asarray(trace) == 0)
    assert modular_rank(np.asarray([ident, trace]))[0] == 2
    return {"k": k, "parameters": len(parameters), "constraints": len(matrix),
            "exact_rational_solution_dimension": 2, "status": "PASS"}


def sampled_large_orders():
    rng = np.random.default_rng(20260913)
    result = []
    for n in [12, 15, 21, 27, 28, 36, 51, 66, 101]:
        factory = FactorFactory(n)
        error = 0.0
        for _ in range(80):
            I = tuple(sorted(rng.choice(n, n//2, replace=False).tolist()))
            K = tuple(sorted(rng.choice(n, n//2, replace=False).tolist()))
            A = factory.factors(I).A
            B = factory.factors(K).B
            exact = n//2-len(set(I).intersection(K))
            error = max(error, abs(float(np.trace(A@B))-exact))
        assert error < 1e-9
        result.append({"n": n, "size": factory.size, "sampled_pairs": 80,
                       "max_abs_trace_error": error})
    return result


def main():
    if not __debug__:
        raise RuntimeError("Run without -O: verification assertions must be enabled")
    assert sp.isprime(1000003)
    (ROOT / "verification").mkdir(exist_ok=True)
    started = time.monotonic()
    record("symbolic_graph", symbolic_graph())
    record("exact_gram_tests", [exact_gram(n) for n in range(3, 12)])
    record("numerical_full_factorizations", [numerical_factors(n) for n in range(3, 12)])
    record("dual_basis_tests", [dual_basis(k) for k in [3, 4, 5]])
    record("conditional_and_commutator_algebra", conditional_coefficients())
    record("quadratic_slice_kernels", [quadratic_slice(n, n//2) for n in range(4, 13)])
    record("commuting_map_tests", [commuting_maps(k) for k in [3, 4, 5]])
    record("large_order_samples", sampled_large_orders())
    bounds = [{"n": n, "lower": proved_bounds(n)[0], "upper": proved_bounds(n)[1],
               "previous_upper": prior_upper(n)} for n in range(5, 102)]
    (ROOT/"verification"/"bounds.json").write_text(json.dumps(bounds, indent=2)+"\n")
    record("elapsed_seconds", round(time.monotonic()-started, 3))
    record("overall", "PASS")
    (ROOT/"verification"/"checks.json").write_text(json.dumps(LOG, indent=2)+"\n")


if __name__ == "__main__":
    main()
