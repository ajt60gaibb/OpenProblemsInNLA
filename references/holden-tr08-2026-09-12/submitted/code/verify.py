#!/usr/bin/env python3
"""Finite checks for the TR-08 proof. These tests are not an asymptotic proof.

Run from the archive root:
    python code/verify.py --output verification/checks.json
Requires Python 3.10+, NumPy, SciPy, and SymPy.
"""
from __future__ import annotations
import argparse
import itertools
import json
import math
import platform
from fractions import Fraction
from pathlib import Path
from typing import Any

import numpy as np
import scipy
import sympy as sp


def nb_matrix(a: np.ndarray, present_only: bool = False) -> np.ndarray:
    """Nonbacktracking operator, with weight on the next oriented edge.

    The complete-bipartite version has extra zero eigenvalues, and is the
    fixed-size operator used in the moment comparison in the manuscript.
    """
    nr, nc = a.shape
    pairs = [(i, j) for i in range(nr) for j in range(nc)
             if not present_only or a[i, j] != 0]
    edges = [(i, nr+j) for i, j in pairs] + [(nr+j, i) for i, j in pairs]
    out: dict[int, list[tuple[int, int, float]]] = {}
    for f, (v, w) in enumerate(edges):
        weight = float(a[v, w-nr] if v < nr else a[w, v-nr])
        out.setdefault(v, []).append((f, w, weight))
    b = np.zeros((len(edges), len(edges)), dtype=float)
    for e, (u, v) in enumerate(edges):
        for f, w, weight in out.get(v, []):
            if w != u:
                b[e, f] = weight
    return b


def tree_matrix(d: int, width: int, rng: np.random.Generator) -> tuple[np.ndarray, np.ndarray]:
    """All column supports of the cancellation tree are included."""
    if d < 1 or width < 1:
        raise ValueError("d and width must be positive")
    nr = d + d*width*(d-1)
    nc = 1 + d*width
    a = np.zeros((nr, nc))
    a[:d, 0] = rng.choice([-1., 1.], d)/math.sqrt(d)
    v = np.zeros(nc)
    v[0] = 1.
    row = d
    for i in range(d):
        for q in range(width):
            j = 1+i*width+q
            a[i, j] = rng.choice([-1., 1.])/math.sqrt(d)
            v[j] = -a[i, 0]/(width*a[i, j])
            if d > 1:
                a[row:row+d-1, j] = rng.choice([-1., 1.], d-1)/math.sqrt(d)
                row += d-1
    return a, v


def symbolic_checks() -> dict[str, Any]:
    d, w = sp.symbols("d w", positive=True)
    quotient = ((d-1)/w)/(1+d/w)
    assert sp.simplify(quotient-(d-1)/(d+w)) == 0
    t, u, gamma, beta = sp.symbols("t u gamma beta", positive=True)
    schur_bound = (1-gamma/(t+u))*(t+u)/t*(beta-t-u)
    target = (t+u-gamma)/t*(beta-t-u)
    assert sp.simplify(schur_bound-target) == 0
    j0 = (sp.Rational(1, 32)*sp.log(sp.Rational(25, 8))
          -sp.Rational(1, 32)+sp.Rational(1, 100))
    assert float(j0) > 0
    conservative_bulk = sp.Rational(3, 4)*sp.Rational(7, 64)
    assert conservative_bulk > sp.Rational(1, 16)
    return {"tree_Rayleigh_quotient_squared": str(sp.factor(quotient)),
            "bulk_bound_identity": str(sp.factor(target)),
            "J_1_over_32": float(j0),
            "eta": float(j0/8),
            "conservative_bulk_eigenvalue_bound": str(conservative_bulk)}


def occupancy_checks() -> dict[str, Any]:
    # Exhaustive exact inclusion probabilities and mgf inequalities.
    tested = 0
    for n in range(2, 10):
        for d in range(1, n+1):
            supports = list(itertools.combinations(range(n), d))
            for size in range(n+1):
                z = Fraction(3, 2)
                moment = sum((z**len(set(s).intersection(range(size))) for s in supports), Fraction())/len(supports)
                product_bound = (1+Fraction(d, n)*(z-1))**size
                assert moment <= product_bound
                tested += 1
    # Pairwise negative correlation of row upper-tail indicators.
    n, d, reservoir = 4, 2, 3
    supports = list(itertools.combinations(range(n), d))
    configurations = list(itertools.product(supports, repeat=reservoir))
    covariances = []
    for threshold in range(1, reservoir+1):
        ai = aj = both = 0
        for ss in configurations:
            di = sum(0 in s for s in ss)
            dj = sum(1 in s for s in ss)
            ii, jj = di >= threshold, dj >= threshold
            ai += ii
            aj += jj
            both += ii and jj
        total = len(configurations)
        cov = Fraction(both, total)-Fraction(ai*aj, total*total)
        assert cov <= 0
        covariances.append(str(cov))
    return {"exact_hypergeometric_mgf_cases": tested,
            "row_tail_covariances": covariances}


def trace_powers_integer(a: np.ndarray, max_power: int) -> list[int]:
    """Integer squared Frobenius norms for an unnormalized sign matrix.

    Only used at dimensions 3 x 2 and powers <= 5, far below int64 overflow.
    Rescale by d**ell only after the integer sum is formed.
    """
    b = nb_matrix(a).astype(np.int64)
    power = np.eye(b.shape[0], dtype=np.int64)
    result: list[int] = []
    for _ in range(max_power):
        power = power @ b
        result.append(int(np.sum(power*power)))
    return result


def moment_domination() -> dict[str, Any]:
    # N=3, m=2, d=2: enumerate all fixed-support signed matrices and all
    # iid ternary matrices. At p=d/n=2/3, each iid entry is uniform on
    # {-1,0,1}; every expectation below is an exact rational number.
    n, m, d, max_power = 3, 2, 2, 5
    supports = list(itertools.combinations(range(n), d))
    full = [0]*max_power
    pruned = [0]*max_power
    count = 0
    for ss in itertools.product(supports, repeat=m):
        for signs in itertools.product([-1, 1], repeat=d*m):
            a = np.zeros((n, m), dtype=np.int64)
            for j in range(m):
                a[list(ss[j]), j] = signs[j*d:(j+1)*d]
            full = [x+y for x, y in zip(full, trace_powers_integer(a, max_power))]
            aa = a.copy()
            # A deliberately support-dependent, sign-independent pruning.
            if np.count_nonzero(aa[0]) == 1:
                aa[0] = 0
            pruned = [x+y for x, y in zip(pruned, trace_powers_integer(aa, max_power))]
            count += 1
    iid = [0]*max_power
    for values in itertools.product([-1, 0, 1], repeat=n*m):
        a = np.asarray(values, dtype=np.int64).reshape(n, m)
        iid = [x+y for x, y in zip(iid, trace_powers_integer(a, max_power))]
    fixed_exact = [Fraction(x, count*d**ell) for ell, x in enumerate(full, 1)]
    pruned_exact = [Fraction(x, count*d**ell) for ell, x in enumerate(pruned, 1)]
    iid_exact = [Fraction(x, 3**(n*m)*d**ell) for ell, x in enumerate(iid, 1)]
    assert all(x <= y for x, y in zip(fixed_exact, iid_exact))
    assert all(x <= y for x, y in zip(pruned_exact, iid_exact))
    return {"fixed_column_matrices_enumerated": count,
            "iid_matrices_enumerated": 3**(n*m),
            "powers": list(range(1, max_power+1)),
            "arithmetic": "Exact integer path sums, normalized as rational numbers",
            "fixed_column_expected_squared_Frobenius": [str(x) for x in fixed_exact],
            "pruned_expected_squared_Frobenius": [str(x) for x in pruned_exact],
            "iid_expected_squared_Frobenius": [str(x) for x in iid_exact]}


def spectral_checks(rng: np.random.Generator) -> dict[str, Any]:
    # Exact tree quotient, checked under many independently chosen signs.
    maximum_tree_error = 0.
    tree_cases = 0
    for d in [1, 2, 3, 5, 8]:
        for width in [1, 2, 7, 20]:
            for _ in range(3):
                a, v = tree_matrix(d, width, rng)
                observed = float(np.linalg.norm(a@v)**2/np.linalg.norm(v)**2)
                expected = (d-1)/(d+width)
                maximum_tree_error = max(maximum_tree_error, abs(observed-expected))
                assert abs(observed-expected) < 1e-12
                assert np.max(np.abs(a[:d]@v)) < 1e-12
                tree_cases += 1

    # The deterministic nonbacktracking lower bound, on a finite matrix
    # satisfying its hypotheses. No random-matrix asymptotic is inferred.
    d = 64
    a = rng.choice([-1., 1.], size=(d, 2))/math.sqrt(d)
    b = nb_matrix(a, present_only=True)
    rho = float(np.max(np.abs(np.linalg.eigvals(b))))
    assert rho < .5
    col_min = float(np.min(np.sum(a*a, axis=0)))
    row_max = float(np.max(np.sum(a*a, axis=1)))
    t, u = .25, 1/d
    lower = (t+u-row_max)/t*(col_min-t-u)
    actual = float(np.linalg.svd(a, compute_uv=False)[-1]**2)
    assert actual+1e-10 >= lower

    # Ihara-Bass determinant identity, independently checked on a small graph.
    aa = np.zeros((5, 3))
    for j in range(3):
        ss = rng.choice(5, 2, replace=False)
        aa[ss, j] = rng.choice([-1., 1.], 2)/math.sqrt(2)
    bb = nb_matrix(aa, present_only=True)
    h = np.block([[np.zeros((5, 5)), aa], [aa.T, np.zeros((3, 3))]])
    deg = np.diag(np.sum(h*h, axis=1))
    z = .2+.3j
    edges = int(np.count_nonzero(aa))
    vertices = h.shape[0]
    lhs = np.linalg.det(np.eye(bb.shape[0])-z*bb)
    rhs = ((1-z*z/2)**(edges-vertices)
           *np.linalg.det(np.eye(vertices)-z*h+z*z*(deg-.5*np.eye(vertices))))
    determinant_error = float(abs(lhs-rhs))
    assert determinant_error < 1e-10

    # Block-triangular gluing, including large couplings.
    block_cases = 0
    smallest_margin = math.inf
    for coupling in [0., .1, 1., 10., 100.]:
        for _ in range(12):
            q, _ = np.linalg.qr(rng.normal(size=(9, 4)), mode="reduced")
            v, _ = np.linalg.qr(rng.normal(size=(7, 3)), mode="reduced")
            zz = rng.normal(size=(7, 4))
            zz *= coupling/max(np.linalg.norm(zz, 2), 1e-100)
            block = np.block([[.25*q, np.zeros((9, 3))], [zz, .5*v]])
            actual_smin = float(np.linalg.svd(block, compute_uv=False)[-1])
            bound = 1/(6+8*coupling)
            assert actual_smin+1e-12 >= bound
            smallest_margin = min(smallest_margin, actual_smin-bound)
            block_cases += 1
    return {"tree_cases": tree_cases,
            "maximum_tree_Rayleigh_error": maximum_tree_error,
            "bulk_example_nonbacktracking_radius": rho,
            "bulk_example_lower_bound_squared": lower,
            "bulk_example_actual_smin_squared": actual,
            "Ihara_Bass_determinant_error": determinant_error,
            "block_cases": block_cases,
            "minimum_block_bound_margin": smallest_margin}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("checks.json"))
    parser.add_argument("--seed", type=int, default=20260912)
    args = parser.parse_args()
    rng = np.random.default_rng(args.seed)
    results: dict[str, Any] = {
        "status": "PASS",
        "scope": "Finite algebraic and numerical checks only; not formal or asymptotic verification.",
        "seed": args.seed,
        "versions": {"python": platform.python_version(), "numpy": np.__version__,
                     "scipy": scipy.__version__, "sympy": sp.__version__},
        "symbolic": symbolic_checks(),
        "occupancy": occupancy_checks(),
        "moment_comparison": moment_domination(),
        "spectral": spectral_checks(rng),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
