#!/usr/bin/env python3
"""Reproduce exact rational checks.  Run from any working directory.

No finite collection of tests proves a universal complexity theorem.  The
mathematical proofs are in report/report.pdf.  This program checks identities,
edge cases, and examples with rational arithmetic, with no rounding tolerance.
"""
from __future__ import annotations

import argparse
import csv
from fractions import Fraction as Q
import json
from pathlib import Path
import random
import sys
import time

import sympy as sp

from exact_arithmetic import (SparseMatrix, cgls_exact, dot,
                              psd_principal_basis, recover_flat_shift)

SEED = 20260912


def rat(x) -> Q:
    x = sp.Rational(x)
    return Q(int(x.p), int(x.q))


def sparse(m) -> SparseMatrix:
    return SparseMatrix.from_coo(m.rows, m.cols,
        ((i, j, rat(m[i, j])) for i in range(m.rows)
         for j in range(m.cols) if m[i, j]))


def orthogonal(n: int, rng: random.Random, layers: int = 2):
    q = sp.eye(n)
    for _ in range(layers):
        order = list(range(n))
        rng.shuffle(order)
        for u in range(0, n - 1, 2):
            i, j = order[u:u + 2]
            c, s = sp.Rational(3, 5), sp.Rational(4, 5)
            if rng.randrange(2):
                s = -s
            ri, rj = q[i, :], q[j, :]
            q[i, :] = c * ri + s * rj
            q[j, :] = -s * ri + c * rj
    assert q.T * q == sp.eye(n)
    return q


def cgls_checks(rng):
    output = []
    for n in [4, 7, 10]:
        for k in sorted({0, 1, min(3, n - 1), n - 1}):
            for kap in [sp.Integer(1), sp.Rational(3, 2), sp.Integer(3)]:
                for repeat in range(2):
                    tail = [sp.Integer(1)] if n - k == 1 else [
                        1 + (kap - 1) * sp.Rational(i, n - k - 1)
                        for i in range(n - k)]
                    spikes = [kap + 2 + 2 * j for j in range(k)]
                    singulars = sorted(spikes + tail, reverse=True)
                    a = (orthogonal(n, rng) * sp.diag(*singulars)
                         * orthogonal(n, rng))
                    b = [Q(rng.randint(-3, 3)) for _ in range(n)]
                    if not any(b):
                        b[0] = Q(1)
                    sa = sparse(a)
                    result = cgls_exact(sa, b)
                    assert result.converged and result.iterations <= n
                    exact_res = [bb - aa for bb, aa in zip(b, sa.mv(result.x))]
                    assert dot(exact_res, exact_res) == 0
                    hist = result.residual_squared
                    assert all(y <= x for x, y in zip(hist, hist[1:]))
                    checks = 0
                    if kap == 1:
                        assert result.iterations <= k + 1
                    else:
                        rho = rat((kap - 1) / (kap + 1))
                        for t in range(k + 1, len(hist)):
                            mm = t - k
                            assert hist[t] <= 4 * rho ** (2 * mm) * hist[0]
                            checks += 1
                    output.append({
                        "n": n, "k": k, "kappa_promise": str(kap),
                        "repeat": repeat, "nnz": sa.nnz,
                        "iterations": result.iterations,
                        "matvec_calls": result.matvec_calls,
                        "chebyshev_inequalities_checked": checks,
                        "exact_residual_squared": "0"})
    return output


def pcg_dense_iterates(core, preconditioner, rhs):
    """Small exact dense PCG trace used only to check the error proof."""
    x = sp.zeros(core.rows, 1)
    residual = rhs.copy()
    output = [x.copy()]
    if residual == sp.zeros(core.rows, 1):
        return output
    pinv = preconditioner.inv()
    z = pinv * residual
    direction = z.copy()
    gamma = (residual.T * z)[0]
    assert gamma > 0
    for _ in range(core.rows):
        product = core * direction
        denominator = (direction.T * product)[0]
        assert denominator > 0
        step = gamma / denominator
        x += step * direction
        residual -= step * product
        output.append(x.copy())
        if residual == sp.zeros(core.rows, 1):
            return output
        z = pinv * residual
        new_gamma = (residual.T * z)[0]
        assert new_gamma > 0
        direction = z + (new_gamma / gamma) * direction
        gamma = new_gamma
    assert residual == sp.zeros(core.rows, 1)
    return output


def flat_checks(rng):
    records = []
    for n, rank in [(5, 1), (9, 2), (13, 3), (17, 4)]:
        for extra_k in [0, 1]:
            k = rank + extra_k
            alpha = sp.Rational(2 + rank, 3)
            bfactor = sp.zeros(n, rank)
            for j in range(rank):
                bfactor[j, j] = j + 2
            for i in range(rank, n):
                for j in range(rank):
                    if rng.randrange(3) == 0:
                        bfactor[i, j] = rng.choice([-2, -1, 1, 2])
            r = bfactor * bfactor.T
            m = alpha * sp.eye(n) + r
            shift, multiplicity = recover_flat_shift(m, k)
            assert shift == alpha
            width = min(n, 2 * k + 2)
            # Algebraic test sketches.  These small, fixed-width choices are
            # NOT claimed to instantiate the quantitative OSE theorem.
            for attempts in range(1, 33):
                omega = sp.zeros(n, width)
                for i in range(n):
                    for j in rng.sample(range(width), min(2, width)):
                        omega[i, j] = rng.choice([-1, 1])
                wfull = omega.T * r * omega
                indices = psd_principal_basis(wfull)
                if len(indices) == rank:
                    break
            else:
                raise AssertionError("Test sketches did not recover the rank")
            om = omega[:, indices]
            f = r * om
            w = om.T * r * om
            assert w.det() > 0
            assert f * w.inv() * f.T == r
            core = alpha * w + f.T * f
            rhs = sp.Matrix([rng.randint(-3, 3) for _ in range(n)])
            if rhs == sp.zeros(n, 1):
                rhs[0] = 1
            z = core.inv() * f.T * rhs
            x = (rhs - f * z) / alpha
            assert m * x == rhs
            # Verify an actual nontrivial perturbation of the Gram factor.
            weights = [sp.Rational([4, 5, 6][i % 3], 5) for i in range(n)]
            sf = sp.diag(*weights) * f
            pre = alpha * w + sf.T * sf
            # Each weight^2 belongs to [1/2,3/2]; congruence proves these
            # inequalities.  Exact LDL-style principal bases also check PSD.
            psd_principal_basis(pre - core / 2)
            psd_principal_basis(3 * core / 2 - pre)
            iterates = pcg_dense_iterates(core, pre, f.T * rhs)
            initial_energy = (z.T * core * z)[0]
            rhs_squared = (rhs.T * rhs)[0]
            assert initial_energy <= rhs_squared
            upper_norm = alpha + sp.trace(r)
            for iteration, zi in enumerate(iterates):
                error = zi - z
                energy = (error.T * core * error)[0]
                # Condition <= 3 implies rho < 1/2.  This is a deliberately
                # conservative, wholly rational CG contraction bound.
                assert energy <= 4 * sp.Rational(1, 4)**iteration * initial_energy
                xi = (rhs - f * zi) / alpha
                physical = m * xi - rhs
                assert (physical.T * physical)[0] <= (upper_norm / alpha)**2 * energy
            records.append({
                "n": n, "rank": rank, "k_upper_bound": k,
                "alpha": str(alpha), "recovered_alpha": str(shift),
                "remaining_gcd_multiplicity": multiplicity,
                "sketch_attempts": attempts, "selected_columns": indices,
                "nystrom_identity": True, "woodbury_identity": True,
                "gram_sandwich": True,
                "pcg_iterations": len(iterates) - 1,
                "pcg_iterates_checked": len(iterates),
                "physical_error_transfer": True})
    # k=0 and a principal block completely missing the outlier support.
    shift0, _ = recover_flat_shift(sp.Rational(7, 5) * sp.eye(3), 0)
    assert shift0 == sp.Rational(7, 5)
    m = sp.diag(*([sp.Integer(2)] * 7 + [sp.Integer(11)]))
    shift_missing, _ = recover_flat_shift(m, 1)
    assert shift_missing == 2
    # An overestimate k is valid even when there are no outliers at all.
    shift_zero_rank, _ = recover_flat_shift(sp.Rational(9, 7) * sp.eye(9), 3)
    assert shift_zero_rank == sp.Rational(9, 7)
    # The PSD rank-profile verifier must reject a range-incompatible cross block.
    try:
        psd_principal_basis(sp.Matrix([[1, 0, 0], [0, 0, 1], [0, 1, 100]]))
    except ValueError:
        pass
    else:
        raise AssertionError("Indefinite matrix was incorrectly accepted as PSD")
    return records


def gram_fill_checks():
    records = []
    for n in [3, 5, 9, 17, 33]:
        a = sp.eye(n)
        a[0, 0] = n
        for j in range(1, n):
            a[0, j] = 1
        h = a.T * a
        na = sum(bool(x) for x in a)
        nh = sum(bool(x) for x in h)
        assert na == 2 * n - 1 and nh == n * n
        t = sp.Symbol("t")
        expected = (t - 1) ** (n - 2) * (t*t - (n*n+n)*t + n*n)
        assert sp.expand(h.charpoly(t).as_expr() - expected) == 0
        records.append({"n": n, "nnz_A": na, "nnz_AtA": nh,
                        "lambda_min_lower_bound": str(sp.Rational(n, n + 1)),
                        "tail_kappa_squared_upper_bound": str(sp.Rational(n + 1, n))})
    return records


def nystrom_checks():
    records = []
    # u=e1, sketch direction (a,b) with rational a^2+b^2=1.
    for a, b in [(sp.Rational(3, 5), sp.Rational(4, 5)),
                 (sp.Rational(5, 13), sp.Rational(12, 13)),
                 (sp.Rational(7, 25), sp.Rational(24, 25))]:
        for ell in [sp.Integer(2), sp.Integer(10), sp.Integer(1000)]:
            h = sp.diag(ell, 1, 1)
            omega = sp.Matrix([a, b, 0])
            nh = h * omega * (omega.T * h * omega).inv() * omega.T * h
            residual = h - nh
            z = sp.Matrix([-b, a, 0])
            t = a * a
            lam = ell / (1 + (ell - 1)*t)
            assert residual == lam * z * z.T + sp.diag(0, 0, 1)
            records.append({"overlap_squared": str(t), "spike": str(ell),
                            "residual_norm": str(lam), "identity_exact": True})
    return records


def row_sketch_checks():
    records = []
    for rows, block_size in [(1, 7), (2, 5), (3, 4)]:
        n = rows * block_size
        sketch = sp.zeros(rows, n)
        for column in range(n):
            sketch[column // block_size, column] = (-1)**column
        assert sketch * sketch.T == block_size * sp.eye(rows)
        gram = sketch.T * sketch
        assert sp.trace(gram) == n and gram.rank() == rows
        assert gram * gram == block_size * gram
        records.append({"n": n, "sketch_rows": rows,
                        "largest_regularized_eigenvalue": block_size + 1,
                        "target_eigenvalue": 2,
                        "spectral_ratio": str(sp.Rational(block_size + 1, 2))})
    return records


def rank_discontinuity():
    n = 11
    delta = sp.Rational(1, 1000)
    m = sp.diag(*[1 + delta * sp.Rational(i, n - 1) for i in range(n)])
    rank = (m - sp.eye(n)).rank()
    assert rank == n - 1
    return {"n": n, "condition_number": str(1 + delta),
            "rank_of_M_minus_lambda_min_I": rank}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path,
                        default=Path(__file__).resolve().parents[1] / "results")
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    rng = random.Random(SEED)
    started = time.perf_counter()
    cg = cgls_checks(rng)
    flat = flat_checks(rng)
    fill = gram_fill_checks()
    ny = nystrom_checks()
    row_sketch = row_sketch_checks()
    discontinuity = rank_discontinuity()
    summary = {
        "status": "ALL_CHECKS_PASSED",
        "does_not_prove_full_KE01": True,
        "arithmetic": "exact rational; no floating-point tolerances",
        "seed": SEED, "python_version": sys.version.split()[0],
        "sympy_version": sp.__version__,
        "cgls_cases": len(cg),
        "chebyshev_inequalities_checked": sum(x["chebyshev_inequalities_checked"] for x in cg),
        "flat_tail_cases": len(flat), "gram_fill_cases": len(fill),
        "nystrom_cases": len(ny),
        "row_sketch_cases": len(row_sketch),
        "pcg_iterates_checked": sum(x["pcg_iterates_checked"] for x in flat),
        "verification_elapsed_seconds": round(time.perf_counter() - started, 3),
        "rank_discontinuity": discontinuity,
        "flat_tail": flat, "gram_fill": fill, "nystrom": ny,
        "row_sketch": row_sketch,
    }
    (args.out / "exact_checks.json").write_text(json.dumps(summary, indent=2) + "\n")
    with (args.out / "cgls_cases.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(cg[0]))
        writer.writeheader()
        writer.writerows(cg)
    print(json.dumps({k: v for k, v in summary.items()
                      if k not in ["flat_tail", "gram_fill", "nystrom", "row_sketch"]}, indent=2))


if __name__ == "__main__":
    main()
