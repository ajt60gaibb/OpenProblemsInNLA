#!/usr/bin/env python3
"""Finite-dimensional experiments for TR-08, not a test of an asymptotic theorem.

The exact fixed-column-support model is sampled, rather than an iid Bernoulli
approximation. Smallest singular values are floating-point estimates. Rare
cancellation witnesses can be invisible at all computationally practical sizes.

Example (run from the archive root):
    python code/experiment.py --sizes 2000 10000 50000 \
        --sparsities 1 2 4 8 16 --repetitions 3 \
        --output verification/experiments.csv
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import platform
from pathlib import Path
from typing import Any

import numpy as np
import scipy
from scipy import linalg, sparse
from scipy.sparse.linalg import ArpackNoConvergence, eigsh


def sample_matrix(k: int, d: int, rng: np.random.Generator,
                  max_nnz: int = 20_000_000) -> sparse.csc_matrix:
    """Return a k by k/100 matrix with independent uniform d-subset columns."""
    if k < 100 or k % 100:
        raise ValueError("k must be a positive multiple of 100")
    if not 1 <= d <= k:
        raise ValueError("sparsity must lie between 1 and k")
    m = k // 100
    if m*d > max_nnz:
        raise ValueError(f"requested {m*d:,} nonzeros exceed --max-nnz={max_nnz:,}")
    rows = np.empty(m*d, dtype=np.int64)
    values = np.empty(m*d, dtype=np.float64)
    for j in range(m):
        loc = slice(j*d, (j+1)*d)
        rows[loc] = rng.choice(k, size=d, replace=False)
        values[loc] = (2*rng.integers(0, 2, size=d)-1)/math.sqrt(d)
    pointers = np.arange(m+1, dtype=np.int64)*d
    a = sparse.csc_matrix((values, rows, pointers), shape=(k, m))
    a.sort_indices()
    if a.nnz != m*d or not np.all(np.diff(a.indptr) == d):
        raise RuntimeError("unexpected support-generation error")
    squared_column_norms = np.asarray(a.power(2).sum(axis=0)).ravel()
    if not np.allclose(squared_column_norms, 1., rtol=2e-13, atol=2e-13):
        raise RuntimeError("unexpected column-normalization error")
    return a


def estimate_smin(a: sparse.csc_matrix, rng: np.random.Generator,
                  dense_limit: int) -> tuple[float, float, float, str]:
    """Estimate sigma_min via the Gram matrix; report eigenpair residual.

    This is numerical evidence, not an interval-arithmetic certificate. For an
    iterative solve, failure to converge is an error, never a reported result.
    """
    gram = (a.T @ a).tocsc()
    m = gram.shape[0]
    if m <= dense_limit or m == 1:
        eigenvalues, eigenvectors = linalg.eigh(
            gram.toarray(), subset_by_index=[0, 0], check_finite=True,
            driver="evr")
        method = "dense_Gram_eigh"
    else:
        try:
            eigenvalues, eigenvectors = eigsh(
                gram, k=1, which="SA", tol=1e-11,
                maxiter=max(10000, 10*m), v0=rng.normal(size=m))
        except ArpackNoConvergence as exc:
            raise RuntimeError("smallest-eigenvalue iteration did not converge") from exc
        method = "sparse_Gram_eigsh"
    eigenvalue = float(eigenvalues[0])
    v = eigenvectors[:, 0]
    residual = float(np.linalg.norm(gram @ v-eigenvalue*v))
    scale = max(1., float(np.asarray(abs(gram).sum(axis=1)).max()))
    if not math.isfinite(eigenvalue) or residual > 1e-8*scale:
        raise RuntimeError(f"unreliable eigenpair: eigenvalue={eigenvalue}, residual={residual}")
    if eigenvalue < -1e-9*scale:
        raise RuntimeError(f"Gram matrix yielded a materially negative eigenvalue: {eigenvalue}")
    # Clip only roundoff-scale negative values. Record the unmodified value too.
    return math.sqrt(max(0., eigenvalue)), eigenvalue, residual, method


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--sizes", type=int, nargs="+", default=[2000, 10000, 50000])
    parser.add_argument("--sparsities", type=int, nargs="+", default=[1, 2, 4, 8, 16])
    parser.add_argument("--repetitions", type=int, default=3)
    parser.add_argument("--seed", type=int, default=20260912)
    parser.add_argument("--output", type=Path, default=Path("experiments.csv"))
    parser.add_argument("--dense-limit", type=int, default=1500)
    parser.add_argument("--max-nnz", type=int, default=20_000_000)
    args = parser.parse_args()
    if args.repetitions < 1 or args.seed < 0 or args.dense_limit < 1 or args.max_nnz < 1:
        parser.error("repetitions, dense-limit, and max-nnz must be positive; seed must be nonnegative")
    if any(k < 100 or k % 100 for k in args.sizes):
        parser.error("every size must be a positive multiple of 100")
    if any(d < 1 or d > min(args.sizes) for d in args.sparsities):
        parser.error("sparsities must be between 1 and the smallest requested matrix size")
    records: list[dict[str, Any]] = []
    for k in sorted(set(args.sizes)):
        for d in sorted(set(args.sparsities)):
            group: list[float] = []
            for repetition in range(args.repetitions):
                rng = np.random.default_rng(np.random.SeedSequence([args.seed, k, d, repetition]))
                a = sample_matrix(k, d, rng, args.max_nnz)
                smin, eigenvalue, residual, method = estimate_smin(a, rng, args.dense_limit)
                max_degree = int(np.bincount(a.indices, minlength=k).max())
                records.append({
                    "k": k, "m": k//100, "sparsity": d,
                    "repetition": repetition, "master_seed": args.seed,
                    "d_squared_over_log_k": d*d/math.log(k),
                    "sigma_min_estimate": smin,
                    "smallest_Gram_eigenvalue_raw": eigenvalue,
                    "eigenpair_residual": residual,
                    "max_row_occupancy": max_degree, "method": method,
                })
                group.append(smin)
            print(f"k={k:6d} d={d:3d} min={min(group):.8f} median={np.median(group):.8f}")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(records[0]))
        writer.writeheader()
        writer.writerows(records)
    metadata = {
        "scope": "Finite experiments only; no inference of an asymptotic threshold",
        "sampling": "Independent uniform fixed-size supports; independent Rademacher signs",
        "numerics": "Gram eigenvalues in floating point, with recorded eigenpair residuals",
        "rows_recorded": len(records),
        "sizes": sorted(set(args.sizes)), "sparsities": sorted(set(args.sparsities)),
        "repetitions": args.repetitions, "seed": args.seed,
        "dense_limit": args.dense_limit,
        "versions": {"python": platform.python_version(), "numpy": np.__version__,
                     "scipy": scipy.__version__},
    }
    args.output.with_suffix(".metadata.json").write_text(
        json.dumps(metadata, indent=2)+"\n", encoding="utf-8")
    print(f"Wrote {len(records)} finite experiments to {args.output}")


if __name__ == "__main__":
    main()
