#!/usr/bin/env python3
"""Exhaustive finite-length diagnostics for the MF-12 pair (not a proof).

Every binary word through --max-length is tested in the spectral norm. Chunking
keeps the working set small; runtime is exponential in the maximum length.
Binary digit 0 means A and digit 1 means P. The leftmost digit is the leftmost
matrix in the reported product. The output is checkpointed after each length.

Python 3.10+ and NumPy. Typical use:
    python enumerate_growth_words.py --alpha 0.5 --max-length 20 --output results.json
"""
from __future__ import annotations
import os
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("OMP_NUM_THREADS", "1")
import argparse
import datetime as dt
import json
import math
from pathlib import Path
import time
from typing import Any
import numpy as np
from numpy.typing import NDArray

Matrix = NDArray[np.float64]


def matrices(alpha: float, lam: float) -> tuple[Matrix, Matrix, float]:
    if not math.isfinite(alpha) or not 0.0 < alpha < 1.0:
        raise ValueError("alpha must lie strictly between zero and one")
    if not math.isfinite(lam) or not 0.0 < lam <= 0.25:
        raise ValueError("lambda must lie in (0, 1/4]")
    mu = lam ** (1.0 - alpha)
    if not lam < mu < 1.0:
        raise ValueError("parameters are not distinguishable at float64 precision")
    a = np.diag([1.0, lam, lam, mu, mu, 1.0])
    a[1, 2] = lam
    a[3, 4] = mu
    v = np.array([[1., 0.], [0., 0.], [1., 0.],
                  [0., 0.], [0., 1.], [0., 1.]])
    u = np.array([[1., -1., 0., 1., 0., 0.],
                  [0., 0., 0., 0., 0., 1.]])
    return a, v @ u, mu


def product_from_index(index: int, length: int, a: Matrix, p: Matrix) -> Matrix:
    if length < 0 or index < 0 or index >= (1 << length):
        raise ValueError("word index is out of range")
    answer = np.eye(a.shape[0])
    for shift in reversed(range(length)):
        answer = answer @ (p if ((index >> shift) & 1) else a)
    return answer


def enumerate_length(n: int, a: Matrix, p: Matrix, batch_bits: int) -> tuple[float, int]:
    """Return max norm and one maximizer; every one of the 2**n words is tested."""
    suffix_length = min(n, batch_bits)
    suffixes = np.eye(a.shape[0])[None, :, :]
    for _ in range(suffix_length):
        suffixes = np.concatenate((a @ suffixes, p @ suffixes), axis=0)
    prefix_length = n - suffix_length
    best, best_index = -math.inf, -1
    for prefix_index in range(1 << prefix_length):
        prefix = product_from_index(prefix_index, prefix_length, a, p)
        products = prefix @ suffixes
        norms = np.linalg.svd(products, compute_uv=False)[:, 0]
        local_index = int(np.argmax(norms))
        candidate = float(norms[local_index])
        if candidate > best:
            best = candidate
            best_index = (prefix_index << suffix_length) + local_index
    # Independently reconstruct the reported winning word, in the stated order.
    winning_norm = float(np.linalg.norm(product_from_index(best_index, n, a, p), 2))
    if not math.isclose(winning_norm, best, rel_tol=2e-12, abs_tol=1e-13):
        raise ArithmeticError("winning-word reconstruction disagrees with enumeration")
    return best, best_index


def atomic_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(payload, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    temporary.replace(path)


def run(alpha: float, lam: float, maximum: int, batch_bits: int, output: Path) -> dict[str, Any]:
    a, p, mu = matrices(alpha, lam)
    lower = -math.expm1(-0.25) * lam**alpha / math.sqrt(2)
    upper = 2 * math.sqrt(6) / (1 - mu)**2
    start = time.monotonic()
    result: dict[str, Any] = {
        "purpose": "Exhaustive finite floating-point diagnostic, not an infinite-length proof",
        "started_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "alpha": alpha, "lambda": lam, "mu": mu,
        "lower_constant": lower, "upper_constant": upper,
        "requested_max_length": maximum, "batch_bits": batch_bits,
        "binary_convention": "0=A, 1=P; leftmost digit is leftmost matrix",
        "all_requested_lengths_complete": False,
        "all_checked_bounds_pass": True,
        "records": [],
    }
    for n in range(1, maximum + 1):
        best, index = enumerate_length(n, a, p, batch_bits)
        scale = n**alpha
        passed = lower * scale <= best * (1 + 2e-12) and best <= upper * scale * (1 + 2e-12)
        result["all_checked_bounds_pass"] &= passed
        result["records"].append({
            "length": n, "number_of_words": 1 << n,
            "maximum_spectral_norm": best, "max_over_n_alpha": best / scale,
            "winning_word_binary_index": index,
            "winning_word": format(index, f"0{n}b"),
            "two_sided_bounds_pass": passed,
        })
        result["elapsed_seconds"] = time.monotonic() - start
        result["total_words_checked"] = (1 << (n + 1)) - 2
        atomic_json(output, result)
        print(f"alpha={alpha:g} n={n} max_norm={best:.12g} ratio={best/scale:.12g} "
              f"elapsed={result['elapsed_seconds']:.2f}s", flush=True)
        if not passed:
            raise ArithmeticError(f"a stated bound failed at length {n}; see {output}")
    result["all_requested_lengths_complete"] = True
    result["completed_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
    atomic_json(output, result)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--alpha", type=float, default=0.5)
    parser.add_argument("--lambda", type=float, dest="lam", default=0.25)
    parser.add_argument("--max-length", type=int, default=20)
    parser.add_argument("--batch-bits", type=int, default=14)
    parser.add_argument("--output", type=Path, default=Path("growth_exhaustive.json"))
    parser.add_argument("--allow-expensive", action="store_true",
                        help="explicitly permit lengths above 20 (exponential runtime)")
    args = parser.parse_args()
    if not 1 <= args.max_length <= 30:
        parser.error("max-length must be between 1 and 30")
    if args.max_length > 20 and not args.allow_expensive:
        parser.error("lengths above 20 require --allow-expensive")
    if not 1 <= args.batch_bits <= 18:
        parser.error("batch-bits must be between 1 and 18")
    try:
        run(args.alpha, args.lam, args.max_length, args.batch_bits, args.output)
    except (ValueError, ArithmeticError, OSError) as exc:
        parser.exit(1, f"error: {exc}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
