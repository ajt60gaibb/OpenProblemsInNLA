#!/usr/bin/env python3
"""Explicit prime-square sign-matrix kernels for the accompanying partial result.

The p^2-by-p^2 matrix is A[g,h] = kernel[g-h] on F_p^2.  Large dense
matrices are deliberately not materialized.  No internet access is needed.
"""
from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path

import numpy as np
from numpy.typing import NDArray


@dataclass(frozen=True)
class FamilyData:
    prime: int
    nonsquare: int
    epsilon: int
    kernel: NDArray[np.int8]
    base_kernel: NDArray[np.int8]
    character: NDArray[np.int8]
    flip_parameters: NDArray[np.int64]


def is_prime(n: int) -> bool:
    """Deterministic trial-division test; adequate for the supported kernel sizes."""
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, math.isqrt(n) + 1, 2))


def make_family(prime: int, *, memory_limit_mib: int = 256) -> FamilyData:
    """Return the exact integer kernel and construction data.

    The memory guard reserves a conservative 96 bytes per kernel entry for
    optional Fourier diagnostics and temporary arrays, not just the int8 kernel.
    """
    if not isinstance(prime, int) or isinstance(prime, bool):
        raise TypeError("prime must be an integer")
    if not isinstance(memory_limit_mib, int) or isinstance(memory_limit_mib, bool):
        raise TypeError("memory_limit_mib must be an integer")
    if memory_limit_mib <= 0:
        raise ValueError("memory_limit_mib must be positive")
    # Check the budget before trial division so a huge command-line integer
    # cannot cause an unnecessarily long primality test.
    if 96 * prime * prime > memory_limit_mib * 1024**2:
        raise MemoryError("Kernel diagnostics exceed the specified memory budget")
    if prime < 3 or prime % 2 == 0 or not is_prime(prime):
        raise ValueError("prime must be an odd prime")
    p = prime
    chi = np.full(p, -1, dtype=np.int8)
    values = np.arange(1, p, dtype=np.int64)
    chi[(values * values) % p] = 1
    chi[0] = 0
    d = int(np.flatnonzero(chi == -1)[0])
    eps = int(chi[-1])
    t = np.arange(p, dtype=np.int64)
    quadratic = (t[:, None] ** 2 - d * t[None, :] ** 2) % p
    base = chi[quadratic]
    flips = t[chi == 1]
    kernel = base.copy()
    kernel[0, 0] = eps
    kernel[(2*d*flips) % p, (1+d*flips*flips) % p] = eps
    return FamilyData(p, d, eps, kernel, base, chi, flips)


def dense_matrix(data: FamilyData, *, max_order: int = 2000) -> NDArray[np.int8]:
    """Materialize A only for small examples, with an explicit order guard."""
    p = data.prime
    n = p * p
    if n > max_order:
        raise MemoryError(f"Dense order {n} exceeds max_order={max_order}; use the kernel")
    x, y = np.indices((p, p), dtype=np.int64).reshape(2, n)
    return data.kernel[(x[:, None] - x[None, :]) % p,
                       (y[:, None] - y[None, :]) % p]


def spectral_summary(data: FamilyData) -> dict[str, object]:
    """Floating-point FFT diagnostics; the analytic theorem is in the manuscript."""
    p = data.prime
    magnitudes = np.abs(np.fft.fft2(data.kernel))
    low, high = float(magnitudes.min()), float(magnitudes.max())
    error = 2.0 + 3.0 * math.sqrt(p)
    return {
        "prime": p,
        "matrix_order": p * p,
        "nonsquare": data.nonsquare,
        "epsilon": data.epsilon,
        "flip_count": len(data.flip_parameters),
        "row_sum_exact": int(data.kernel.sum(dtype=np.int64)),
        "sigma_min_fft": low,
        "sigma_max_fft": high,
        "condition_fft": high / low if low > 1e-12 else None,
        "analytic_condition_upper_bound": (p + error) / (p - error) if p > error else None,
        "scope": "prime-square family only; not an all-order solution of IS-04",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prime", type=int, default=1009)
    parser.add_argument("--kernel-output", type=Path)
    parser.add_argument("--memory-limit-mib", type=int, default=256)
    args = parser.parse_args()
    try:
        data = make_family(args.prime, memory_limit_mib=args.memory_limit_mib)
        if args.kernel_output:
            args.kernel_output.parent.mkdir(parents=True, exist_ok=True)
            np.save(args.kernel_output, data.kernel, allow_pickle=False)
        print(json.dumps(spectral_summary(data), indent=2, allow_nan=False))
    except (ValueError, TypeError, MemoryError, OSError) as exc:
        parser.error(str(exc))


if __name__ == "__main__":
    main()
