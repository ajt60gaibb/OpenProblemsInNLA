"""Floating-point demonstration of the exact-real algorithm proved in the paper.

This is NOT a finite-precision implementation theorem. The universal guarantee
is the mathematical exact-real guarantee in IE12_solution.pdf. Dense products
are available as a convenient experimental backend; the asymptotic proof uses
weighted-pattern products. All reported final errors are recomputed with A.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Literal
import math
import numpy as np
from weighted_matvec import (WeightedMatvec, PatternCatalogue, choose_k,
                             floor_by_comparisons)


def ceil_log2_by_doubling(value: int) -> int:
    if value <= 0:
        raise ValueError("value must be positive")
    exponent, power = 0, 1
    while power < value:
        power *= 2
        exponent += 1
    return exponent


def uniforms_from_gaussians(rng: np.random.Generator, shape: tuple[int, ...]):
    """Exact-real construction: normalized first coordinate on the 2-sphere.

    In floating-point arithmetic this only approximates the exact distribution.
    """
    gaussian = rng.standard_normal(shape + (3,))
    radius = np.sqrt(np.sum(gaussian * gaussian, axis=-1))
    nonzero = radius > 0
    uniform = np.full(shape, 0.5)
    uniform[nonzero] = (1.0 + gaussian[..., 0][nonzero] / radius[nonzero]) / 2.0
    return uniform


def stochastic_quantize(A, epsilon: float, rng: np.random.Generator,
                        floor_backend: Literal["scan", "numpy"] = "scan"):
    A = np.asarray(A, dtype=float)
    n = A.shape[0]
    h = epsilon / (64.0 * math.sqrt(n))
    scaled = A / h
    if not np.all(np.isfinite(scaled)):
        raise FloatingPointError("scaled input is outside the floating-point range")
    if floor_backend == "scan":
        floors = np.array([[floor_by_comparisons(value) for value in row]
                           for row in scaled], dtype=float)
    elif floor_backend == "numpy":
        # Experimental shortcut only; the proof explicitly pays for comparisons.
        floors = np.floor(scaled)
    else:
        raise ValueError("unknown floor backend")
    uniform = uniforms_from_gaussians(rng, scaled.shape)
    rounded = floors + (uniform < scaled - floors)
    Z = [[int(value) for value in row] for row in rounded]
    Q = h * rounded
    return Z, Q, h


@dataclass
class SolverResult:
    x: np.ndarray
    backward_error: float
    augmented_relative_residual: float
    steps: int
    theoretical_step_cap: int
    used_step_cap: int
    truncated: bool
    k: int
    integer_weight: int
    quantization_error: float | None
    backend: str
    certificate_passed: bool


def solve(A, b, epsilon: float, *, seed: int = 0,
          backend: Literal["compressed", "dense"] = "compressed",
          floor_backend: Literal["scan", "numpy"] = "scan",
          max_steps: int | None = None,
          measure_quantization_norm: bool = False) -> SolverResult:
    """Run the construction on a finite floating-point test instance.

    Input promise: ||A||_2=1. This promise is not checked by an expensive SVD.
    An optional max_steps is a resource cap for experiments; truncation disables
    the theorem's fixed-time guarantee. An exact-arithmetic augmented-residual
    early exit is valid and never increases the stated operation count.
    """
    A, b = np.asarray(A, dtype=float), np.asarray(b, dtype=float)
    if A.ndim != 2 or A.shape[0] != A.shape[1] or A.shape[0] < 1:
        raise ValueError("A must be a nonempty square matrix")
    n = A.shape[0]
    if b.shape != (n,) or not np.all(np.isfinite(A)) or not np.all(np.isfinite(b)):
        raise ValueError("inputs must have compatible shapes and finite entries")
    if not math.isfinite(epsilon) or not 0 < epsilon < 0.5:
        raise ValueError("epsilon must lie strictly between 0 and 1/2")
    beta = float(np.linalg.norm(b))
    if not math.isfinite(beta) or beta <= 0:
        raise ValueError("b must be nonzero with representable Euclidean norm")
    c, eta = b / beta, epsilon / 8.0
    rng = np.random.default_rng(seed)
    Z, Q, h = stochastic_quantize(A, epsilon, rng, floor_backend)
    k = choose_k(n)
    weight = sum(1 + abs(z) for row in Z for z in row)
    if backend == "compressed":
        catalogue = PatternCatalogue(k)
        forward = WeightedMatvec(Z, k, catalogue)
        transpose = WeightedMatvec([list(column) for column in zip(*Z)], k, catalogue)
        q_product = lambda x: h * forward.apply_numpy(x)
        qt_product = lambda x: h * transpose.apply_numpy(x)
    elif backend == "dense":
        q_product = lambda x: Q @ x
        qt_product = lambda x: Q.T @ x
    else:
        raise ValueError("unknown product backend")
    ell = ceil_log2_by_doubling(10**9 * (n + 1))
    cap = math.ceil(4 * ell / (eta * eta))
    if max_steps is not None and (not isinstance(max_steps, int) or max_steps < 0):
        raise ValueError("max_steps must be a nonnegative integer or None")
    used_cap = cap if max_steps is None else min(cap, max_steps)
    z = rng.standard_normal(n + 1)
    u, alpha = z[:n].copy(), float(z[n])
    steps = 0
    for _ in range(used_cap):
        residual = q_product(u) - c * alpha
        norm_z = math.sqrt(float(u @ u) + alpha * alpha)
        if norm_z > 0 and np.linalg.norm(residual) <= eta * norm_z:
            break
        u = u - qt_product(residual) / 4.0
        alpha += float(c @ residual) / 4.0
        steps += 1
    residual = q_product(u) - c * alpha
    norm_z = math.sqrt(float(u @ u) + alpha * alpha)
    augmented_error = float(np.linalg.norm(residual) / norm_z) if norm_z > 0 else math.inf
    norm_u = float(np.linalg.norm(u))
    if norm_u == 0:
        x = np.zeros(n)
        x[0] = beta
    else:
        alpha_prime = max(abs(alpha), eta * norm_u)
        if alpha < 0:
            alpha_prime = -alpha_prime
        x = (beta / alpha_prime) * u
    if not np.all(np.isfinite(x)) or np.linalg.norm(x) == 0:
        raise FloatingPointError("prototype encountered floating-point failure")
    backward_error = float(np.linalg.norm(A @ x - b) / np.linalg.norm(x))
    quantization_norm = (float(np.linalg.norm(Q - A, 2))
                         if measure_quantization_norm else None)
    return SolverResult(x, backward_error, augmented_error, steps, cap, used_cap,
                        used_cap < cap, k, weight, quantization_norm,
                        backend, backward_error <= epsilon)


if __name__ == "__main__":
    A = np.array([[1., 0.], [0., 1e-12]])
    b = np.array([1., 1.])
    result = solve(A, b, 0.25, seed=7)
    print("x =", result.x)
    print("backward error =", result.backward_error)
    print("steps =", result.steps)
    print("certificate passed =", result.certificate_passed)
