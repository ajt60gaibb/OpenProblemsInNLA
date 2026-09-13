"""Fourier fixed point for random circulant Lovasz theta.

The fixed point is an exact reformulation; a finite Picard iterate is NOT an
optimizer. All estimates printed by experiments are numerical, not proofs.
"""
from __future__ import annotations
import math
from typing import Any
import numpy as np


def check_signs(signs: np.ndarray) -> np.ndarray:
    s = np.asarray(signs, dtype=float)
    if s.ndim != 1 or len(s) < 2:
        raise ValueError("signs must be a vector of length at least two")
    n = len(s)
    if s[0] != 0 or not np.all(np.isin(s[1:], [-1.0, 1.0])):
        raise ValueError("zero frequency must be zero; all others must be +/-1")
    if not np.array_equal(s, s[(-np.arange(n)) % n]):
        raise ValueError("signs must agree on inversion classes")
    return s


def sample_signs(n: int, rng: np.random.Generator) -> np.ndarray:
    if n < 2:
        raise ValueError("n must be at least two")
    s = np.zeros(n)
    for j in range(1, n // 2 + 1):
        s[j] = s[-j] = rng.choice([-1.0, 1.0])
    return s


def signs_from_mask(n: int, mask: int) -> np.ndarray:
    if mask < 0 or mask >= 2 ** (n // 2):
        raise ValueError("invalid mask")
    s = np.zeros(n)
    for j in range(1, n // 2 + 1):
        s[j] = s[-j] = 1.0 if (mask >> (j - 1)) & 1 else -1.0
    return s


def apply_r(s: np.ndarray, x: np.ndarray) -> np.ndarray:
    return np.fft.ifft(s * np.fft.fft(x)).real


def picard(signs: np.ndarray, t: float, steps: int) -> np.ndarray:
    s = check_signs(signs)
    if not math.isfinite(t) or t < 1 or steps < 0:
        raise ValueError("require finite t >= 1 and steps >= 0")
    v = np.full(len(s), 1.0 / t)
    v[0] = 1.0
    u = np.zeros(len(s))
    for _ in range(steps):
        u = apply_r(s, np.sqrt(v + u * u))
    return u


def worst_case_error_bound(n: int, t: float, steps: int) -> float:
    """Rigorous exact-arithmetic bound D*q**steps from the manuscript.

    Floating-point evaluations of this expression are not interval arithmetic.
    """
    if n < 2 or t < 1 or steps < 0:
        raise ValueError("invalid input")
    W = t + n - 1
    D = math.sqrt(n * W / (2 * t))
    log_q = -0.5 * math.log1p(1.0 / (2 * n * W))
    return D * math.exp(steps * log_q)


def numerical_fixed_point(signs: np.ndarray, t: float) -> dict[str, Any]:
    """Numerical root with residual reporting. Not a certified interval solve."""
    from scipy.optimize import root
    s = check_signs(signs)
    n = len(s)
    if t < 1 or not math.isfinite(t):
        raise ValueError("t must be finite and at least one")
    eye = np.eye(n)
    R = np.column_stack([apply_r(s, eye[:, i]) for i in range(n)])
    u = np.zeros(n)
    times = [1.0]
    while times[-1] < t:
        times.append(min(t, 2 * times[-1]))
    for current in times[1:]:
        v = np.full(n, 1.0 / current); v[0] = 1
        def fun(x):
            return x - R @ np.sqrt(v + x*x)
        def jac(x):
            return eye - R * (x / np.sqrt(v + x*x))[None, :]
        sol = root(fun, u, jac=jac, method='hybr', options={'xtol': 1e-11})
        residual = float(np.linalg.norm(fun(sol.x), np.inf))
        if residual > 2e-8:
            raise RuntimeError(f"root failed: n={n}, t={current}, residual={residual}")
        u = sol.x
    v = np.full(n, 1/t); v[0] = 1
    c = np.sqrt(v + u*u)
    norm = math.sqrt(n * (1 + (n-1)/t))
    # Rationalized forms avoid cancellation when c approximately equals |u|.
    plus = np.where(u >= 0, c + u, v / (c - u))
    minus = np.where(u <= 0, c - u, v / (c + u))
    p, q = plus / norm, minus / norm
    return {'u': u, 'p': p, 'q': q,
            'residual': float(np.linalg.norm(u - apply_r(s, c), np.inf)),
            'theta_lower': float(n*p[0]), 'theta_upper': float(1/q[0])}


def theta_lp(signs: np.ndarray) -> float:
    """Full real Fourier probability LP; signs -1 are edge classes."""
    from scipy.optimize import linprog
    s = check_signs(signs); n = len(s)
    j = np.arange(n)
    rows = [np.ones(n)]
    for frequency in range(1, n//2 + 1):
        if s[frequency] == -1:
            rows.append(np.cos(2*np.pi*frequency*j/n))
            if 2*frequency != n:
                rows.append(np.sin(2*np.pi*frequency*j/n))
    cost = np.zeros(n); cost[0] = -n
    rhs = np.zeros(len(rows)); rhs[0] = 1
    sol = linprog(cost, A_eq=np.array(rows), b_eq=rhs,
                  bounds=(0, None), method='highs')
    if not sol.success:
        raise RuntimeError(sol.message)
    return float(-sol.fun)
