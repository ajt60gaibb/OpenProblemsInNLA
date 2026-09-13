"""Companion calculations for the RA-05 lower-bound manuscript.

The asymptotic existence proofs are in the manuscript. Numerical diagnostics
here do not certify a uniform continuum guarantee or prove a theorem.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import ceil, comb, floor, isfinite, sqrt
from typing import Callable

import numpy as np
from numpy.typing import NDArray
from scipy.linalg import qr

FloatArray = NDArray[np.float64]
IntArray = NDArray[np.int64]


def validate_p(p: float) -> float:
    p = float(p)
    if not isfinite(p) or p <= 2:
        raise ValueError("p must be a finite real number greater than 2")
    return p


def normalize_rows(a: FloatArray) -> FloatArray:
    a = np.asarray(a, dtype=float)
    if a.ndim != 2 or not np.isfinite(a).all():
        raise ValueError("expected a finite two-dimensional array")
    norms = np.linalg.norm(a, axis=1)
    if np.any(norms == 0):
        raise ValueError("cannot normalize a zero row")
    return a / norms[:, None]


def derivative_stencil(q: int) -> list[Fraction]:
    """Exact derivative-at-zero interpolation weights at nodes 0,...,q."""
    if not isinstance(q, int) or q < 1:
        raise ValueError("q must be a positive integer")
    return [-sum((Fraction(1, j) for j in range(1, q + 1)), Fraction(0))] + [
        Fraction((-1) ** (j + 1) * comb(q, j), j) for j in range(1, q + 1)
    ]


def finite_difference(fun: Callable[[float], float], t: float, q: int) -> float:
    if not isfinite(t) or t <= 0:
        raise ValueError("t must be positive and finite")
    return sum(float(d) * fun(j * t)
               for j, d in enumerate(derivative_stencil(q))) / t


def psi(a: FloatArray, p: float) -> FloatArray:
    """phi'(a)/p, with phi(a)=|a|**p; this is NOT an ordinary matrix power."""
    p = validate_p(p)
    a = np.asarray(a, dtype=float)
    return a * np.abs(a) ** (p - 2)


def derivative_kernel(z: FloatArray, u: FloatArray, p: float) -> FloatArray:
    z = np.asarray(z, dtype=float)
    u = np.asarray(u, dtype=float)
    if z.ndim != 2 or u.ndim != 2 or z.shape[1] != u.shape[1]:
        raise ValueError("z and u must have the same ambient dimension")
    return psi(z @ u.T, p)


@dataclass
class CoreDiagnostic:
    z: FloatArray
    u: FloatArray
    indices: NDArray[np.int64]
    evaluation: FloatArray
    report: dict


def sampled_core(r: int, p: float, seed: int = 0) -> CoreDiagnostic:
    """Generate a small illustrative core and check its selected singular value.

    Pivoted QR is a heuristic here, NOT an implementation or proof of the
    restricted-invertibility theorem. The returned lower singular value is
    explicitly measured. Small r need not meet the asymptotic Frobenius event.
    """
    p = validate_p(p)
    if r < 2:
        raise ValueError("r must be at least 2")
    L = floor(r ** (p / 2))
    if L > 2500:
        raise ValueError("diagnostic capped at 2500 candidate vectors")
    M = max(1, L // 48)
    rng = np.random.default_rng(seed)
    z = normalize_rows(rng.normal(size=(L, r)))
    K = derivative_kernel(z, z, p)
    eig, Q = np.linalg.eigh(K)
    good = (eig >= 0.5) & (eig <= 1.5)
    if not np.any(good):
        raise RuntimeError("no good spectral subspace for this diagnostic draw")
    B = (Q[:, good] * eig[good]) @ Q[:, good].T
    _, _, piv = qr(B, mode="economic", pivoting=True)
    indices = np.sort(piv[:M]).astype(np.int64)
    u = z[indices]
    E = K[:, indices]
    sig2 = float(np.linalg.svd(E, compute_uv=False)[-1] ** 2)
    stable_rank = float(np.sum(eig[good] ** 2) / np.max(eig[good] ** 2))
    report = {
        "r": r, "p": p, "L": L, "M": M,
        "frobenius_squared": float(np.sum((K - np.eye(L)) ** 2)),
        "frobenius_threshold": L / 16,
        "frobenius_condition_met": bool(np.sum((K - np.eye(L)) ** 2) <= L / 16),
        "good_eigenvalue_count": int(good.sum()),
        "minimum_kernel_eigenvalue": float(eig[0]),
        "truncated_stable_rank": stable_rank,
        "selected_minimum_singular_value_squared": sig2,
        "comparison_target_3_over_64": 3 / 64,
        "selected_target_met": bool(sig2 >= 3 / 64),
        "warning": "Numerical diagnostic, not a certificate of the asymptotic lemma."
    }
    return CoreDiagnostic(z, u, indices, E, report)


def product_cost(u: FloatArray, v: FloatArray, x: FloatArray, y: FloatArray,
                 p: float, weights: FloatArray | None = None) -> float:
    """Cost for rows N^(-1/p)(u_j,v_t) at the unnormalized normal (x,y)."""
    p = validate_p(p)
    u, v = np.asarray(u, float), np.asarray(v, float)
    x, y = np.asarray(x, float), np.asarray(y, float)
    if u.ndim != 2 or v.ndim != 2 or x.shape != (u.shape[1],) or y.shape != (v.shape[1],):
        raise ValueError("incompatible matrix/vector dimensions")
    values = np.abs((u @ x)[:, None] + (v @ y)[None, :]) ** p
    if weights is not None:
        weights = np.asarray(weights, float)
        if weights.shape != values.shape or not np.isfinite(weights).all():
            raise ValueError("weights must be finite and have shape (M,N)")
        values *= weights
    return float(np.sum(values) / len(v))


def mean_error(u: FloatArray, v: FloatArray, weights: FloatArray) -> FloatArray:
    weights = np.asarray(weights, float)
    if weights.shape != (len(u), len(v)):
        raise ValueError("weights must have shape (M,N)")
    return weights @ v / len(v) - np.mean(v, axis=0)[None, :]


def product_error_derivative(u: FloatArray, v: FloatArray, weights: FloatArray,
                             x: FloatArray, y: FloatArray, p: float) -> float:
    H = mean_error(u, v, weights)
    return float(p * psi(u @ x, p) @ H @ y)


def explicit_product_rows(u: FloatArray, v: FloatArray, p: float,
                          max_entries: int = 5_000_000) -> FloatArray:
    """Materialize a small product matrix, refusing accidentally huge output."""
    p = validate_p(p)
    M, r = u.shape
    N, s = v.shape
    if M * N * (r + s) > max_entries:
        raise ValueError("matrix exceeds the explicit-entry limit")
    return np.concatenate((np.repeat(u, N, axis=0), np.tile(v, (M, 1))), axis=1) / N ** (1 / p)


# Binary finite fields and the complete real mutually unbiased bases.
def poly_mod(a: int, modulus: int) -> int:
    degree = modulus.bit_length() - 1
    while a and a.bit_length() - 1 >= degree:
        a ^= modulus << (a.bit_length() - 1 - degree)
    return a


def poly_gcd(a: int, b: int) -> int:
    while b:
        a, b = b, poly_mod(a, b)
    return a


def gf_mul(a: int, b: int, modulus: int) -> int:
    out = 0
    degree = modulus.bit_length() - 1
    while b:
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
        if a & (1 << degree):
            a ^= modulus
    return out


def irreducible_polynomial(degree: int) -> int:
    if degree < 1:
        raise ValueError("positive field degree required")
    for modulus in range((1 << degree) | 1, 1 << (degree + 1), 2):
        x = poly_mod(2, modulus)
        z = x
        ok = True
        for i in range(1, degree + 1):
            z = gf_mul(z, z, modulus)
            if i <= degree // 2 and poly_gcd(z ^ x, modulus) != 1:
                ok = False
                break
        if ok and z == x:
            return modulus
    raise RuntimeError("irreducible polynomial search failed")


def field_trace(a: int, degree: int, modulus: int) -> int:
    out, z = 0, a
    for _ in range(degree):
        out ^= z
        z = gf_mul(z, z, modulus)
    if out not in (0, 1):
        raise ArithmeticError("trace did not land in the prime field")
    return out


def binary_rank(a: IntArray) -> int:
    a = (np.asarray(a, dtype=np.int64) & 1).copy()
    row = 0
    for col in range(a.shape[1]):
        pivots = np.flatnonzero(a[row:, col])
        if len(pivots) == 0:
            continue
        pivot = row + int(pivots[0])
        a[[row, pivot]] = a[[pivot, row]]
        for k in range(a.shape[0]):
            if k != row and a[k, col]:
                a[k] ^= a[row]
        row += 1
        if row == a.shape[0]:
            break
    return row


def real_mub(h: int) -> tuple[IntArray, list[IntArray], dict]:
    """Return T = sqrt(r) U in integer arithmetic, r=4**h.

    Each block of r rows is one basis. The first block is sqrt(r) I;
    subsequent blocks have entries +/-1. Thus U=T/sqrt(r).
    """
    if not isinstance(h, int) or h < 1 or h > 4:
        raise ValueError("supported diagnostic range is 1 <= h <= 4")
    m = 2 * h - 1
    r = 4 ** h
    modulus = irreducible_polynomial(m)
    size_E = 1 << m
    tr = [field_trace(a, m, modulus) for a in range(size_E)]

    def beta(a: int, z: int, w: int) -> int:
        t, x = z & 1, z >> 1
        s, y = w & 1, w >> 1
        ax, ay = gf_mul(a, x, modulus), gf_mul(a, y, modulus)
        return tr[gf_mul(ax, ay, modulus)] ^ (tr[ax] & tr[ay]) ^ (t & tr[ay]) ^ (s & tr[ax])

    chars = np.array([[1 - 2 * ((ell & z).bit_count() & 1)
                       for z in range(r)] for ell in range(r)], dtype=np.int64)
    forms: list[IntArray] = []
    blocks = [int(sqrt(r)) * np.eye(r, dtype=np.int64)]
    for a in range(size_E):
        form = np.array([[beta(a, 1 << i, 1 << j) for j in range(m + 1)]
                         for i in range(m + 1)], dtype=np.int64)
        forms.append(form)
        signs = []
        for z in range(r):
            value = 0
            for i in range(m + 1):
                if (z >> i) & 1:
                    for j in range(i + 1, m + 1):
                        value ^= int(form[i, j]) & ((z >> j) & 1)
            signs.append(1 - 2 * value)
        blocks.append(chars * np.asarray(signs, dtype=np.int64)[None, :])
    return np.vstack(blocks), forms, {"r": r, "field_degree": m, "field_modulus_binary": bin(modulus)}


def orthogonal_noise_cost(u: FloatArray, delta: float, x: FloatArray,
                          y: FloatArray, weights: FloatArray | None = None) -> float:
    r = u.shape[1]
    vals = ((u @ x)[:, None] + delta * y[None, :]) ** 4
    if weights is not None:
        if weights.shape != vals.shape:
            raise ValueError("weights must have shape (M,r)")
        vals *= weights
    return float(vals.sum() / r)


def quartic_witness(u: FloatArray, weights: FloatArray) -> dict:
    """Find the four-query witness from the explicit quartic theorem."""
    M, r = u.shape
    if weights.shape != (M, r):
        raise ValueError("weights must have shape (M,r)")
    B = r / 2 + 1
    delta = B ** (-0.25)
    H = (weights - 1) / r
    KH = (1 - 1 / r) * H + u @ (u.T @ H) / r
    row_norms = np.linalg.norm(KH, axis=1)
    i = int(np.argmax(row_norms))
    if row_norms[i] == 0:
        raise ValueError("the candidate has no mixed-coefficient error")
    x, y = u[i], KH[i] / row_norms[i]
    candidates = []
    for scale, sign in ((1, 1), (1, -1), (2, 1), (2, -1)):
        xx, yy = scale * x, sign * y
        f = orthogonal_noise_cost(u, delta, xx, yy)
        fw = orthogonal_noise_cost(u, delta, xx, yy, weights)
        rel = abs(fw - f) / f
        z = np.r_[xx, yy]
        z /= np.linalg.norm(z)
        candidates.append({"scale_x": scale, "sign_y": sign,
                           "cost": f, "weighted_cost": fw, "relative_error": rel,
                           "normal": z.tolist()})
    best = max(candidates, key=lambda item: item["relative_error"])
    return {"r": r, "M": M, "rows": M * r,
            "support": int(np.count_nonzero(weights)), "delta": delta,
            "target_epsilon": delta / (20 * sqrt(r)),
            "guaranteed_witness_error": float(delta * row_norms[i] / 10),
            "candidates": candidates, "best": best}
