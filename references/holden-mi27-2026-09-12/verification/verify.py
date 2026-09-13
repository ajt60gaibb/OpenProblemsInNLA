#!/usr/bin/env python3
"""Reproducible consistency checks for the MI-27 proof.

These tests are NOT a proof of a universally quantified matrix inequality.
The analytic proof is in ../solution.pdf and ../solution.tex. No optimizer,
network access, GPU, or external data is needed by this script.

Usage:
    python verify.py --output results.json

Exit status is nonzero if a check fails. Floating-point and quadrature
checks have explicit tolerances; symbolic identities are checked exactly.
"""
from __future__ import annotations

import argparse
import json
import platform
from pathlib import Path
from typing import Any, Callable

import mpmath as mp
import numpy as np
import scipy
from scipy.integrate import quad
from scipy.linalg import eigvalsh, expm
import sympy as sp

Array = np.ndarray


def hermitian(x: Array) -> Array:
    return (x + x.conj().T) / 2


def trace_norm(x: Array) -> float:
    return float(np.linalg.svd(x, compute_uv=False).sum())


def positive_trace(x: Array) -> float:
    return float(np.maximum(np.linalg.eigvalsh(hermitian(x)), 0).sum())


def matrix_log(x: Array) -> Array:
    w, u = np.linalg.eigh(hermitian(x))
    if np.min(w) <= 0:
        raise ValueError("matrix_log requires a positive definite matrix")
    return (u * np.log(w)) @ u.conj().T


def entropy(x: Array) -> float:
    w = np.linalg.eigvalsh(hermitian(x))
    if np.min(w) < -1e-12:
        raise ValueError("entropy requires a positive semidefinite matrix")
    w = w[w > 0]
    return float(-np.dot(w, np.log(w)))


def binary_entropy(a: float, b: float) -> float:
    """Use both weights rather than computing a tiny weight as 1-b."""
    if min(a, b) < 0 or abs(a + b - 1) > 1e-12:
        raise ValueError("a,b must be probabilities summing to one")
    q = min(a, b)
    if q == 0:
        return 0.0
    return float(-q * np.log(q) - (1 - q) * np.log1p(-q))


def relative_entropy(rho: Array, sigma: Array) -> float:
    return float(np.trace(rho @ (matrix_log(rho) - matrix_log(sigma))).real)


def random_state(n: int, rng: np.random.Generator, *, complex_: bool = True) -> Array:
    x = rng.normal(size=(n, n))
    if complex_:
        x = x + 1j * rng.normal(size=(n, n))
    x = x @ x.conj().T + 0.15 * np.eye(n)
    return x / np.trace(x).real


def random_hamiltonian(n: int, rng: np.random.Generator) -> Array:
    x = hermitian(rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n)))
    return x / np.max(np.abs(np.linalg.eigvalsh(x)))


def assert_close(x: float, y: float, *, atol: float, label: str) -> None:
    if not np.isfinite(x + y) or abs(x - y) > atol:
        raise AssertionError(f"{label}: {x:.17g} != {y:.17g}; tolerance {atol:g}")


def symbolic_checks() -> dict[str, Any]:
    a, g, t = sp.symbols("a g t", positive=True)
    b = 1 - a
    w1 = b**2 / (g * (b + a*g)**2)
    w2 = b**2 / (a + b*g)**2
    k1 = a*b / (g * (b + a*g))
    k2 = a*b / (g * (a + b*g))
    checks = {
        "skew_first_primitive": sp.diff(sp.log(g)-sp.log(b+a*g)+b/(b+a*g), g)-w1,
        "skew_second_primitive": sp.diff(-b/(a+b*g), g)-w2,
        "holevo_first_primitive": sp.diff(a*(sp.log(g)-sp.log(b+a*g)), g)-k1,
        "holevo_second_primitive": sp.diff(b*(sp.log(g)-sp.log(a+b*g)), g)-k2,
        "holevo_first_kernel_combination": a*w1+b*a**2/(b+a*g)**2-k1,
        "holevo_second_kernel_combination": a*w2+b*a**2/(g*(a+b*g)**2)-k2,
    }
    d = (1-2*t**2)*t*(1-t)
    S = sp.diag(1-t, t)
    B = t**2*S + d*sp.ones(2)
    A = S-B
    determinant = t**3*(1-t)*(1-t**2)
    checks["sharpness_det_A"] = A.det()-determinant
    checks["sharpness_det_B"] = B.det()-determinant
    checks["sharpness_trace_B"] = sp.trace(B)-(t**2+2*d)
    for name, expression in checks.items():
        if sp.simplify(expression) != 0:
            raise AssertionError(f"symbolic identity failed: {name}")
    return {"exact_identities": list(checks), "passed": len(checks)}


def integration_points(rho: Array, sigma: Array) -> list[float]:
    """Zeros of det(z*rho-sigma) and det(z*sigma-rho), within (0,1).

    Supplying these generalized eigenvalues prevents adaptive quadrature
    from overlooking the positive-part kinks or short nonzero intervals.
    """
    values = np.r_[eigvalsh(sigma, rho), eigvalsh(rho, sigma)]
    return sorted(set(float(v) for v in values if 1e-15 < v < 1-1e-15))


def integrate_with_breaks(f: Callable[[float], float], points: list[float]) -> tuple[float, float]:
    value, error = quad(f, 0, 1, points=points, epsabs=2e-12, epsrel=2e-12, limit=500)
    return float(value), float(error)


def integral_checks(rng: np.random.Generator) -> dict[str, Any]:
    records = []
    for n in (2, 3, 5, 8):
        for a in (0.01, 0.1, 0.5, 0.9, 0.99):
            b = 1-a
            rho, sigma = random_state(n, rng), random_state(n, rng)
            M = a*rho+b*sigma
            points = integration_points(rho, sigma)

            # z = 1/gamma. The pencils below avoid multiplying by large gamma.
            def pencils(z: float) -> tuple[float, float]:
                return positive_trace(z*rho-sigma), positive_trace(z*sigma-rho)

            def f_D(z: float) -> float:
                if z == 0:
                    return 0.0
                F, G = pencils(z)
                return F/z**2 + G/z

            def f_skew(z: float) -> float:
                if z == 0:
                    return 0.0
                F, G = pencils(z)
                return b*b*F/(a+b*z)**2 + b*b*G/(z*(b+a*z)**2)

            def f_chi(z: float) -> float:
                if z == 0:
                    return 0.0
                F, G = pencils(z)
                return a*b*(F/(z*(a+b*z)) + G/(z*(b+a*z)))

            D_integral, D_error = integrate_with_breaks(f_D, points)
            skew_integral, skew_error = integrate_with_breaks(f_skew, points)
            chi_integral, chi_error = integrate_with_breaks(f_chi, points)
            D_direct = relative_entropy(rho, sigma)
            skew_direct = relative_entropy(rho, M)
            chi_direct = a*skew_direct+b*relative_entropy(sigma, M)
            for label, direct, numerical in (
                ("Frenkel-Hirche-Tomamichel identity", D_direct, D_integral),
                ("skew integral", skew_direct, skew_integral),
                ("Holevo integral", chi_direct, chi_integral),
            ):
                assert_close(direct, numerical, atol=2e-9, label=label)
            records.append({
                "n": n, "a": a,
                "relative_entropy_error": abs(D_direct-D_integral),
                "skew_error": abs(skew_direct-skew_integral),
                "holevo_error": abs(chi_direct-chi_integral),
                "quadrature_estimates": [D_error, skew_error, chi_error],
            })
    return {"cases": len(records), "records": records,
            "max_absolute_error": max(max(r["relative_entropy_error"], r["skew_error"],
                                          r["holevo_error"]) for r in records)}


def elementary_checks(rng: np.random.Generator) -> dict[str, Any]:
    worst_commutator = 0.0
    worst_hockey_derivative = 0.0
    worst_commutation_residual = 0.0
    count = 0
    for n in (2, 3, 5, 10, 20):
        for _ in range(15):
            rho, sigma = random_state(n, rng), random_state(n, rng)
            H = random_hamiltonian(n, rng)
            for gamma in (1.0, 1.01, 2.0, 10.0):
                w, u = np.linalg.eigh(rho-gamma*sigma)
                Q = u[:, w > 0] @ u[:, w > 0].conj().T
                c_rho, c_sigma = rho@Q-Q@rho, sigma@Q-Q@sigma
                cr = trace_norm(c_rho)
                residual = trace_norm(c_rho-gamma*c_sigma)
                derivative = abs(np.trace(H @ (-1j*gamma*c_sigma)).real)
                if cr > 1+2e-11 or derivative > 1+2e-11 or residual > 2e-10:
                    raise AssertionError("positive-part derivative/commutator bound failed")
                worst_commutator = max(worst_commutator, cr)
                worst_hockey_derivative = max(worst_hockey_derivative, derivative)
                worst_commutation_residual = max(worst_commutation_residual, residual)
                count += 1

    # Exact saturation of ||[rho,Q]||_1 <= 1.
    rho = np.ones((2, 2))/2
    Q = np.diag([1.0, 0.0])
    assert_close(trace_norm(rho@Q-Q@rho), 1.0, atol=1e-14, label="commutator sharpness")

    # A nondifferentiable positive-part example: E_1(rho||sigma_t)=|sin(t)|.
    rho = np.diag([1.0, 0.0])
    for t in (-0.2, -1e-6, 0.0, 1e-6, 0.2):
        v = np.array([np.cos(t), np.sin(t)])
        value = positive_trace(rho-np.outer(v, v))
        assert_close(value, abs(np.sin(t)), atol=2e-14, label="eigenvalue-crossing example")
        if value > abs(t)+1e-14:
            raise AssertionError("crossing Lipschitz check failed")

    # The constant one is sharp for each gamma>1, already for pure qubits.
    sharp_derivatives = []
    delta = 1e-5
    for gamma in (1.01, 1.5, 2.0, 10.0):
        theta = np.arcsin(np.sqrt((gamma-1)/(2*gamma)))
        def value(angle: float) -> float:
            v = np.array([np.cos(angle), np.sin(angle)])
            return positive_trace(rho-gamma*np.outer(v, v))
        derivative = (value(theta+delta)-value(theta-delta))/(2*delta)
        assert_close(derivative, 1.0, atol=1e-7, label="hockey-stick sharpness")
        sharp_derivatives.append({"gamma": gamma, "finite_difference": derivative})

    return {"random_cases": count, "max_commutator_norm": worst_commutator,
            "max_hockey_derivative": worst_hockey_derivative,
            "max_commutation_residual": worst_commutation_residual,
            "crossing_cases": 5, "sharp_derivatives": sharp_derivatives}


def matrix_inequality_checks(rng: np.random.Generator) -> dict[str, Any]:
    ratios = []
    finite_ratios = []
    derivative_errors = []
    for n in (2, 3, 5, 8, 16, 32):
        for complex_ in (False, True):
            for b in (1e-8, 1e-4, 0.05, 0.25, 0.5, 0.95, 1-1e-4):
                a = 1-b
                rho = random_state(n, rng, complex_=complex_)
                sigma = random_state(n, rng, complex_=complex_)
                A, B = a*rho, b*sigma
                S = A+B
                logS = matrix_log(S)
                C = B@logS-logS@B
                K = hermitian(-1j*C)
                numerator = trace_norm(C)
                bound = binary_entropy(a, b)
                ratio = numerator/bound
                if numerator > bound+2e-11:
                    raise AssertionError("MI-27 random consistency check failed")
                ratios.append(ratio)

                # Trace-norm dual witness: H=sign(-i[B,log S]).
                w, u = np.linalg.eigh(K)
                H = (u*np.sign(w))@u.conj().T
                direct_derivative = float(np.trace(H@K).real)
                assert_close(direct_derivative, numerator, atol=3e-11, label="dual witness")
                if n <= 8 and b in (0.05, 0.25, 0.5, 0.95):
                    epsilon = 2e-5
                    def rotated_entropy(t: float) -> float:
                        U = expm(1j*t*H)
                        return entropy(A+U@B@U.conj().T)
                    fd = (rotated_entropy(epsilon)-rotated_entropy(-epsilon))/(2*epsilon)
                    assert_close(fd, direct_derivative, atol=5e-8, label="entropy derivative")
                    derivative_errors.append(abs(fd-direct_derivative))
                    for t in (-0.25, 0.01, 0.3):
                        difference = abs(rotated_entropy(t)-entropy(S))
                        limit = abs(t)*bound
                        if difference > limit+2e-11:
                            raise AssertionError("finite-time entropy Lipschitz check failed")
                        finite_ratios.append(difference/limit)
    return {"matrix_cases": len(ratios), "max_MI27_ratio": max(ratios),
            "finite_time_cases": len(finite_ratios), "max_finite_time_ratio": max(finite_ratios),
            "entropy_derivative_cases": len(derivative_errors),
            "max_entropy_derivative_error": max(derivative_errors)}


def weight_mass_checks() -> dict[str, Any]:
    records = []
    with mp.workdps(70):
        for alpha in ("0.001", "0.01", "0.1", "0.5", "0.9", "0.99", "0.999"):
            a = mp.mpf(alpha)
            b = 1-a
            # Finite interval z=1/gamma; weights already include the Jacobian.
            m1 = mp.quad(lambda z: b*b*z/(a+b*z)**2, [0, 1])
            m2 = mp.quad(lambda z: b*b/(b+a*z)**2, [0, 1])
            c1 = mp.quad(lambda z: a*b/(a+b*z), [0, 1])
            c2 = mp.quad(lambda z: a*b/(b+a*z), [0, 1])
            error = max(abs(m1-(-mp.log(a)-b)), abs(m2-b),
                        abs(c1+a*mp.log(a)), abs(c2+b*mp.log(b)))
            if error > mp.mpf("1e-60"):
                raise AssertionError("weight mass integral failed")
            records.append({"a": alpha, "max_error": mp.nstr(error, 8)})
    return {"cases": len(records), "decimal_precision": 70, "records": records}


def sharpness_checks() -> list[dict[str, str]]:
    records = []
    previous_ratio = mp.mpf(0)
    for k in (2, 4, 8, 16, 32, 64, 128, 256):
        with mp.workdps(max(100, 2*k+80)):
            t = mp.mpf(10)**(-k)
            d = (1-2*t*t)*t*(1-t)
            b = t*t+2*d
            numerator = 2*d*(mp.log1p(-t)-mp.log(t))
            denominator = -b*mp.log(b)-(1-b)*mp.log1p(-b)
            ratio = numerator/denominator
            determinant = t**3*(1-t)*(1-t*t)
            if not (0 < t*t < 1-t*t < 1 and determinant > 0 and previous_ratio < ratio < 1):
                raise AssertionError("strict-PD sharpness-family check failed")
            records.append({"t": f"1e-{k}", "ratio": mp.nstr(ratio, 40),
                            "b": mp.nstr(b, 30), "det_A_equals_det_B": mp.nstr(determinant, 25)})
            previous_ratio = ratio
    return records


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=270912, help="deterministic NumPy RNG seed")
    parser.add_argument("--output", type=Path, default=Path("results.json"))
    args = parser.parse_args()
    rng = np.random.default_rng(args.seed)
    results: dict[str, Any] = {
        "status": "running", "seed": args.seed,
        "scope": "Consistency checks only. The universal inequality is proved analytically.",
        "versions": {"python": platform.python_version(), "numpy": np.__version__,
                     "scipy": scipy.__version__, "sympy": sp.__version__, "mpmath": mp.__version__},
    }
    tasks = [
        ("symbolic", symbolic_checks),
        ("positive_part", lambda: elementary_checks(rng)),
        ("weight_masses", weight_mass_checks),
        ("integral_identities", lambda: integral_checks(rng)),
        ("matrix_inequality", lambda: matrix_inequality_checks(rng)),
        ("sharpness_family", sharpness_checks),
    ]
    for name, task in tasks:
        print(f"Checking {name} ...", flush=True)
        results[name] = task()
        print(f"  PASS: {name}", flush=True)
    results["status"] = "all checks passed"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"status": results["status"], "output": str(args.output),
                      "max_integral_error": results["integral_identities"]["max_absolute_error"],
                      "max_random_MI27_ratio": results["matrix_inequality"]["max_MI27_ratio"]}, indent=2))


if __name__ == "__main__":
    main()
