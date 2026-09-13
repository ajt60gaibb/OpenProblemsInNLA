#!/usr/bin/env python3
"""Reproduce exact finite checks and numerical diagnostics.

Run from the package root:
    OPENBLAS_NUM_THREADS=1 python code/verify.py --output results

No finite test below is substituted for the manuscript's universal proofs.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from itertools import combinations
import json
import math
from pathlib import Path
import platform
import sys
import time

import mpmath as mp
import numpy as np
import scipy

from ra05 import (binary_rank, derivative_stencil, derivative_kernel,
                  explicit_product_rows, finite_difference, mean_error,
                  normalize_rows, product_cost, product_error_derivative,
                  quartic_witness, real_mub, sampled_core)

CHECKS = 0


def check(condition: bool, message: str) -> None:
    global CHECKS
    CHECKS += 1
    if not condition:
        raise AssertionError(message)


def exact_stencils() -> dict:
    identities = 0
    for q in range(1, 17):
        d = derivative_stencil(q)
        for ell in range(q + 1):
            value = sum((d[j] * j ** ell for j in range(q + 1)), Fraction(0))
            check(value == (1 if ell == 1 else 0), f"stencil q={q}, degree={ell}")
            identities += 1
    return {"arithmetic": "exact rational", "degrees": [1, 16], "moment_identities": identities}


def exact_even_extraction() -> dict:
    rng = np.random.default_rng(9231)
    reports = []
    for p in (4, 6, 8, 10, 12):
        atoms = [(Fraction(int(rng.integers(-8, 9)), 5),
                  Fraction(int(rng.integers(-8, 9)), 7),
                  Fraction(int(rng.integers(-4, 5)), 3)) for _ in range(16)]
        t = Fraction(1, 3)
        def h(s: Fraction) -> Fraction:
            return sum((c * (a + b * s) ** p for a, b, c in atoms), Fraction(0))
        numerical_name_but_exact = sum((d * h(j * t) for j, d in enumerate(derivative_stencil(p))), Fraction(0)) / t
        actual = sum((c * p * a ** (p - 1) * b for a, b, c in atoms), Fraction(0))
        check(numerical_name_but_exact == actual, f"exact even extraction p={p}")
        reports.append({"p": p, "atoms": len(atoms), "exact_residual": "0"})
    return {"arithmetic": "exact rational", "cases": reports}


def taylor_diagnostics() -> dict:
    mp.mp.dps = 100
    cases = []
    aa = ["0", "0.000001", "-0.000001", "0.25", "-0.25", "0.5", "-0.5", "1", "-1", "2", "-2", "10", "-10", "1000", "-1000"]
    for pp in ("2.01", "2.1", "2.5", "3", "3.1", "3.9", "4", "4.5", "5", "5.9", "6", "7.25", "10.5"):
        p = mp.mpf(pp)
        q = int(mp.ceil(p)) - 1
        largest = mp.mpf(0)
        for astr in aa:
            a = mp.mpf(astr)
            for b in (mp.mpf(-1), mp.mpf(1)):
                polynomial = abs(a) ** p
                falling = mp.mpf(1)
                for ell in range(1, q + 1):
                    falling *= p - ell + 1
                    deriv = falling * (mp.sign(a) ** ell) * abs(a) ** (p - ell)
                    polynomial += deriv * b ** ell / mp.factorial(ell)
                residual = abs(abs(a + b) ** p - polynomial) / abs(b) ** p
                check(residual <= 2 + mp.mpf("1e-60"), f"Taylor bound p={pp}, a={a}")
                largest = max(largest, residual)
        cases.append({"p": pp, "q": q, "points": 2 * len(aa),
                      "maximum_remainder_over_abs_b_to_p": str(largest)})
    return {"arithmetic": "100-digit floating point", "scope": "finite scalar test points only", "cases": cases}


def gaussian_increment_identity() -> dict:
    rng = np.random.default_rng(619)
    maximum = 0.0
    for p in (2.1, 3., 4., 6.5):
        pstar = p / (p - 1)
        for _ in range(100):
            x, xx = normalize_rows(rng.normal(size=(2, 7)))
            y, yy = rng.normal(size=(2, 11))
            y /= np.linalg.norm(y, ord=pstar)
            yy /= np.linalg.norm(yy, ord=pstar)
            a, b = float(x @ xx), float(y @ yy)
            vx = np.dot(y, y) + np.dot(yy, yy) - 2 * a * b
            vy = np.sum((x - xx) ** 2) + np.sum((y - yy) ** 2)
            residual = abs((vy - vx) - 2 * (1 - a) * (1 - b))
            check(residual < 1e-12 and vy >= vx - 1e-12, "Gaussian increment identity")
            maximum = max(maximum, residual)
    return {"cases": 400, "maximum_identity_residual": maximum}


def indefinite_kernel_example() -> dict:
    theta = 2 * np.pi * np.arange(16) / 16
    z = np.column_stack((np.cos(theta), np.sin(theta)))
    eig = np.linalg.eigvalsh(derivative_kernel(z, z, 3.0))
    check(eig[0] < -1e-3, "non-even derivative kernel should exhibit non-PSD example")
    return {"p": 3, "r": 2, "vectors": 16, "minimum_eigenvalue": float(eig[0]),
            "purpose": "Reject the invalid shortcut that every derivative kernel is PSD."}


def noise_small_subset_diagnostic() -> dict:
    rng = np.random.default_rng(2819)
    r, N, qmax = 12, 24, 3
    v = normalize_rows(rng.normal(size=(N, r)))
    minimum = 1.0
    subsets = 0
    for q in range(1, qmax + 1):
        for subset in combinations(range(N), q):
            s2 = float(np.linalg.svd(v[list(subset)].T, compute_uv=False)[-1] ** 2)
            minimum = min(minimum, s2)
            subsets += 1
    check(minimum >= 1 / 64, "small-subset instance meets the 1/64 squared singular-value threshold")
    return {"r": r, "N": N, "qmax_exhaustively_tested": qmax,
            "subsets_tested": subsets, "smallest_squared_singular_value": minimum,
            "meets_1_over_64_on_tested_subsets": minimum >= 1 / 64,
            "scope": "Exhaustive over this finite small instance, in floating point; not the asymptotic noise construction."}


def product_diagnostics(out: Path) -> dict:
    reports = []
    for p, r, seed in ((2.5, 64, 10), (3.0, 64, 11), (3.5, 32, 12), (4.0, 24, 13), (5.0, 12, 14), (6.0, 8, 15)):
        core = sampled_core(r, p, seed)
        check(core.report["selected_target_met"], f"selected rectangular kernel singular value p={p}")
        u = core.u
        rng = np.random.default_rng(700 + seed)
        N, qretain = 25, 3
        v = normalize_rows(rng.normal(size=(N, r)))
        w = np.zeros((len(u), N))
        for j in range(len(u)):
            w[j, rng.choice(N, qretain, replace=False)] = N / qretain
        H = mean_error(u, v, w)
        EH = core.evaluation @ H
        i = int(np.argmax(np.linalg.norm(EH, axis=1)))
        x, y = core.z[i], EH[i] / np.linalg.norm(EH[i])
        h = lambda t: product_cost(u, v, x, t * y, p, w) - product_cost(u, v, x, t * y, p)
        derivative = product_error_derivative(u, v, w, x, y, p)
        direct = p * np.sum((w - 1) * (u @ x)[:, None] * np.abs((u @ x)[:, None]) ** (p - 2) * (v @ y)[None, :]) / N
        check(abs(derivative - direct) < 1e-10, "product derivative identity")
        is_even = p.is_integer() and int(p) % 2 == 0
        q = int(p) if is_even else math.ceil(p) - 1
        t = 0.2
        fd = finite_difference(h, t, q)
        W = product_cost(u, v, np.zeros(r), y, p, w) + product_cost(u, v, np.zeros(r), y, p)
        remainder = 0 if is_even else 2 * t ** (p - 1) * W * sum(abs(float(d)) * j ** p for j, d in enumerate(derivative_stencil(q)))
        check(abs(fd - derivative) <= remainder + 1e-9, "finite difference remainder")
        z = np.r_[x, y]
        z /= np.linalg.norm(z)
        A = explicit_product_rows(u, v, p)
        Q = np.outer(z, z)
        projection_cost = float(np.sum(np.linalg.norm(A @ Q, axis=1) ** p))
        dot_cost = float(np.sum(np.abs(A @ z) ** p))
        check(abs(projection_cost - dot_cost) <= 1e-10 * max(1, dot_cost), "hyperplane reduction")
        padded_A = np.pad(A, ((0, 0), (0, 1)))
        padded_z = np.r_[z, 0]
        check(np.allclose(A @ z, padded_A @ padded_z, atol=1e-14), "zero padding")
        errors = []
        for ell in range(q + 1):
            f = product_cost(u, v, x, ell * t * y, p)
            errors.append(abs(h(ell * t)) / f)
        report = {"core": core.report, "noise_rows": N, "support_per_group": qretain,
                  "derivative_formula": derivative, "direct_derivative": float(direct),
                  "finite_difference": fd, "finite_difference_error": abs(fd - derivative),
                  "proved_remainder_bound_for_this_input": remainder,
                  "maximum_tested_relative_cost_error": max(errors),
                  "hyperplane_identity_residual": abs(projection_cost - dot_cost)}
        reports.append(report)
        if p == 3.0:
            np.savez_compressed(out / "p3_diagnostic_instance.npz", A=A, U=u, V=v,
                                Z=core.z, E=core.evaluation, weights=w, normal=z)
    return {"scope": "Illustrative finite inputs, not a uniform coreset search or large-r existence proof", "cases": reports}


def mub_diagnostics(out: Path) -> dict:
    reports = []
    for h in (1, 2, 3):
        T, forms, meta = real_mub(h)
        r = 4 ** h
        B, M = r // 2 + 1, len(T)
        check(M == B * r, "MUB vector count")
        pair_count = 0
        for i in range(len(forms)):
            check(np.array_equal(forms[i], forms[i].T), "symmetric binary form")
            check(np.all(np.diag(forms[i]) == 0), "alternating binary form")
            for j in range(i):
                check(binary_rank(forms[i] ^ forms[j]) == 2 * h, "nondegenerate form difference")
                pair_count += 1
        Gnum = T @ T.T
        for b in range(B):
            for c in range(B):
                block = Gnum[b*r:(b+1)*r, c*r:(c+1)*r]
                if b == c:
                    check(np.array_equal(block, r * np.eye(r, dtype=np.int64)), "within-basis Gram")
                else:
                    check(np.all(block ** 2 == r), "mutual unbiasedness")
        identity = (r ** 3 - r ** 2) * np.eye(M, dtype=np.int64) + r * Gnum
        check(np.array_equal(Gnum ** 3, identity), "exact cubic kernel identity")
        check(np.array_equal(T.T @ T, B * r * np.eye(r, dtype=np.int64)), "tight frame identity")
        rng = np.random.default_rng(300 + h)
        for _ in range(20):
            x = rng.integers(-3, 4, size=r, dtype=np.int64)
            lhs = int(np.sum((T @ x) ** 4))
            rhs = (3 * r ** 2 * int(x @ x) ** 2) // 2
            check(lhs == rhs, "exact integer fourth moment")
        U = T / math.sqrt(r)
        w = np.zeros(M * r)
        w[rng.permutation(M * r)[:M * r // 2]] = 2
        w = w.reshape(M, r)
        witness = quartic_witness(U, w)
        check(witness["best"]["relative_error"] >= witness["guaranteed_witness_error"] - 1e-12, "quartic witness lower estimate")
        check(witness["best"]["relative_error"] > witness["target_epsilon"], "quartic explicit violation")
        if r <= 16:
            delta = witness["delta"]
            A = np.concatenate((np.repeat(U, r, axis=0), delta * np.tile(np.eye(r), (M, 1))), axis=1) / r ** 0.25
            z = np.asarray(witness["best"]["normal"])
            f = float(np.sum((A @ z) ** 4))
            fw = float(np.sum(w.ravel() * (A @ z) ** 4))
            rel = abs(fw - f) / f
            check(abs(rel - witness["best"]["relative_error"]) < 1e-12, "materialized quartic witness")
            np.savez_compressed(out / f"quartic_r{r}.npz", A=A, weights=w.ravel(), normal=z, integer_core=T)
        reports.append({**meta, "M": M, "binary_form_pairs": pair_count,
                        "integer_gram_blocks_checked": B * B,
                        "integer_fourth_moment_trials": 20,
                        "witness": witness})
    return {"scope": "Exact integer identities plus floating-point witnesses for specific weights", "cases": reports}


def exponent_separations() -> dict:
    result = []
    for p in (Fraction(201,100), Fraction(5,2), Fraction(3), Fraction(4), Fraction(5), Fraction(8), Fraction(20)):
        a = min(p - 2, Fraction(1)) / 8
        beta = 2 - 2 / p
        d1 = a * (beta - 1)
        d2 = p / 2 - 1 - a * (2 - beta)
        check(d1 > 0 and d2 > 0 and a * beta < 1, "polynomial separation")
        result.append({"p": str(p), "a": str(a), "universal_beta": str(beta),
                       "gap_to_first_term": str(d1), "gap_to_second_term": str(d2)})
    return {"arithmetic": "exact rational", "cases": result}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("results"))
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    start = time.perf_counter()
    result = {"seed_policy": "fixed seed in each test", "python": platform.python_version(),
              "numpy": np.__version__, "scipy": scipy.__version__, "mpmath": mp.__version__,
              "scope": "Finite verification is supplementary; see manuscript for universal proofs."}
    suites = [("exact_stencils", exact_stencils),
              ("exact_even_extraction", exact_even_extraction),
              ("taylor_diagnostics", taylor_diagnostics),
              ("gaussian_increment_identity", gaussian_increment_identity),
              ("indefinite_kernel_example", indefinite_kernel_example),
              ("noise_small_subset_diagnostic", noise_small_subset_diagnostic),
              ("product_diagnostics", lambda: product_diagnostics(args.output)),
              ("mub_diagnostics", lambda: mub_diagnostics(args.output)),
              ("exponent_separations", exponent_separations)]
    for name, fun in suites:
        result[name] = fun()
        print(f"PASS {name}", flush=True)
    result["assertions_passed"] = CHECKS
    result["elapsed_seconds"] = time.perf_counter() - start
    result["status"] = "PASS"
    target = args.output / "verification.json"
    target.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(f"PASS all {CHECKS} checks in {result['elapsed_seconds']:.3f} seconds")
    print(f"Results: {target}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
