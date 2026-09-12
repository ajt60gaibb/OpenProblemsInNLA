"""Reproducible floating-point illustrations, NOT a proof or timing claim.

Test-matrix construction and diagnostic SVDs are outside the solver. The
``numpy`` floor option is a prototype shortcut; the proof and exact tests
explicitly implement floors by comparisons. Run from any working directory.
"""
from __future__ import annotations
from dataclasses import asdict
from pathlib import Path
import csv
import json
import platform
import sys
import numpy as np
from solver import solve, stochastic_quantize
from weighted_matvec import PatternCatalogue, WeightedMatvec

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "verification"


def orthogonal(n, rng):
    q, r = np.linalg.qr(rng.standard_normal((n, n)))
    signs = np.where(np.diag(r) >= 0, 1.0, -1.0)
    return q * signs


def rotated(singular_values, rng):
    n = len(singular_values)
    U, V = orthogonal(n, rng), orthogonal(n, rng)
    return (U * np.asarray(singular_values)) @ V.T, U, V


def make_cases():
    rng = np.random.default_rng(20260912)
    cases = [("scalar", np.array([[1.0]]), np.array([2.0]), 0.25),
             ("diagonal_1e-250", np.diag([1., .5, .2, 1e-250]),
              np.array([1., -1., .5, 1.]), 0.25)]
    for n, epsilon in ((8, .4), (16, .25), (32, .1)):
        A, U, _ = rotated(np.ones(n), rng)
        cases.append((f"orthogonal_{n}", A, rng.standard_normal(n), epsilon))
    for n, epsilon in ((16, .25), (32, .1)):
        A, U, _ = rotated(np.linspace(1., .3, n), rng)
        cases.append((f"well_conditioned_{n}", A, rng.standard_normal(n), epsilon))
    for n, epsilon in ((16, .25), (32, .1), (64, .25)):
        spectrum = np.r_[np.linspace(1., .3, n - 1), 1e-14]
        A, U, _ = rotated(spectrum, rng)
        weights = np.ones(n) / np.sqrt(n)
        weights[-1] = 1.
        cases.append((f"small_outlier_{n}", A, U @ weights, epsilon))
    for n, epsilon in ((16, .25), (32, .1), (64, .25)):
        A, U, _ = rotated(np.geomspace(1., 1e-12, n), rng)
        cases.append((f"geometric_spectrum_{n}", A, U @ np.ones(n), epsilon))
    n = 24
    A = np.eye(n) + .99 * np.diag(np.ones(n-1), 1)
    A /= np.linalg.norm(A, 2)
    cases.append(("nonnormal_bidiagonal_24", A, rng.standard_normal(n), .25))
    A, U, _ = rotated(np.r_[np.linspace(1., .2, 8), np.zeros(8)], rng)
    cases.append(("singular_inconsistent_extension_16", A, U[:, -1], .25))
    return cases


def main():
    OUTPUT.mkdir(exist_ok=True)
    cases = make_cases()
    rows = []
    for i, (name, A, b, epsilon) in enumerate(cases):
        result = solve(A, b, epsilon, seed=31000+i,
                       backend="dense", floor_backend="numpy",
                       measure_quantization_norm=True)
        assert not result.truncated
        assert result.certificate_passed
        assert result.quantization_error <= epsilon / 8
        assert result.augmented_relative_residual <= epsilon / 8 * (1+1e-12)
        assert result.backward_error <= 5 * epsilon / 8
        rows.append({
            "case": name, "n": len(b), "epsilon": epsilon,
            "steps": result.steps,
            "theoretical_step_cap": result.theoretical_step_cap,
            "backward_error": result.backward_error,
            "augmented_relative_residual": result.augmented_relative_residual,
            "quantization_error": result.quantization_error,
            "quantization_budget": epsilon/8,
            "certificate_passed": result.certificate_passed,
            "k": result.k, "integer_weight": result.integer_weight,
            "backend": result.backend,
        })
        print(f"{name:38s} n={len(b):3d} steps={result.steps:6d} "
              f"berr={result.backward_error:.6e} eps={epsilon:g}")

    # End-to-end compressed-circuit vs dense evaluation with the same draws.
    comparisons = []
    for case_index in (1, 3, 7, 10, 14):
        name, A, b, epsilon = cases[case_index]
        dense = solve(A, b, epsilon, seed=31000+case_index,
                      backend="dense", floor_backend="numpy")
        compressed = solve(A, b, epsilon, seed=31000+case_index,
                           backend="compressed", floor_backend="numpy")
        relative_difference = float(np.linalg.norm(dense.x-compressed.x)
                                    / np.linalg.norm(dense.x))
        assert relative_difference < 1e-8
        assert compressed.certificate_passed
        comparisons.append({"case": name,
                            "relative_output_difference": relative_difference,
                            "compressed_steps": compressed.steps,
                            "dense_steps": dense.steps,
                            "compressed_backward_error": compressed.backward_error})

    # Exercise actual nontrivial pattern blocks at experimental budgets 2..7.
    rng = np.random.default_rng(1234)
    circuit_checks = []
    for k in range(2, 8):
        n = 37
        Z_array = rng.choice(np.array([-1000, -2, -1, 0, 0, 0, 1, 2, 1000]), (n, n))
        Z = [[int(value) for value in row] for row in Z_array]
        vector = rng.standard_normal(n)
        circuit = WeightedMatvec(Z, k, PatternCatalogue(k))
        observed = circuit.apply_numpy(vector)
        expected = Z_array @ vector
        relative_error = float(np.linalg.norm(observed-expected)
                               / max(np.linalg.norm(expected), 1.0))
        assert relative_error < 1e-12
        circuit_checks.append({"k": k, "relative_difference": relative_error,
                               "pattern_terms": circuit.pattern_count,
                               "heavy_terms": circuit.heavy_count})

    # A finite sample checks implementation, not the universal probability bound.
    rounding_ratios = []
    for n in (4, 16, 32):
        A, _, _ = rotated(np.linspace(1., .1, n), rng)
        for _ in range(100):
            _, Q, _ = stochastic_quantize(A, .25, rng, "numpy")
            rounding_ratios.append(float(np.linalg.norm(Q-A, 2) / (.25/8)))
    assert max(rounding_ratios) < 1
    report = {
        "description": "Finite floating-point illustrations; not a proof or finite-precision guarantee.",
        "python": platform.python_version(), "numpy": np.__version__,
        "cases": rows, "end_to_end_comparisons": comparisons,
        "nontrivial_pattern_comparisons": circuit_checks,
        "rounding_trials": len(rounding_ratios),
        "maximum_observed_rounding_error_over_budget": max(rounding_ratios),
        "all_checks_passed": True,
    }
    (OUTPUT / "experiments.json").write_text(json.dumps(report, indent=2)+"\n")
    with (OUTPUT / "experiments.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print("\nAll numerical checks passed.")
    print(f"Rounding trials: {len(rounding_ratios)}; "
          f"maximum ||Q-A||/(epsilon/8) = {max(rounding_ratios):.6f}")
    print(f"Largest dense/compressed relative output difference: "
          f"{max(r['relative_output_difference'] for r in comparisons):.3e}")


if __name__ == "__main__":
    main()
