#!/usr/bin/env python3
"""TR-04: exact tie-projector certificates and floating-point diagnostics.

Restored from the earlier work, with formatting and output-path cleanup.
The theorem uses exact SVDs and exact equality of singular values. This
implementation uses a tolerance and is NOT a certified bit-complexity
algorithm. No numerical optimizer is used as an oracle for the optimum.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import numpy as np
import sympy as sp


def reconstruct(cores: list[np.ndarray]) -> np.ndarray:
    value = cores[0][0]
    for core in cores[1:]:
        value = np.tensordot(value, core, axes=([-1], [0]))
    return value[..., 0]


def ordinary_tt_svd(tensor: np.ndarray, ranks: tuple[int, ...]) -> np.ndarray:
    shape = tensor.shape
    if len(shape) < 2 or len(ranks) != len(shape)-1 or min(ranks) <= 0:
        raise ValueError("One positive rank bound is needed at each cut.")
    cores: list[np.ndarray] = []
    carry, left_rank = tensor.copy(), 1
    for mode, cap in enumerate(ranks):
        matrix = carry.reshape(left_rank*shape[mode], -1)
        U, singular, Vh = np.linalg.svd(matrix, full_matrices=False)
        kept = min(cap, len(singular))
        cores.append(U[:, :kept].reshape(left_rank, shape[mode], kept))
        carry = singular[:kept, None]*Vh[:kept]
        left_rank = kept
    cores.append(carry.reshape(left_rank, shape[-1], 1))
    return reconstruct(cores)


def first_subspaces(tensor: np.ndarray, cap: int, tolerance: float = 1e-12,
                    tie_rotation: np.ndarray | None = None) -> list[np.ndarray]:
    matrix = tensor.reshape(tensor.shape[0], -1)
    U, singular, _ = np.linalg.svd(matrix, full_matrices=False)
    scale = max(1.0, float(singular[0]))
    numerical_rank = int(np.sum(singular > tolerance*scale))
    if numerical_rank == 0:
        return []
    if numerical_rank <= cap:
        return [U[:, :numerical_rank]]
    boundary = singular[cap-1]
    high = np.flatnonzero(singular > boundary+tolerance*scale)
    equal = np.flatnonzero(np.abs(singular-boundary) <= tolerance*scale)
    H, E = U[:, high], U[:, equal]
    h, t = H.shape[1], E.shape[1]
    selected = cap-h
    if not 1 <= selected <= t:
        raise AssertionError("Inconsistent numerical singular-value grouping.")
    if tie_rotation is not None:
        if tie_rotation.shape != (t, t):
            raise ValueError("Tie rotation has the wrong dimension.")
        assert np.allclose(tie_rotation.T@tie_rotation, np.eye(t), atol=1e-12)
        E = E@tie_rotation
    if selected == t:
        return [np.column_stack((H, E))]
    return [np.column_stack((H, E[:, [(j+offset) % t
                                     for offset in range(selected)]]))
            for j in range(t)]


def tie_aware_tt_svd(tensor: np.ndarray, ranks: tuple[int, ...],
                     tie_rotation: np.ndarray | None = None) -> tuple:
    if tensor.ndim < 3 or len(ranks) != tensor.ndim-1 or min(ranks) <= 0:
        raise ValueError("Expected order >= 3 with positive rank bounds.")
    subspaces = first_subspaces(tensor, ranks[0], tie_rotation=tie_rotation)
    if not subspaces:
        return np.zeros_like(tensor), []
    candidates, errors = [], []
    for U in subspaces:
        k = U.shape[1]
        compressed = (U.T@tensor.reshape(tensor.shape[0], -1)).reshape(
            (k*tensor.shape[1],)+tensor.shape[2:])
        completion = ordinary_tt_svd(compressed, ranks[1:])
        candidate = (U@completion.reshape(k, -1)).reshape(tensor.shape)
        candidates.append(candidate)
        errors.append(float(np.linalg.norm(tensor-candidate)**2))
    return candidates[int(np.argmin(errors))], errors


def check_ranks(tensor: np.ndarray, ranks: tuple[int, ...]) -> list[int]:
    actual = []
    for cut, cap in enumerate(ranks, start=1):
        matrix = tensor.reshape(int(np.prod(tensor.shape[:cut])), -1)
        singular = np.linalg.svd(matrix, compute_uv=False)
        tolerance = 2e-10*max(1.0, float(singular[0]))
        value = int(np.sum(singular > tolerance))
        assert value <= cap, (cut, value, cap)
        actual.append(value)
    return actual


def cut_lower_bounds(tensor: np.ndarray, ranks: tuple[int, ...]) -> list[float]:
    bounds = []
    for cut, cap in enumerate(ranks, start=1):
        singular = np.linalg.svd(
            tensor.reshape(int(np.prod(tensor.shape[:cut])), -1), compute_uv=False)
        bounds.append(float(np.sum(singular[cap:]**2)))
    return bounds


def exact_tests() -> dict:
    averaging = []
    for t in range(2, 15):
        for selected in range(1, t):
            projectors = []
            for start in range(t):
                included = {(start+j) % t for j in range(selected)}
                projectors.append(sp.diag(*[int(i in included) for i in range(t)]))
            total = sum(projectors, sp.zeros(t))
            assert total == selected*sp.eye(t)
            averaging.append({"tie_dimension": t, "selected": selected})
    A = sp.zeros(3, 6)
    A[0, 0], A[1, 2], A[2, 5] = 2, 1, 1
    rotations = [(sp.Integer(1), sp.Integer(0)),
                 (sp.Rational(3, 5), sp.Rational(4, 5)),
                 (sp.sqrt(2)/2, sp.sqrt(2)/2)]
    rotated = []
    for cosine, sine in rotations:
        assert sp.simplify(cosine**2+sine**2) == 1
        errors = []
        for w in (sp.Matrix([0, cosine, sine]), sp.Matrix([0, -sine, cosine])):
            e0 = sp.Matrix([1, 0, 0])
            P = e0*e0.T+w*w.T
            candidate = P*A
            # The remaining rank-one SVD keeps f_1: norm >= 2 vs norm <= 1.
            for col in (1, 3, 5):
                candidate[:, col] = sp.zeros(3, 1)
            errors.append(sp.simplify(sum(entry**2 for entry in A-candidate)))
        assert min(errors) <= sp.Rational(3, 2) < 2
        rotated.append({"cosine": str(cosine), "sine": str(sine),
                        "candidate_squared_errors": list(map(str, errors)),
                        "optimum_squared_error": "1"})
    approaching = []
    for denominator in (2, 5, 10, 100, 1000, 10000):
        gamma = 1+sp.Rational(1, denominator)
        ratio = sp.simplify((1+gamma**2)/gamma**2)
        assert ratio < 2
        approaching.append({"gamma": str(gamma), "ratio": str(ratio),
                            "ratio_decimal": float(ratio)})
    return {"projector_averaging_cases": averaging, "rotated_tie_cases": rotated,
            "fixed_format_ratios_approaching_two": approaching}


def main(output: Path) -> None:
    result = exact_tests()
    rng = np.random.default_rng(4042026)
    formats = [((3, 3, 2), (2, 1)), ((3, 4, 3), (2, 2)),
               ((2, 3, 2, 2), (1, 2, 1)), ((3, 2, 3, 2), (2, 2, 1)),
               ((2, 2, 2, 2, 2), (1, 2, 2, 1))]
    random_records = []
    for shape, ranks in formats:
        for trial in range(8):
            tensor = rng.standard_normal(shape)
            approximation, candidate_errors = tie_aware_tt_svd(tensor, ranks)
            actual = check_ranks(approximation, ranks)
            error = float(np.linalg.norm(tensor-approximation)**2)
            lower = max(cut_lower_bounds(tensor, ranks))
            # Max-cut tail <= E_*; this is not a numerical estimate of E_*.
            assert error < (len(shape)-1)*lower
            random_records.append({"shape": shape, "ranks": ranks, "trial": trial,
                                   "output_cut_ranks": actual, "squared_error": error,
                                   "optimum_lower_bound_numerical": lower,
                                   "candidate_count": len(candidate_errors)})
    reconstruction = []
    for shape, ranks in formats:
        tensor = ordinary_tt_svd(rng.standard_normal(shape), ranks)
        recovered, _ = tie_aware_tt_svd(tensor, ranks)
        relative = float(np.linalg.norm(recovered-tensor)/max(1.0, np.linalg.norm(tensor)))
        assert relative < 2e-12
        reconstruction.append({"shape": shape, "ranks": ranks, "relative_error": relative})
    zero, _ = tie_aware_tt_svd(np.zeros((2, 2, 2)), (1, 1))
    assert np.count_nonzero(zero) == 0
    tie_records = []
    A = np.zeros((3, 3, 2))
    A[0, 0, 0], A[1, 1, 0], A[2, 2, 1] = 2.0, 1.0, 1.0
    for angle in (0.0, 0.2, 0.5, np.pi/4):
        c, s = np.cos(angle), np.sin(angle)
        rotation = np.array([[c, -s], [s, c]])
        approximation, errors = tie_aware_tt_svd(A, (2, 1), rotation)
        error = float(np.linalg.norm(A-approximation)**2)
        assert error <= 1.5+1e-12 and len(errors) == 2
        check_ranks(approximation, (2, 1))
        tie_records.append({"rotation_angle": float(angle),
                            "candidate_squared_errors": errors,
                            "optimum_squared_error": 1.0})
    result.update({"problem": "TR-04", "status": "PASS",
                   "scope": "Exact averaging/examples and tolerance-based diagnostics. "
                            "No uniform-factor improvement or certified bit-complexity claim.",
                   "random_cases": random_records,
                   "feasible_reconstruction_cases": reconstruction,
                   "numerical_rotated_ties": tie_records,
                   "numpy_version": np.__version__, "sympy_version": sp.__version__})
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(f"TR-04: PASS; {len(result['projector_averaging_cases'])} exact averaging cases, "
          f"{len(random_records)} random tensors, rotated ties and reconstruction tests")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1]/"evidence/TR-04.json")
    main(parser.parse_args().output)
