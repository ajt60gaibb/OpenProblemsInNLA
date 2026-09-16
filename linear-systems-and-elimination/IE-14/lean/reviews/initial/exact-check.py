#!/usr/bin/env python3
"""Independent exact diagnostics for IE-14's actual current-last-row pivot path.

Standard-library Fraction arithmetic only.  This is a finite diagnostic, not a
proof of the all-size witness, universal upper bound, or Lean statement.
When retained under a checkout, discover the repository from this file's parents.
An external staging copy can use --repo-root PATH.  No repository files change.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path


SOURCE_FILES = (
    "linear-systems-and-elimination/IE-14/README.md",
    "linear-systems-and-elimination/IE-14/problem.tex",
    "linear-systems-and-elimination/IE-14/problem.pdf",
    "references/colbrook-recovered-2026-09-11/manuscripts/IE-14.tex",
    "references/colbrook-recovered-2026-09-11/manuscripts/IE-14.pdf",
    "references/colbrook-recovered-2026-09-11/verification/reviews/IE-14-review.md",
    "references/colbrook-recovered-2026-09-11/README.md",
)
SOURCE_BASE = "d8c38a795876b132c90df8d1be8682d3dcde394c"


def repository_root(explicit: str | None) -> Path:
    if explicit:
        candidates = [Path(explicit).resolve()]
    else:
        candidates = [*Path(__file__).resolve().parents,
                      Path.cwd().resolve(), *Path.cwd().resolve().parents]
    for root in candidates:
        if (root / "problem_ids.json").is_file():
            return root
    raise RuntimeError("No enclosing problem_ids.json; pass --repo-root PATH")


def source_hashes(root: Path) -> dict:
    registry = json.loads((root / "problem_ids.json").read_text())
    assert registry["IE-14"] == SOURCE_FILES[0]
    files = {}
    for relative in SOURCE_FILES:
        content = (root / relative).read_bytes()
        files[relative] = {"bytes": len(content),
                           "sha256": hashlib.sha256(content).hexdigest()}
    return {"problem_id": "IE-14", "published_source_base": SOURCE_BASE,
            "hash_convention": "SHA-256 of the complete unmodified file bytes",
            "files": files}


def fib(n: int) -> int:
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def matmul(A: list[list[Q]], B: list[list[Q]]) -> list[list[Q]]:
    n = len(A)
    return [[sum((A[i][k] * B[k][j] for k in range(n)), Q(0))
             for j in range(n)] for i in range(n)]


def det_independent(A: list[list[Q]]) -> Q:
    """A second elimination routine: first nonzero pivot, unpadded storage.

    It does not use the prescribed GEPP path, labels, L/U determinant formula,
    or maximal-modulus pivots.
    """
    R = [row[:] for row in A]
    determinant = Q(1)
    for k in range(len(R)):
        p = next((i for i in range(k, len(R)) if R[i][k]), None)
        if p is None:
            return Q(0)
        if p != k:
            R[k], R[p] = R[p], R[k]
            determinant = -determinant
        pivot = R[k][k]
        determinant *= pivot
        for i in range(k + 1, len(R)):
            multiplier = R[i][k] / pivot
            for j in range(k + 1, len(R)):
                R[i][j] -= multiplier * R[k][j]
            R[i][k] = Q(0)
    return determinant


def witness(n: int) -> tuple[list[list[Q]], list[list[Q]], list[list[Q]]]:
    """Branch order and zero-based indexing match the draft Definitions.lean."""
    L = [[Q(1) if i == j else Q(-1) if j + 1 == i or j + 2 == i else Q(0)
          for j in range(n)] for i in range(n)]

    def upper_entry(i: int, j: int) -> Q:
        if j + 1 == n:
            return Q(fib(n + 1) + 1 if i == j else fib(i + 2))
        if i == j:
            return Q(1, 2) if i == 1 else Q(1)
        return Q(1, 2) if i == 0 and j == 1 else Q(0)

    U = [[upper_entry(i, j) for j in range(n)] for i in range(n)]
    C = matmul(L, U)
    factor_index = lambda i: 0 if i == 0 else 1 if i + 1 == n else i + 1
    A = [C[factor_index(i)][:] for i in range(n)]
    assert len(set(factor_index(i) for i in range(n))) == n
    assert [row[n - 1] for row in C] == [Q(1), Q(1)] + [Q(0)] * (n - 3) + [Q(1)]
    return L, U, A


def actual_path_diagnostic(n: int) -> dict:
    assert n >= 4
    L, U, A = witness(n)
    allowed = lambda i, j: abs(i - j) <= 1 or (i, j) in ((0, n - 1), (n - 1, 0))
    assert all(allowed(i, j) or A[i][j] == 0 for i in range(n) for j in range(n))
    assert A[0][n - 1] == 1 and A[n - 1][0] == -1
    initial_max = max(abs(entry) for row in A for entry in row)
    assert initial_max == 1
    determinant = det_independent(A)
    bound = Q(fib(n + 1) + 1)
    assert determinant == Q((-1) ** (n - 2), 2) * bound != 0

    # Actual trajectory: no initial row permutation.  A is already the input.
    # Original labels below are OBSERVATIONS only; they never choose the pivot.
    S = [row[:] for row in A]
    original_labels = list(range(n))
    factor_labels = [0] + list(range(2, n)) + [1]
    pivot_rows, pivot_labels, pivot_values, stage_maxima = [], [], [], []
    tie_counts, stage_traces = [], []
    recorded_U = [[Q(0) for _ in range(n)] for _ in range(n)]
    for k in range(n):
        assert all(S[i][j] == 0 for i in range(n) for j in range(n)
                   if k > 0 and (i < k or j < k))
        active_max = max(abs(S[i][j]) for i in range(k, n) for j in range(k, n))
        stage_maxima.append(active_max)
        assert active_max <= bound
        p = k if k == 0 else n - 1  # literal witnessPath, including the final stage
        pivot = S[p][k]
        column_max = max(abs(S[i][k]) for i in range(k, n))
        assert k <= p and pivot != 0 and abs(pivot) == column_max
        assert all(abs(S[i][k] / pivot) <= 1 for i in range(k, n))
        pivot_rows.append(p)
        pivot_labels.append(original_labels[p])
        pivot_values.append(pivot)
        tie_counts.append(sum(abs(S[i][k]) == column_max for i in range(k, n)))

        # Independently check the factor-order residual formula in the physical
        # row ordering, not just the selected pivot column.
        for i in range(k, n):
            assert factor_labels[i] >= k
            for j in range(k, n):
                residual = sum((L[factor_labels[i]][a] * U[a][j]
                                for a in range(k, n)), Q(0))
                assert S[i][j] == residual
        assert factor_labels[p] == k

        if n == 4:
            stage_traces.append({"stage_zero_based": k, "pivot_row_zero_based": p,
                                 "original_labels_one_based": [i + 1 for i in original_labels],
                                 "active_matrix": [row[k:] for row in S[k:]],
                                 "pivot": pivot, "active_max": active_max})

        # Equiv.swap k p acts on rows.  Then create the newly padded Schur block.
        B = [row[:] for row in S]
        B[k], B[p] = B[p], B[k]
        original_labels[k], original_labels[p] = original_labels[p], original_labels[k]
        factor_labels[k], factor_labels[p] = factor_labels[p], factor_labels[k]
        for j in range(k, n):
            recorded_U[k][j] = B[k][j]
        S = [[B[i][j] - (B[i][k] / B[k][k]) * B[k][j]
              if k < i and k < j else Q(0)
              for j in range(n)] for i in range(n)]

    assert pivot_labels == [0, n - 1] + list(range(1, n - 1))
    assert pivot_rows == [0] + [n - 1] * (n - 1)
    assert pivot_values == [Q(1), Q(1, 2)] + [Q(1)] * (n - 3) + [bound]
    assert recorded_U == U
    assert max(stage_maxima) / initial_max == bound
    assert stage_maxima[-1] == bound
    assert all(entry == 0 for row in S for entry in row)
    result = {"n": n, "passed": True, "initial_max": initial_max,
              "corners": [A[0][n - 1], A[n - 1][0]],
              "independent_determinant": determinant, "growth": bound,
              "pivot_rows_zero_based": pivot_rows,
              "pivot_original_labels_one_based": [i + 1 for i in pivot_labels],
              "pivot_values": pivot_values, "stage_maxima": stage_maxima,
              "maximal_tie_counts": tie_counts,
              "all_active_factor_residual_entries_checked": True,
              "recorded_pivot_rows_equal_U": True}
    if n == 4:
        result.update({"L": L, "U": U, "input_A": A, "stage_traces": stage_traces})
    return result


def json_fraction(value):
    if isinstance(value, Q):
        return str(value)
    raise TypeError(f"Cannot encode {type(value)}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root")
    parser.add_argument("--source-hashes-output", type=Path)
    args = parser.parse_args()
    root = repository_root(args.repo_root)
    hashes = source_hashes(root)
    if args.source_hashes_output:
        args.source_hashes_output.write_text(json.dumps(hashes, indent=2, sort_keys=True) + "\n")
    cases = [actual_path_diagnostic(n) for n in range(4, 31)]
    result = {"problem_id": "IE-14", "diagnostic_only": True,
              "arithmetic": "Python standard-library fractions.Fraction; no floating point",
              "pivot_rule": "k=0: p=k; k>0: p=n-1; no initial permutation",
              "source_files": hashes, "case_count": len(cases), "all_passed": True,
              "limitations": "Finite rational witness checks; not an all-size or all-complex upper proof.",
              "cases": cases}
    print(json.dumps(result, default=json_fraction, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
