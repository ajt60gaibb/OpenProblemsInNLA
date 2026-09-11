#!/usr/bin/env python3
"""Exact diagnostic checks for TR-13's uniform Koszul certificate; restored."""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp


def koszul(M: list[sp.Matrix]) -> sp.Matrix:
    a = M[0].rows
    Z = sp.zeros(a)
    return sp.BlockMatrix([[-M[1], M[0], Z],
                           [-M[2], Z, M[0]],
                           [Z, -M[2], M[1]]]).as_explicit()


def check_case(m: int, n: int, full: bool) -> dict:
    if m < 3 or m % 2 != 1 or n < 3:
        raise ValueError("Expected odd m >= 3 and n >= 3")
    k, ell = (m-1)//2, n-1
    a, s, r = k*ell+1, ell//2, (m*ell+2)//2
    h = [0]*(m*ell+1)
    h[a-1] = h[2*a+s-1] = 1
    M = [sp.Matrix(a, a, lambda i, j, off=off: h[i+j+off])
         for off in (0, s, 2*s)]
    J = sp.Matrix(a, a, lambda i, j: int(i+j == a-1))
    L = sp.Matrix(a, a, lambda i, j: int(i == j+1))
    E = sp.zeros(a)
    for i in range(s):
        E[i, a-s+i] = 1
    assert M[0] == J and J*J == sp.eye(a)
    B, C = J*M[1], J*M[2]
    assert B == L**s
    assert C == L**(2*s)+E
    comm = C*B-B*C
    expected = sp.zeros(a)
    for i in range(s):
        expected[i, a-2*s+i] = 1
        expected[s+i, a-s+i] = -1
    assert comm == expected
    minor = comm[:2*s, a-2*s:a]
    assert minor == sp.diag(sp.eye(s), -sp.eye(s))
    assert minor.det() == (-1)**s
    assert comm.rank() == 2*s
    assert a+s == r
    full_rank = None
    if full:
        full_rank = int(koszul(M).rank())
        assert full_rank == 2*r
    return {"m": m, "n": n, "a": a, "s": s,
            "spike_indices": [a-1, 2*a+s-1],
            "commutator_rank": 2*s, "minor_determinant": (-1)**s,
            "full_koszul_rank": full_rank, "lower_bound": r}


def main() -> None:
    cases = [check_case(m, n, full=(m <= 7 and n <= 6))
             for m in (3, 5, 7, 9, 11) for n in range(3, 12)]
    binaries = []
    for m in range(3, 20, 2):
        k = (m-1)//2
        a = k+1
        h = [int(j == k) for j in range(m+1)]
        F = sp.Matrix(a, a+1, lambda i, j: h[i+j])
        assert F.rank() == a
        assert abs(F[:, :a].det()) == 1
        binaries.append({"m": m, "n": 2, "flattening_rank": a})
    rank_one_checks = []
    for a in (2, 3, 4, 5):
        u = sp.Matrix([j+1 for j in range(a)])
        v = sp.Matrix([(-1)**j*(j+2) for j in range(a)])
        for c in ((1, 2, 3), (0, 0, 1), (0, 0, 0)):
            rank = int(koszul([cj*u*v.T for cj in c]).rank())
            assert rank <= 2
            rank_one_checks.append({"a": a, "c": c, "koszul_rank": rank})
    result = {"target": "TR-13", "arithmetic": "exact integer / rational",
              "cases": cases, "binary_cases": binaries,
              "rank_one_checks": rank_one_checks, "status": "PASS",
              "scope": "Diagnostic grid, not a proof by sampling."}
    out = Path(__file__).resolve().parents[1] / "evidence" / "TR-13.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(f"TR-13: PASS; {len(cases)} shift certificates, "
          f"{len(binaries)} binary cases, {len(rank_one_checks)} rank-one checks")


if __name__ == "__main__":
    main()
