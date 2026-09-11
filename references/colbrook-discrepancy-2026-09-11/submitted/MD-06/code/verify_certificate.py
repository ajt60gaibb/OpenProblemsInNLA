#!/usr/bin/env python3
"""Exact rational existence certificates for nonsynchronized Kuramoto minima.

Usage (from the MD-06 directory):
    python code/verify_certificate.py data/cubic20_certificate.json

Acceptance uses only fractions.Fraction arithmetic. Floating-point numbers in
output are descriptive. The rational input phases need not be stationary: the
small-gradient lemma in the manuscript proves a nearby exact local minimum.
"""
from __future__ import annotations

import argparse
from collections import deque
from fractions import Fraction as F
import json
from pathlib import Path
from typing import Any


def trig_intervals(x: F, terms: int = 40) -> tuple[tuple[F, F], tuple[F, F]]:
    """Taylor/Lagrange enclosures, valid for every real rational x.

    Include the next zero Taylor coefficient when applying the remainder bound.
    All derivatives of sine and cosine have absolute value at most one.
    """
    if terms < 1:
        raise ValueError("terms must be positive")
    x2 = x*x
    s = st = x
    c = ct = F(1)
    for j in range(1, terms + 1):
        st *= -x2 / ((2*j)*(2*j+1))
        ct *= -x2 / ((2*j-1)*(2*j))
        s += st
        c += ct
    sr = abs(st*x2 / ((2*terms+2)*(2*terms+3)))
    cr = abs(ct*x2 / ((2*terms+1)*(2*terms+2)))
    return (s-sr, s+sr), (c-cr, c+cr)


def graph_diameter(n: int, edges: list[tuple[int, int]]) -> int:
    """Check simplicity, cubic degree, connectivity; compute diameter exactly."""
    adj: list[list[int]] = [[] for _ in range(n)]
    seen: set[tuple[int, int]] = set()
    for u, v in edges:
        if not (0 <= u < n and 0 <= v < n) or u == v:
            raise ValueError("invalid endpoint or self-loop")
        pair = tuple(sorted((u, v)))
        if pair in seen:
            raise ValueError("repeated undirected edge")
        seen.add(pair)
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != 3 for a in adj):
        raise ValueError("graph is not cubic")
    diameter = 0
    for root in range(n):
        dist = [-1]*n
        dist[root] = 0
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v in adj[u]:
                if dist[v] < 0:
                    dist[v] = dist[u] + 1
                    queue.append(v)
        if min(dist) < 0:
            raise ValueError("graph is disconnected")
        diameter = max(diameter, max(dist))
    return diameter


def verify(path: Path, terms: int = 40) -> dict[str, Any]:
    data = json.loads(path.read_text())
    n, q = data["n"], data["phase_denominator"]
    if not isinstance(n, int) or n < 4 or n % 2:
        raise ValueError("n must be even and at least four")
    if not isinstance(q, int) or q <= 0:
        raise ValueError("phase denominator must be a positive integer")
    nums = data["phase_numerators"]
    if len(nums) != n or not all(isinstance(p, int) for p in nums):
        raise ValueError("invalid rational phase vector")
    phi = [F(p, q) for p in nums]
    edges = [tuple(e) for e in data["edges"]]
    if not all(len(e) == 2 and all(isinstance(v, int) for v in e) for e in edges):
        raise ValueError("invalid edge list")
    diameter = graph_diameter(n, edges)
    c = F(data["cosine_lower_bound"])
    if not 0 < c <= 1:
        raise ValueError("cosine lower bound must be in (0,1]")
    # The manuscript's path argument gives lambda_2(L) >= 2/((n-1)D).
    # We deliberately use the weaker rational bound below.
    gamma = F(1, n*diameter)
    lo, hi = [F(0) for _ in range(n)], [F(0) for _ in range(n)]
    min_cos = F(1)
    witness: tuple[int, int] | None = None
    for u, v in edges:
        delta = phi[u]-phi[v]
        (sl, su), (cl, _cu) = trig_intervals(delta, terms)
        if cl < c:
            raise AssertionError(f"cosine bound not established on edge {(u,v)}")
        min_cos = min(min_cos, cl)
        lo[u] += sl
        hi[u] += su
        lo[v] -= su
        hi[v] -= sl
        # The certified perturbation changes this difference by <=c/2<=1/2.
        # Its new absolute value stays in (0,6), and 2*pi>6.
        if 1 <= abs(delta) <= 5:
            witness = (u, v)
    if witness is None:
        raise AssertionError("no nonsynchronization witness edge")
    g2_upper = sum((max(abs(a), abs(b))**2 for a, b in zip(lo, hi)), F(0))
    threshold2 = c**4 * gamma**2 / 32
    if not g2_upper < threshold2:
        raise AssertionError("small-gradient inequality not established")
    conservative = next((F(1,10**k) for k in range(40,0,-1)
                         if g2_upper < F(1,10**k)), None)
    return {
        "certificate": path.name,
        "status": "PASS: exact rational inequalities establish existence",
        "n": n, "edges": len(edges), "diameter": diameter,
        "cosine_lower_bound": str(c),
        "laplacian_gap_lower_bound": str(gamma),
        "taylor_terms_parameter": terms,
        "nonsynchronized_witness_edge": list(witness),
        "conservative_exact_gradient_squared_upper_bound": str(conservative),
        "required_threshold_squared_exact": str(threshold2),
        "gradient_norm_squared_upper_display": float(g2_upper),
        "required_threshold_squared_display": float(threshold2),
        "squared_margin_factor_display": float(threshold2/g2_upper) if g2_upper else None,
        "minimum_cosine_lower_enclosure_display": float(min_cos),
        "arithmetic_for_acceptance": "fractions.Fraction; no floating-point decisions",
        "conclusion": "A nearby exact nonsynchronized local minimum exists; its Hessian is positive definite modulo common rotation."
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--terms", type=int, default=40)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        result = verify(args.certificate, args.terms)
    except (ValueError, AssertionError, KeyError, TypeError, OSError, json.JSONDecodeError) as exc:
        parser.exit(1, f"FAIL: {exc}\n")
    text = json.dumps(result, indent=2)+"\n"
    print(text, end="")
    if args.output:
        args.output.write_text(text)

if __name__ == "__main__":
    main()
