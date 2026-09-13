#!/usr/bin/env python3
"""Exact, auxiliary checks for the PF-04 proposed proof.

Python 3.10+; standard library only. These finite combinatorial and rational
arithmetic checks do NOT formally verify the continuous mathematical proof.
Run: python3 verification/verify.py --output verification/results.json
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product
import json
from pathlib import Path
import random
import sys

N = 6
VERTICES = tuple(range(N))
ALL_EDGES = tuple(combinations(VERTICES, 2))
PAIRS = ((0, 1), (2, 3), (4, 5))
MISSING = frozenset(PAIRS)
O_EDGES = tuple(e for e in ALL_EDGES if e not in MISSING)
TRIANGLES = tuple(tuple(t) for t in product(*PAIRS))
FULL = (1 << N) - 1


def graph(edges: tuple[tuple[int, int], ...], mask: int) -> tuple[int, ...]:
    a = [0] * N
    for k, (i, j) in enumerate(edges):
        if mask & (1 << k):
            a[i] |= 1 << j
            a[j] |= 1 << i
    return tuple(a)


def dominated(a: tuple[int, ...]) -> list[tuple[int, int]]:
    """Return (i,j) with closed N[j] contained in closed N[i], i != j."""
    closed = tuple(a[i] | (1 << i) for i in VERTICES)
    return [(i, j) for i in VERTICES for j in VERTICES
            if i != j and (closed[j] & ~closed[i]) == 0]


def components(a: tuple[int, ...]) -> list[list[int]]:
    unseen = set(VERTICES)
    ans: list[list[int]] = []
    while unseen:
        root = min(unseen)
        unseen.remove(root)
        stack, comp = [root], [root]
        while stack:
            v = stack.pop()
            for w in tuple(unseen):
                if a[v] & (1 << w):
                    unseen.remove(w)
                    stack.append(w)
                    comp.append(w)
        ans.append(sorted(comp))
    return ans


def terminal_type(a: tuple[int, ...]) -> str:
    h = tuple((FULL ^ (1 << i)) & ~a[i] for i in VERTICES)
    parts = components(h)
    sizes = sorted(map(len, parts))
    if sizes == [2, 2, 2] and all(x.bit_count() == 1 for x in h):
        return "octahedron"
    if sizes == [3, 3] and all(x.bit_count() == 2 for x in h):
        return "K3,3"
    if sizes == [6] and all(x.bit_count() == 2 for x in h):
        return "triangular_prism"
    raise AssertionError(f"Unexpected terminal graph: adjacency={a}")


def verify_six_vertex_graphs() -> dict:
    counts: Counter[str] = Counter()
    dominated_pairs = 0
    for mask in range(1 << len(ALL_EDGES)):
        a = graph(ALL_EDGES, mask)
        pairs = dominated(a)
        dominated_pairs += len(pairs)
        for i, j in pairs:
            # The shear of row/column i by row/column j cannot create a nonedge.
            assert a[i] & (1 << j)
            for k in VERTICES:
                if k != i and not (a[i] & (1 << k)):
                    assert k != j and not (a[j] & (1 << k))
        if min(x.bit_count() for x in a) >= 3 and not pairs:
            assert len(components(a)) == 1
            counts[terminal_type(a)] += 1
    expected = {"K3,3": 10, "triangular_prism": 60, "octahedron": 15}
    assert dict(counts) == expected, counts
    return {"graphs_checked": 1 << len(ALL_EDGES),
            "domination_pairs_checked": dominated_pairs,
            "terminal_labelled_counts": dict(sorted(counts.items())),
            "total_terminal_graphs": sum(counts.values())}


def verify_octahedral_subgraphs() -> dict:
    counts: Counter[str] = Counter()
    full_mask = (1 << len(O_EDGES)) - 1
    for mask in range(full_mask + 1):
        a = graph(O_EDGES, mask)
        if min(x.bit_count() for x in a) >= 3 and not dominated(a):
            kind = terminal_type(a)
            counts[kind] += 1
            if mask < full_mask:
                assert kind == "triangular_prism"
            else:
                assert kind == "octahedron"
    # Check directly that no labelled K3,3 embeds in the octahedron.
    allowed = set(O_EDGES)
    embeddings = 0
    for left in combinations(VERTICES, 3):
        if 0 not in left:  # quotient by interchanging the two parts
            continue
        right = set(VERTICES) - set(left)
        cross = {tuple(sorted((i, j))) for i in left for j in right}
        embeddings += int(cross <= allowed)
    assert embeddings == 0
    return {"subgraphs_checked": full_mask + 1,
            "proper_subgraphs_checked": full_mask,
            "terminal_labelled_counts": dict(sorted(counts.items())),
            "K3,3_embeddings": embeddings}


def verify_octahedral_zero_counting() -> dict:
    edge_id = {e: k for k, e in enumerate(O_EDGES)}
    face_edges = [tuple(edge_id[e] for e in combinations(t, 2)) for t in TRIANGLES]
    incidence = Counter(k for face in face_edges for k in face)
    assert len(TRIANGLES) == 8 and all(incidence[k] == 2 for k in range(12))
    eligible = 0
    bound_hist: Counter[int] = Counter()
    edge_hist: Counter[int] = Counter()
    max_degree = 0
    for mask in range(1 << len(O_EDGES)):
        selected = {k for k in range(12) if mask & (1 << k)}
        hits = [tuple(k for k in face if k in selected) for face in face_edges]
        if any(len(hit) == 3 for hit in hits):
            continue  # H must be triangle-free.
        eligible += 1
        h = len(selected)
        c = sum(bool(hit) for hit in hits)
        j_adj = {k: set() for k in selected}
        for hit in hits:
            if len(hit) == 2:
                p, q = hit
                j_adj[p].add(q)
                j_adj[q].add(p)
        degree = max((len(a) for a in j_adj.values()), default=0)
        assert degree <= 2
        assert sum(map(len, hits)) == 2 * h
        assert h <= c
        assert h + (8 - c) <= 8
        max_degree = max(max_degree, degree)
        bound_hist[h + 8 - c] += 1
        edge_hist[h] += 1
    return {"edge_subsets_checked": 4096,
            "triangle_free_H_checked": eligible,
            "triangle_count": 8,
            "incidences_per_edge": 2,
            "maximum_auxiliary_degree": max_degree,
            "h_plus_empty_triangles_histogram": dict(sorted(bound_hist.items())),
            "triangle_free_edge_count_histogram": dict(sorted(edge_hist.items()))}


Matrix = list[list[Fraction]]


def fm(a: list[list[int | Fraction]]) -> Matrix:
    return [[Fraction(x) for x in row] for row in a]


def transpose(a: Matrix) -> Matrix:
    return [list(row) for row in zip(*a)]


def mm(a: Matrix, b: Matrix) -> Matrix:
    assert len(a[0]) == len(b)
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), Fraction(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def add(a: Matrix, b: Matrix) -> Matrix:
    return [[x + y for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def determinant(a: Matrix) -> Fraction:
    b = [row[:] for row in a]
    n = len(b)
    assert all(len(row) == n for row in b)
    result = Fraction(1)
    for k in range(n):
        p = next((i for i in range(k, n) if b[i][k]), None)
        if p is None:
            return Fraction(0)
        if p != k:
            b[p], b[k] = b[k], b[p]
            result = -result
        pivot = b[k][k]
        result *= pivot
        for i in range(k + 1, n):
            ratio = b[i][k] / pivot
            for j in range(k + 1, n):
                b[i][j] -= ratio * b[k][j]
            b[i][k] = Fraction(0)
    return result


def inverse(a: Matrix) -> Matrix:
    n = len(a)
    b = [a[i][:] + [Fraction(i == j) for j in range(n)] for i in range(n)]
    for k in range(n):
        p = next((i for i in range(k, n) if b[i][k]), None)
        if p is None:
            raise ValueError("Singular matrix")
        b[p], b[k] = b[k], b[p]
        pivot = b[k][k]
        b[k] = [x / pivot for x in b[k]]
        for i in range(n):
            if i != k:
                ratio = b[i][k]
                b[i] = [x - ratio * y for x, y in zip(b[i], b[k])]
    return [row[n:] for row in b]


def rank(a: Matrix) -> int:
    b = [row[:] for row in a]
    r = 0
    for c in range(len(b[0])):
        p = next((i for i in range(r, len(b)) if b[i][c]), None)
        if p is None:
            continue
        b[p], b[r] = b[r], b[p]
        pivot = b[r][c]
        b[r] = [x / pivot for x in b[r]]
        for i in range(r + 1, len(b)):
            ratio = b[i][c]
            b[i] = [x - ratio * y for x, y in zip(b[i], b[r])]
        r += 1
        if r == len(b):
            break
    return r


def to_ints(a: Matrix) -> list[list[int]]:
    assert all(x.denominator == 1 for row in a for x in row)
    return [[int(x) for x in row] for row in a]


def verify_witnesses() -> dict:
    b = fm([[0] * 9 for _ in VERTICES])
    for k, (i, j) in enumerate(product(range(3), range(3, 6))):
        b[i][k] = Fraction(1)
        b[j][k] = Fraction(2 if (i, j) == (0, 3) else 1)
    a = mm(b, transpose(b))
    assert determinant(a) == 36 and rank(b) == 6
    expected_edges = {tuple(sorted((i, j))) for i in range(3) for j in range(3, 6)}
    actual_edges = {e for e in ALL_EDGES if a[e[0]][e[1]]}
    assert expected_edges == actual_edges
    assert all(not all(e in actual_edges for e in combinations(t, 2))
               for t in combinations(VERTICES, 3))
    assert len(actual_edges) == 9
    # Triangle-free support gives at least one distinct column per edge.
    # The displayed nonnegative factor has exactly nine columns.

    w = fm([[0] * 8 for _ in VERTICES])
    for k, (i, j, ell) in enumerate(TRIANGLES):
        x, y = 1, (2 if k == 0 else 1)
        w[i][k], w[j][k], w[ell][k] = map(Fraction, (x + y, x, y))
    r = mm(w, transpose(w))
    v = fm([[1], [0], [1], [0], [1], [0]])
    q = fm([[1], [1], [-1], [-1], [-1], [-1]])
    p = add(r, mm(v, transpose(v)))
    assert rank(r) == 5 and determinant(p) == 128
    assert mm(r, q) == fm([[0]] * 6)
    assert {e for e in ALL_EDGES if r[e[0]][e[1]]} == set(O_EDGES)
    minus_q = [[-x] for [x] in q]
    assert mm(p, minus_q) == v
    assert mm(transpose(v), minus_q) == [[Fraction(1)]]
    assert all(row[0] != 0 for row in minus_q)
    return {
        "sharp_cp_rank_nine_witness": {
            "B": to_ints(b), "A": to_ints(a), "determinant": 36,
            "ordinary_rank": 6, "cp_rank": 9,
            "lower_bound_reason": "Triangle-free support has nine positive edges; one nonnegative factor column covers at most one edge."
        },
        "singular_octahedral_peeling_endpoint": {
            "W": to_ints(w), "R": to_ints(r), "v": to_ints(v), "q": to_ints(q),
            "rank_R": 5, "det_R_plus_vvT": 128,
            "A_inverse_v": to_ints(minus_q), "peeling_endpoint": "1",
            "note": "R has an explicit eight-column factor. No minimal cp-rank is asserted for this octahedral example."
        }
    }


def verify_cross_block_identity() -> dict:
    positions = {(0, 1): 0, (0, 2): 1, (1, 0): 2,
                 (1, 2): 3, (2, 0): 4, (2, 1): 5}
    terms: Counter[tuple[int, ...]] = Counter()
    for p in permutations(range(3)):
        if any(i == p[i] for i in range(3)):
            continue
        inversions = sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3))
        monomial = tuple(sorted(positions[(i, p[i])] for i in range(3)))
        terms[monomial] += (-1) ** inversions
    assert dict(terms) == {(0, 3, 4): 1, (1, 2, 5): 1}
    return {"matrix": "[[0,a,b],[c,0,d],[e,f,0]]",
            "determinant": "a*d*e + b*c*f",
            "all_nonzero_terms_positive": True}


def verify_thirteen_vector_examples(trials: int = 64) -> dict:
    rng = random.Random(60409)
    choices: Counter[int] = Counter()
    for _ in range(trials):
        # I ensures positive definiteness. All eight positive triangle columns
        # ensure the exact octahedral support. All operations below are exact.
        columns: list[list[int]] = [[int(i == j) for i in VERTICES] for j in VERTICES]
        for t in TRIANGLES:
            col = [0] * 6
            for i in t:
                col[i] = rng.randrange(1, 6)
            columns.append(col)
        b = transpose(fm(columns))
        a = mm(b, transpose(b))
        ai = inverse(a)
        target = (0, 2, 4)
        opposite = (1, 3, 5)
        cross = [[a[i][j] for j in opposite] for i in target]
        assert determinant(cross) > 0
        assert all(any(ai[i][j] != 0 for j in target) for i in VERTICES)
        chosen = None
        for ell in range(1, 14):
            v = fm([[1], [0], [ell], [0], [ell * ell], [0]])
            q = mm(ai, v)
            if all(row[0] for row in q):
                chosen = ell
                break
        assert chosen is not None
        choices[chosen] += 1
    return {"exact_rational_examples": trials, "seed": 60409,
            "chosen_integer_histogram": dict(sorted(choices.items())),
            "scope": "Examples only; the universal 13-vector statement is proved in the manuscript."}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write the JSON report to this path.")
    args = parser.parse_args()
    try:
        report = {
            "status": "PASS",
            "verification_scope": "Finite exact checks, not formal verification of the entire proof.",
            "six_vertex_graphs": verify_six_vertex_graphs(),
            "octahedral_subgraphs": verify_octahedral_subgraphs(),
            "octahedral_zero_counting": verify_octahedral_zero_counting(),
            "cross_block_determinant": verify_cross_block_identity(),
            "witnesses": verify_witnesses(),
            "thirteen_vector_examples": verify_thirteen_vector_examples(),
        }
    except (AssertionError, ValueError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    text = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
