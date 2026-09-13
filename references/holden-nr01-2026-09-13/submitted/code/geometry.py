"""Finite geometry cover for four-dimensional, eight-facet lifts.

The completeness input is the published count of 39 combinatorial
3-spheres with eight vertices. This module generates 39 pairwise
nonisomorphic spheres by sphere-preserving bistellar moves, then
exhausts generic rank-two projected normal configurations.

All geometric decisions use integer masks and signs, not floating point.
The cover deliberately includes two non-polytopal spheres and other
unrealizable data: over-inclusion is safe for the exclusion argument.
"""
from __future__ import annotations
from collections import deque, Counter
from itertools import permutations, combinations
from typing import Iterable
import numpy as np
from numba import njit


def mask_maps(perms: np.ndarray) -> np.ndarray:
    result = np.zeros((len(perms), 256), dtype=np.uint8)
    for mask in range(1, 256):
        low = mask & -mask
        j = low.bit_length() - 1
        result[:, mask] = result[:, mask ^ low] | (np.uint8(1) << perms[:, j])
    return result


def canonical_sphere(facets: Iterable[int], perms: np.ndarray,
                     maps: np.ndarray) -> tuple[int, ...]:
    facets = tuple(sorted(facets))
    degrees = np.array([sum(bool(f & (1 << i)) for f in facets) for i in range(8)])
    target = np.sort(degrees)
    admissible = np.all(target[perms] == degrees[None, :], axis=1)
    candidates = np.sort(maps[admissible][:, list(facets)], axis=1)
    for j in range(len(facets)):
        candidates = candidates[candidates[:, j] == candidates[:, j].min()]
        if len(candidates) == 1:
            break
    return tuple(map(int, candidates[0]))


def bistellar_neighbors(facets: Iterable[int]):
    """All 2<->3 moves; the new opposite simplex must not already occur."""
    facets = set(facets)
    faces = {s for f in facets for s in range(1, 256) if s & f == s}
    for s in sorted(faces):
        k = s.bit_count()
        if k not in (2, 3):
            continue
        star = [f for f in facets if f & s == s]
        if len(star) != 5 - k:
            continue
        opposite = 0
        for f in star:
            opposite |= f ^ s
        if opposite.bit_count() != 5 - k or opposite in faces:
            continue
        boundary = {opposite ^ (1 << i) for i in range(8) if opposite & (1 << i)}
        if {f ^ s for f in star} != boundary:
            continue
        replacement = {opposite | (s ^ (1 << i)) for i in range(8) if s & (1 << i)}
        yield tuple(sorted(facets.difference(star).union(replacement)))


def enumerate_spheres() -> list[list[int]]:
    """Generate spheres, not arbitrary complexes; use count 39 for completeness."""
    perms = np.array(list(permutations(range(8))), dtype=np.uint8)
    maps = mask_maps(perms)
    facets = {sum(1 << i for i in f) for f in combinations(range(5), 4)}
    # Three stellar subdivisions of tetrahedra, starting at the 4-simplex boundary.
    for vertex in range(5, 8):
        f = min(facets)
        facets.remove(f)
        facets.update((f ^ (1 << j)) | (1 << vertex)
                      for j in range(vertex) if f & (1 << j))
    root = canonical_sphere(facets, perms, maps)
    queue, seen = deque([root]), {root}
    while queue:
        old = queue.popleft()
        for candidate in bistellar_neighbors(old):
            new = canonical_sphere(candidate, perms, maps)
            if new not in seen:
                seen.add(new)
                queue.append(new)
    answer = [list(k) for k in sorted(seen, key=lambda k: (len(k), k))]
    if len(answer) != 39:
        raise AssertionError(f"Published completeness count not met: {len(answer)}")
    for k in answer:
        if len(set(k)) != len(k) or any(f.bit_count() != 4 for f in k):
            raise AssertionError("Invalid tetrahedron list")
        triangles = Counter(f ^ (1 << v) for f in k for v in range(8) if f & (1 << v))
        if set(triangles.values()) != {2}:
            raise AssertionError("Not a closed pseudomanifold")
    return answer


def positive_span_table() -> np.ndarray:
    """Represent normals as sign_i*(1,i); sign_0 is fixed positive.

    A subset positively spans R^2 iff its signs, in slope order, have
    at least two changes. No angular distances enter this criterion.
    """
    good = np.zeros((128, 256), dtype=np.uint8)
    for sigma in range(128):
        signs = [0] + [(sigma >> i) & 1 for i in range(7)]
        for mask in range(256):
            sequence = [signs[i] for i in range(8) if mask & (1 << i)]
            good[sigma, mask] = sum(a != b for a, b in zip(sequence, sequence[1:])) >= 2
    return good


@njit(cache=True)
def _scan_cycles(facets, edge_vertices, triangles, maps, good):
    """Exhaust all 7!*2^7 states for one sphere, with checked output capacity."""
    n = len(facets)
    output = np.zeros((65536, n + 3), np.int64)
    out_count = 0
    adj = np.full((n, 2), -1, np.int64)
    degree = np.zeros(n, np.int64)
    path = np.zeros(n, np.int64)
    maximum_positive = 0
    for ip in range(len(maps)):
        for sigma in range(128):
            count = 0
            for f in facets:
                count += good[sigma, maps[ip, f]]
            maximum_positive = max(maximum_positive, count)
            if count < 17:
                continue
            for i in range(n):
                degree[i] = 0
            for e in range(len(triangles)):
                if good[sigma, maps[ip, triangles[e]]]:
                    a, b = edge_vertices[e]
                    if degree[a] >= 2 or degree[b] >= 2:
                        raise ValueError("Unexpected degree > 2")
                    adj[a, degree[a]] = b
                    adj[b, degree[b]] = a
                    degree[a] += 1
                    degree[b] += 1
            actual_count = 0
            for i in range(n):
                if degree[i] not in (0, 2):
                    raise ValueError("Unexpected degree 1")
                actual_count += degree[i] == 2
            if actual_count != count:
                raise ValueError("Vertex and edge tests disagree")
            first = 0
            while not degree[first]:
                first += 1
            a, previous, length = first, -1, 1
            path[0] = facets[a]
            for _ in range(count):
                b = adj[a, 0] if adj[a, 0] != previous else adj[a, 1]
                if b == first:
                    break
                if length >= n:
                    raise ValueError("Cycle walk did not close")
                path[length] = facets[b]
                length += 1
                previous, a = a, b
            if length != count:
                continue  # Multiple disjoint cycles cannot be a convex shadow.
            if out_count >= len(output):
                raise ValueError("Output capacity exhausted; no truncation allowed")
            output[out_count, 0] = count
            output[out_count, 1] = ip
            output[out_count, 2] = sigma
            output[out_count, 3:count + 3] = path[:count]
            out_count += 1
    return output[:out_count], maximum_positive


def canonical_cycle(cycle: Iterable[int]) -> tuple[int, ...]:
    """Eight column masks, canonical under facet relabeling and dihedral order."""
    cycle = tuple(map(int, cycle))
    n, mask = len(cycle), (1 << len(cycle)) - 1
    cols = [sum(((f >> v) & 1) << j for j, f in enumerate(cycle)) for v in range(8)]
    reverse = [sum(((v >> j) & 1) << (n - 1 - j) for j in range(n)) for v in cols]
    return min(tuple(sorted((v >> j) | ((v << (n - j)) & mask) for v in cs))
               for cs in (cols, reverse) for j in range(n))


def cycle_from_columns(columns: Iterable[int], n: int) -> list[int]:
    columns = tuple(columns)
    return [sum(((c >> j) & 1) << v for v, c in enumerate(columns)) for j in range(n)]


def enumerate_cycles(spheres: list[list[int]]) -> tuple[list[dict], dict]:
    perms = np.array([(0,) + p for p in permutations(range(1, 8))], dtype=np.uint8)
    maps, good = mask_maps(perms), positive_span_table()
    unique, per_sphere = {}, []
    for ki, facets in enumerate(spheres):
        if len(facets) < 17:
            continue
        incidence = {}
        for fi, f in enumerate(facets):
            for v in range(8):
                if f & (1 << v):
                    incidence.setdefault(f ^ (1 << v), []).append(fi)
        if any(len(x) != 2 for x in incidence.values()):
            raise AssertionError("Invalid triangle incidence")
        states, max_positive = _scan_cycles(
            np.array(facets, np.int64), np.array(list(incidence.values()), np.int64),
            np.array(list(incidence), np.int64), maps, good)
        per_sphere.append({"sphere_index": ki, "tetrahedra": len(facets),
                           "single_cycle_states_at_least_17": len(states),
                           "maximum_positive_tetrahedra": int(max_positive)})
        for row in states:
            n, ip, sigma = map(int, row[:3])
            cycle = list(map(int, row[3:n + 3]))
            key = (n, canonical_cycle(cycle))
            if key not in unique:
                unique[key] = {"n": n, "columns": list(key[1]),
                    "cycle": cycle_from_columns(key[1], n),
                    "witness": {"sphere_index": ki, "permutation": perms[ip].tolist(),
                                "sign_mask": sigma, "uncanonical_cycle": cycle}}
    cycles = [unique[key] for key in sorted(unique)]
    summary = {"spheres": len(spheres), "eligible_spheres": len(per_sphere),
        "states_per_sphere": len(perms) * 128,
        "total_states_checked": len(per_sphere) * len(perms) * 128,
        "single_cycle_states_at_least_17": sum(x["single_cycle_states_at_least_17"] for x in per_sphere),
        "cycles_by_length": dict(sorted(Counter(x["n"] for x in cycles).items())),
        "maximum_positive_tetrahedra": max(x["maximum_positive_tetrahedra"] for x in per_sphere),
        "per_sphere": per_sphere}
    if summary["cycles_by_length"] != {17: 855, 18: 192, 19: 14}:
        raise AssertionError("Unexpected exhaustive cycle counts")
    if summary["maximum_positive_tetrahedra"] != 19:
        raise AssertionError("Unexpected maximum shadow candidate size")
    return cycles, summary


def selected_patterns(cycles: list[dict], n: int) -> list[dict]:
    unique = {}
    for ip, parent in enumerate(cycles):
        for selected in combinations(range(parent["n"]), n):
            cycle = [parent["cycle"][j] for j in selected]
            key = canonical_cycle(cycle)
            if key not in unique:
                unique[key] = {"n": n, "cycle": cycle_from_columns(key, n),
                    "parent_pattern": ip, "selection": list(selected)}
    return [unique[key] for key in sorted(unique)]
