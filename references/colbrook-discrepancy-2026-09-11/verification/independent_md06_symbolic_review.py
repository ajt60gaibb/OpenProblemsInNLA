"""Reviewer-written symbolic check of MD-06's finite tree construction.

Not supplied in the author's archive. Uses the analytically proved scalar
identity 2*a_0 = 2*pi-delta_0 and sin(delta_j)=t_R/2**j.
No numerical trigonometry, optimizer, or supplied code is imported.
"""
from collections import deque
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path


def check(radius):
    phases, edges, last = [], [], []
    signs = (1, 1, -1, -1)
    def vertex(sign, depth):
        phases.append(tuple(sign if j >= depth else 0 for j in range(radius)))
        return len(phases) - 1
    roots = [vertex(sign, 0) for sign in signs]
    edges.extend((roots[i], roots[(i+1) % 4]) for i in range(4))
    for root, sign in zip(roots, signs):
        level = [root]
        for depth in range(1, radius):
            following = []
            for parent in level:
                for _ in range(1 if depth == 1 else 2):
                    child = vertex(sign, depth)
                    edges.append((parent, child))
                    following.append(child)
            level = following
        last.append([parent for parent in level for _ in range(2)])
    groups = []
    for positive, negative in ((0, 2), (1, 3)):
        group = []
        for p, q in zip(last[positive], last[negative]):
            leaf = vertex(0, radius)
            edges.extend(((p, leaf), (q, leaf)))
            group.append(leaf)
        groups.append(group)
    edges.extend(zip(groups[0], groups[1]))
    n = len(phases)
    assert n == 3 * 2**radius and len(edges) == 3*n//2
    assert len({tuple(sorted(edge)) for edge in edges}) == len(edges)
    adj = [[] for _ in phases]
    flow = [F(0) for _ in phases]
    kinds = {"zero": 0, "tree": 0, "cross_root": 0}
    for u, v in edges:
        assert u != v
        adj[u].append(v)
        adj[v].append(u)
        difference = tuple(x-y for x, y in zip(phases[u], phases[v]))
        nonzero = [j for j, value in enumerate(difference) if value]
        if not nonzero:
            coefficient = F(0)
            kinds["zero"] += 1
        elif len(nonzero) == 1 and abs(difference[nonzero[0]]) == 1:
            j = nonzero[0]
            coefficient = F(difference[j], 2**j)
            kinds["tree"] += 1
        else:
            assert difference in ((2,)*radius, (-2,)*radius)
            coefficient = F(-difference[0], 2)
            kinds["cross_root"] += 1
        flow[u] += coefficient
        flow[v] -= coefficient
    assert all(len(neighbors) == 3 for neighbors in adj)
    visited, queue = {0}, deque([0])
    while queue:
        for v in adj[queue.popleft()]:
            if v not in visited:
                visited.add(v)
                queue.append(v)
    assert len(visited) == n and all(value == 0 for value in flow)
    return {"R": radius, "vertices": n, "edges": len(edges),
            "edge_types": kinds, "all_exact_sine_flow_coefficients_zero": True}


if __name__ == '__main__':
    # Exact arithmetic in the explicit-constant remark.
    assert F(-1, 5) + F(7, 4)*F(99, 100) + F(1, 24)*F(97, 100) == F(151, 96)
    assert F(151, 96) > F(11, 7)
    assert F(99, 100)**2 < F(255, 256)
    assert F(97, 100)**2 < F(255, 256)**3
    assert F(32) / (F(1, 16)**4 * F(1, 10)**2) == 209715200 < 2**28
    assert F(1, 4)**4 * F(1, 100)**2 / 32 == F(1, 81920000)
    assert F(1, 8)**4 * F(1, 6000)**2 / 32 == F(1, 4718592000000)
    source = Path(__file__).resolve().parents[1] / 'submitted/MD-06/manuscript/md06_counterexample.tex'
    normalized = source.read_bytes().decode('utf-8').replace('\r\n', '\n').encode('utf-8')
    result = {"status": "PASS", "provenance": "independent reviewer; not submitted code",
              "source_utf8_lf_no_trim_sha256": sha256(normalized).hexdigest(),
              "source_normalized_bytes": len(normalized),
              "exact_constant_arithmetic": "PASS",
              "symbolic_gadgets": [check(r) for r in (4, 5, 6)]}
    destination = Path(__file__).with_name('independent_md06_symbolic_review_results.json')
    destination.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
