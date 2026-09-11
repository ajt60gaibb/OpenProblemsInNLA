"""Independent exact spot checks for the AV-01/AV-02 proof review.

Uses only Python's standard library; does not import submitted code.
These bounded checks supplement, and do not replace, the proof audit.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import isqrt
from pathlib import Path
import json


def positive_definite(matrix):
    # Congruence elimination: all pivots must be strictly positive.
    h = [[F(z) for z in row] for row in matrix]
    for k in range(len(h)):
        if h[k][k] <= 0:
            return False
        for i in range(k + 1, len(h)):
            for j in range(i, len(h)):
                h[j][i] = h[i][j] = h[i][j] - h[i][k] * h[k][j] / h[k][k]
    return True


def threshold_test(matrix, signs, threshold):
    n = len(matrix)
    m = [[matrix[i][j] - (signs[i] if i == j else 0)
          for j in range(n)] for i in range(n)]
    h = [[threshold**2 * sum(m[k][i] * m[k][j] for k in range(n))
          - (i == j) for j in range(n)] for i in range(n)]
    return not positive_definite(h)


def graph_check(v, edges):
    n = 1 + v + len(edges)
    scale = 12 * n**2
    a = [[2 * (i == j) for j in range(n)] for i in range(n)]
    for i in range(v):
        a[0][i + 1] = scale
    for j, (p, q) in enumerate(edges):
        a[p + 1][1 + v + j] = scale
        a[q + 1][1 + v + j] = -scale
    cuts = [sum(s[p] != s[q] for p, q in edges)
            for s in product((0, 1), repeat=v)]
    maximum = max(cuts)
    cases = 0
    for k in range(1, len(edges) + 1):
        threshold = 8 * n**3 * isqrt(144 * n**2 * k)
        # Exhaust every diagonal endpoint, including all no-instance endpoints.
        outcomes = [threshold_test(a, signs, threshold)
                    for signs in product((-1, 1), repeat=n)]
        assert any(outcomes) == (maximum >= k)
        cases += len(outcomes)
    return {"vertices": v, "edges": edges, "maximum_cut": maximum,
            "endpoint_threshold_tests": cases}


def main():
    a = [[F(3, 5), F(3, 5)], [F(-3, 5), F(3, 5)]]
    b = [F(1), F(2)]
    solutions = [[F(10, 73), F(95, 73)], [F(-10, 7), F(5, 7)],
                 [F(40, 7), F(-95, 7)], [F(-40, 13), F(-5, 13)]]
    determinants = []
    for x in solutions:
        assert [sum(a[i][j] * x[j] for j in range(2)) + abs(x[i])
                for i in range(2)] == b
        s = [1 if z > 0 else -1 for z in x]
        determinant = (a[0][0] + s[0]) * (a[1][1] + s[1]) - a[0][1] * a[1][0]
        assert determinant != 0
        determinants.append(str(determinant))
    # Fully integral verification of both inequalities used to separate thresholds.
    gap_tests = 0
    graph_count = 0
    for v in range(2, 6):
        possible = list(combinations(range(v), 2))
        for bits in product((0, 1), repeat=len(possible)):
            m = sum(bits)
            if not m:
                continue
            graph_count += 1
            n = 1 + v + m
            for k in range(1, m + 1):
                t = 8 * n**3 * isqrt(144 * n**2 * k)
                lead, remainder = 96 * n**4, 36 * n**3
                assert t*t <= lead*lead*k
                assert t > remainder and (t-remainder)**2 > lead*lead*(k-1)
                gap_tests += 1
    records = [graph_check(2, [(0, 1)]), graph_check(3, [(0, 1)]),
               graph_check(3, [(0, 1), (1, 2)]),
               graph_check(3, [(0, 1), (0, 2), (1, 2)])]
    # Equality is a yes case; a larger positive threshold is not.
    assert threshold_test([[2]], [1], F(1))
    assert not threshold_test([[2]], [1], F(2))
    root = Path(__file__).resolve().parents[3]
    inputs = root / '.cache/colbrook-package-submission/nla_submission/manuscripts'
    hashes = {}
    for name in ('AV-01.tex', 'AV-02.tex', 'common.tex'):
        normalized = (inputs / name).read_bytes().decode('utf-8').replace('\r\n', '\n').encode('utf-8')
        hashes[name] = {"sha256_utf8_lf_no_trim": sha256(normalized).hexdigest(),
                        "normalized_bytes": len(normalized)}
    out = {"status": "PASS", "source_hashes": hashes,
           "AV-01_example_sign_system_determinants": determinants,
           "AV-02_gap_graphs": graph_count, "AV-02_gap_threshold_cases": gap_tests,
           "AV-02_exhaustive_endpoint_graphs": records,
           "AV-02_equality_boundary_tests": 2}
    destination = Path(__file__).with_name('independent_av_review_results.json')
    destination.write_text(json.dumps(out, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(out, indent=2))


if __name__ == '__main__':
    main()
