"""Exact small-n check of the MD-01 Theorem 3.24 mixed-moment example.

The shapes, in product order, are P1, P1, overline(overline(P2) o P1),
and overline(P2).  For a sign adjacency matrix A, the last two matrices
are respectively a four-cycle with a chord and a triangle.  Every graph
matrix sums over injective maps, as in Definition 2.9 of arXiv:2609.30064v1.
"""

from fractions import Fraction
from itertools import combinations


def expected_unnormalized_trace(n: int) -> Fraction:
    pairs = list(combinations(range(n), 2))
    total = 0
    for mask in range(1 << len(pairs)):
        sign = [[0] * n for _ in range(n)]
        for bit, (i, j) in enumerate(pairs):
            sign[i][j] = sign[j][i] = 1 if (mask >> bit) & 1 else -1

        triangle = [[0] * n for _ in range(n)]
        chorded_cycle = [[0] * n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                for k in range(n):
                    if k in (i, j):
                        continue
                    triangle[i][j] += sign[i][k] * sign[k][j] * sign[i][j]
                    for ell in range(n):
                        if ell in (i, j, k):
                            continue
                        chorded_cycle[i][j] += (
                            sign[i][k]
                            * sign[k][ell]
                            * sign[ell][j]
                            * sign[i][j]
                            * sign[i][ell]
                        )

        total += sum(
            sign[a][b] * sign[b][c] * chorded_cycle[c][d] * triangle[d][a]
            for a in range(n)
            for b in range(n)
            for c in range(n)
            for d in range(n)
        )
    return Fraction(total, 1 << len(pairs))


if __name__ == "__main__":
    for n in (4, 5):
        expected = expected_unnormalized_trace(n)
        four_distinct = n * (n - 1) * (n - 2) * (n - 3)
        assert expected == four_distinct
        print(f"n={n}: E[raw mixed trace]={expected}=(n)_4")
    print("Normalized witness contribution: (n)_4 / n^(7/2) = Theta(sqrt(n)).")
