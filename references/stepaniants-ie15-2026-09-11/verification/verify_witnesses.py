#!/usr/bin/env python3
"""Exact witness checks for IE-15; the universal upper bound is analytic.

Uses only standard-library rational arithmetic. Run with Python 3.
"""
from fractions import Fraction as F


def verify_rook_path(matrix, expected_pivots, expected_growth):
    active = [[F(x) for x in row] for row in matrix]
    initial = max(abs(x) for row in active for x in row)
    largest = initial
    pivots = []
    determinant = F(1)
    stages = []
    while active:
        stages.append(active)
        p = active[0][0]
        assert p != 0
        assert all(abs(active[0][j]) <= abs(p) for j in range(len(active)))
        assert all(abs(active[i][0]) <= abs(p) for i in range(len(active)))
        largest = max(largest, max(abs(x) for row in active for x in row))
        pivots.append(p)
        determinant *= p
        active = [[active[i][j] - active[i][0]*active[0][j]/p
                   for j in range(1, len(active))]
                  for i in range(1, len(active))]
    assert pivots == list(map(F, expected_pivots))
    assert determinant != 0
    assert largest/initial == F(expected_growth)
    return pivots, determinant, largest/initial, stages


a3 = [[1, 0, -1], [0, 1, -1], [1, 1, 1]]
a4 = [[1, 0, 1, 1], [0, 1, F(1, 3), -1],
      [F(-1, 3), -1, 1, -1], [-1, 1, 1, 1]]

for matrix, pivots, growth in [(a3, [1, 1, 3], F(3)),
                                (a4, [1, 1, F(5, 3), F(14, 3)], F(14, 3))]:
    pp, det, actual_growth, stages = verify_rook_path(matrix, pivots, growth)
    print('order:', len(matrix))
    print('pivots:', ', '.join(map(str, pp)))
    print('determinant:', det)
    print('growth:', actual_growth)
    for k, active in enumerate(stages, 1):
        print('stage', k, [[str(x) for x in row] for row in active])
print('PASS: both matrices are nonsingular, every diagonal pivot is rook-admissible,')
print('and the exact growth factors are 3 and 14/3.')
