"""Standalone four-pivot proof of the literal factor-2 counterexample.

Run with Python 3; no third-party libraries are needed.
"""
from fractions import Fraction as Q
import json


def verify() -> dict:
    a = ((Q(2), Q(1)), (Q(1), Q(2)))
    normalizer = sum((x * x for row in a for x in row), Q(0))
    expected = Q(0)
    probability_sum = Q(0)
    rows = []
    for i in range(2):
        for j in range(2):
            p = a[i][j] ** 2 / normalizer
            residual = tuple(tuple(a[u][v] - a[u][j] * a[i][v] / a[i][j]
                                   for v in range(2)) for u in range(2))
            error = sum((x * x for row in residual for x in row), Q(0))
            probability_sum += p
            expected += p * error
            rows.append({"pivot_one_based": [i + 1, j + 1], "probability": str(p),
                         "residual": [[str(x) for x in row] for row in residual],
                         "squared_error": str(error), "weighted_squared_error": str(p * error)})
    assert probability_sum == 1
    assert expected == Q(18, 5)
    # A(1,1)^T = 3(1,1)^T and A(1,-1)^T = (1,-1)^T: singular values 3,1.
    optimal_squared_error = Q(1)
    assert expected > 2 * optimal_squared_error
    return {"matrix": [[2, 1], [1, 2]], "singular_values": [3, 1],
            "optimal_rank_one_squared_error": str(optimal_squared_error),
            "expected_squared_error": str(expected), "pivots": rows,
            "literal_factor_two_bound_is_false": True}


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
