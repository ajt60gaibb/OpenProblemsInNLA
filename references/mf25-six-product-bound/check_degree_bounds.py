#!/usr/bin/env python3
"""Verify the finite pivot-degree and dimension bounds used for MF-25.

This enumerates an overapproximation of possible degree-echelon patterns.
It does not try to construct a straight-line program for any pattern.
"""

from itertools import combinations_with_replacement


def extend(states):
    """Return pivot lists and parameter bounds after one nonredundant gate."""
    result = {}
    for pivots, bound in states.items():
        for i, j in combinations_with_replacement(range(1, len(pivots)), 2):
            product_degree = pivots[i] + pivots[j]
            candidates = (
                range(2, product_degree)
                if product_degree in pivots
                else (product_degree,)
            )
            for degree in candidates:
                if degree in pivots:
                    continue
                new_pivots = tuple(sorted((*pivots, degree)))
                increment = i + j - 2
                if pivots == (0, 1, 2):
                    # The span through degree 3 is fixed. For degree 4,
                    # a new basis element is x**4 + c*x**3 modulo the span.
                    increment = int(degree == 4)
                result[new_pivots] = max(
                    result.get(new_pivots, -1), bound + increment
                )
    return result


def high_degree_rows():
    states = {(0, 1): 0}
    rows = []
    for used in range(6):
        if max(max(pivots) for pivots in states) > 2**used:
            raise RuntimeError("A degree bound exceeded the doubling limit")
        for pivots, bound in sorted(states.items()):
            for i, j in combinations_with_replacement(range(1, len(pivots)), 2):
                a, b = pivots[i], pivots[j]
                if a + b in (33, 34, 35):
                    # Since all previous degrees are at most 32, the last
                    # product must have exactly the target degree.
                    output_bound = bound + i + j - 2 + len(pivots) + 1
                    rows.append((a + b, pivots, (a, b), bound, output_bound))
        if used < 5:
            states = extend(states)
    return sorted(rows)


def main():
    expected = [
        (33, (0, 1, 2, 4, 8, 16, 17), (16, 17), 15, 32),
        (33, (0, 1, 2, 4, 8, 16, 32), (1, 32), 19, 32),
        (34, (0, 1, 2, 4, 8, 9, 17), (17, 17), 15, 33),
        (34, (0, 1, 2, 4, 8, 16, 17), (17, 17), 15, 33),
        (34, (0, 1, 2, 4, 8, 16, 18), (16, 18), 16, 33),
        (34, (0, 1, 2, 4, 8, 16, 32), (2, 32), 19, 33),
    ]
    rows = high_degree_rows()
    if rows != expected:
        raise SystemExit(f"Unexpected high-degree cases: {rows!r}")
    for degree, pivots, factors, before, bound in rows:
        print(f"{degree}: {pivots}, {factors}, parameters {before} -> {bound}")
    print("Verified: no degree-35 case; degree-33/34 dimensions at most 32/33.")


if __name__ == "__main__":
    main()
