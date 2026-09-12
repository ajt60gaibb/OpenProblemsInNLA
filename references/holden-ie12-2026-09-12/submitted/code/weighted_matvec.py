"""Exact weighted-pattern matrix-vector products used in the IE-12 proof.

The default ``apply`` method supports Python integers and fractions.Fraction;
it contains no floating-point arithmetic. The optional ``apply_numpy`` method
is a floating-point implementation for experiments, not a stability theorem.

Complexity here means scalar operations, not Python bit complexity. In the
paper, pattern identifiers are built by scalar integer arithmetic, not by
assuming a floor, logarithm, hashing, or bit-packing primitive.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Sequence


def choose_k(n: int) -> int:
    """Return max(1, floor(log_16(n))) using only multiplication/comparison."""
    if not isinstance(n, int) or n < 1:
        raise ValueError("n must be a positive integer")
    k, power = 1, 16
    while 16 * power <= n:
        power *= 16
        k += 1
    return k


def floor_by_comparisons(value):
    """Floor using O(1+abs(value)) scalar additions/comparisons, no floor oracle."""
    integer = 0
    if value >= 0:
        while integer + 1 <= value:
            integer += 1
    else:
        while integer > value:
            integer -= 1
    return integer


def pattern_weight(pattern: Sequence[int]) -> int:
    return sum(1 + abs(a) for a in pattern)


def encode_pattern(pattern: Sequence[int], k: int) -> int:
    """Unary signed code over {0,1,2}, then padding by 3 to length k.

    0 -> 0; +r -> r copies of 1 followed by 0;
    -r -> r copies of 2 followed by 0. Identifiers are base-4 integers.
    """
    if k < 1:
        raise ValueError("k must be positive")
    code, length = 0, 0
    for a in pattern:
        if not isinstance(a, int):
            raise TypeError("pattern coefficients must be Python integers")
        digit = 1 if a > 0 else 2
        for _ in range(abs(a)):
            code = 4 * code + digit
            length += 1
        code *= 4  # the terminating zero, including for the coefficient 0
        length += 1
    if length > k:
        raise ValueError("pattern exceeds the weight budget")
    while length < k:
        code = 4 * code + 3
        length += 1
    return code


@dataclass(frozen=True)
class PatternDescriptor:
    code: int
    head: int
    tail_code: int
    pattern: tuple[int, ...]


class PatternCatalogue:
    """All integer sequences of weight <= k, including the empty sequence."""

    def __init__(self, k: int):
        if not isinstance(k, int) or k < 1:
            raise ValueError("k must be a positive integer")
        self.k = k
        self.capacity = 4 ** k
        self.empty_code = self.capacity - 1
        self.patterns: list[tuple[int, ...]] = []

        def visit(prefix: tuple[int, ...], remaining: int) -> None:
            self.patterns.append(prefix)
            for a in range(-(remaining - 1), remaining):
                cost = 1 + abs(a)
                if cost <= remaining:
                    visit(prefix + (a,), remaining - cost)

        visit((), k)
        self.descriptors: list[PatternDescriptor] = []
        for pattern in self.patterns:
            if pattern:
                self.descriptors.append(PatternDescriptor(
                    encode_pattern(pattern, k), pattern[0],
                    encode_pattern(pattern[1:], k), pattern))
        assert len(self.patterns) <= self.capacity
        assert len({encode_pattern(s, k) for s in self.patterns}) == len(self.patterns)
        self._numpy_cache = None

    def table(self, vector: Sequence[Any]) -> list[list[Any]]:
        """F[j,s] = sum_i s[i]*vector[j+i], with zero padding at the end."""
        n = len(vector)
        rows: list[list[Any]] = [[0] * self.capacity for _ in range(n + 1)]
        for j in range(n - 1, -1, -1):
            current, following = rows[j], rows[j + 1]
            for descriptor in self.descriptors:
                current[descriptor.code] = (
                    descriptor.head * vector[j]
                    + following[descriptor.tail_code]
                )
        return rows

    def table_numpy(self, vector):
        import numpy as np
        vector = np.asarray(vector, dtype=float)
        if vector.ndim != 1:
            raise ValueError("vector must be one-dimensional")
        if self._numpy_cache is None:
            self._numpy_cache = (
                np.array([d.code for d in self.descriptors], dtype=np.intp),
                np.array([d.head for d in self.descriptors], dtype=float),
                np.array([d.tail_code for d in self.descriptors], dtype=np.intp),
            )
        codes, heads, tails = self._numpy_cache
        table = np.zeros((len(vector) + 1, self.capacity), dtype=float)
        for j in range(len(vector) - 1, -1, -1):
            table[j, codes] = heads * vector[j] + table[j + 1, tails]
        return table


@dataclass(frozen=True)
class Term:
    start: int
    pattern_code: int | None = None
    coefficient: int | None = None

    @property
    def is_heavy(self) -> bool:
        return self.pattern_code is None


class WeightedMatvec:
    """Preprocess a rectangular integer matrix for repeated real products.

    If the matrix is m-by-n and W=sum(1+abs(z_ij)), each product costs
    O(n*4**k + W/k + m), after O(W + m*k + k*4**k) preprocessing.
    The main theorem uses square matrices and k=choose_k(n).
    """

    def __init__(self, matrix: Sequence[Sequence[int]], k: int | None = None,
                 catalogue: PatternCatalogue | None = None):
        if not matrix or not matrix[0]:
            raise ValueError("matrix must be nonempty")
        self.m, self.n = len(matrix), len(matrix[0])
        if any(len(row) != self.n for row in matrix):
            raise ValueError("matrix rows have different lengths")
        if any(not isinstance(z, int) for row in matrix for z in row):
            raise TypeError("matrix coefficients must be Python integers")
        self.k = choose_k(self.n) if k is None else k
        if self.k < 1:
            raise ValueError("k must be positive")
        self.catalogue = catalogue or PatternCatalogue(self.k)
        if self.catalogue.k != self.k:
            raise ValueError("catalogue and matrix use different budgets")
        self.weight = sum(1 + abs(z) for row in matrix for z in row)
        self.rows: list[list[Term]] = []
        self.heavy_count = 0
        self.pattern_count = 0

        for row in matrix:
            terms: list[Term] = []
            pending: list[int] = []
            pending_weight, start = 0, 0

            def flush() -> None:
                nonlocal pending, pending_weight
                if pending:
                    terms.append(Term(start, encode_pattern(pending, self.k)))
                    self.pattern_count += 1
                    pending, pending_weight = [], 0

            for j, coefficient in enumerate(row):
                weight = 1 + abs(coefficient)
                if weight > self.k:
                    flush()
                    terms.append(Term(j, coefficient=coefficient))
                    self.heavy_count += 1
                    continue
                if pending_weight + weight > self.k:
                    flush()
                if not pending:
                    start = j
                pending.append(coefficient)
                pending_weight += weight
            flush()
            self.rows.append(terms)

        self.term_count = self.heavy_count + self.pattern_count
        # The packing estimate is exact integer arithmetic.
        assert self.k * self.term_count <= 2 * self.weight + self.k * self.m
        self._numpy_terms = None

    def apply(self, vector: Sequence[Any]) -> list[Any]:
        if len(vector) != self.n:
            raise ValueError("incompatible vector length")
        table = self.catalogue.table(vector)
        result = []
        for terms in self.rows:
            value = 0
            for term in terms:
                if term.is_heavy:
                    value += term.coefficient * vector[term.start]
                else:
                    value += table[term.start][term.pattern_code]
            result.append(value)
        return result

    def apply_numpy(self, vector):
        """Floating-point evaluation of the same arithmetic circuit."""
        import numpy as np
        vector = np.asarray(vector, dtype=float)
        if vector.shape != (self.n,):
            raise ValueError("incompatible vector shape")
        table = self.catalogue.table_numpy(vector)
        if self._numpy_terms is None:
            p_rows, starts, codes = [], [], []
            h_rows, h_cols, h_coeffs = [], [], []
            for row, terms in enumerate(self.rows):
                for term in terms:
                    if term.is_heavy:
                        h_rows.append(row)
                        h_cols.append(term.start)
                        h_coeffs.append(term.coefficient)
                    else:
                        p_rows.append(row)
                        starts.append(term.start)
                        codes.append(term.pattern_code)
            self._numpy_terms = (
                np.array(p_rows, dtype=np.intp),
                np.array(starts, dtype=np.intp),
                np.array(codes, dtype=np.intp),
                np.array(h_rows, dtype=np.intp),
                np.array(h_cols, dtype=np.intp),
                np.array(h_coeffs, dtype=float),
            )
        p_rows, starts, codes, h_rows, h_cols, h_coeffs = self._numpy_terms
        result = np.bincount(p_rows, weights=table[starts, codes],
                             minlength=self.m).astype(float, copy=False)
        result += np.bincount(h_rows, weights=h_coeffs * vector[h_cols], minlength=self.m)
        return result

    def scalar_arithmetic_count(self) -> int:
        """Arithmetic count for apply; excludes table/metadata memory access."""
        return (2 * self.n * len(self.catalogue.descriptors)
                + self.term_count + self.heavy_count)


def dense_product(matrix: Sequence[Sequence[Any]], vector: Sequence[Any]) -> list[Any]:
    if not matrix or any(len(row) != len(vector) for row in matrix):
        raise ValueError("incompatible matrix/vector")
    return [sum(a * x for a, x in zip(row, vector)) for row in matrix]
