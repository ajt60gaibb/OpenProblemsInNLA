"""Exact modular rank certificates for regular-polygon lift incidences.

A nonzero minor modulo a prime proves that the corresponding minor over
Q(zeta_n) is nonzero. The report supplies the specialization argument;
this is NOT the invalid claim that absence of F_p-points implies absence
of real or complex solutions.
"""
from __future__ import annotations
from itertools import combinations
from math import comb
import numpy as np
from numba import njit
from sympy import isprime, primitive_root


@njit(cache=True)
def rref(matrix, prime):
    a = matrix.copy()
    m, n = a.shape
    rank = 0
    pivots = np.zeros(min(m, n), np.int64)
    inverse = np.zeros(prime, np.int64)
    for x in range(1, prime):
        # Prime-field inverses, exact integer arithmetic.
        for y in range(1, prime):
            if (x * y) % prime == 1:
                inverse[x] = y
                break
    for j in range(n):
        k = rank
        while k < m and a[k, j] == 0:
            k += 1
        if k == m:
            continue
        for c in range(n):
            a[rank, c], a[k, c] = a[k, c], a[rank, c]
        scale = inverse[a[rank, j]]
        for c in range(n):
            a[rank, c] = (a[rank, c] * scale) % prime
        for k in range(m):
            if k == rank:
                continue
            scale = a[k, j]
            if scale:
                for c in range(n):
                    a[k, c] = (a[k, c] - scale * a[rank, c]) % prime
        pivots[rank] = j
        rank += 1
        if rank == n or rank == m:
            break
    return a[:rank], pivots[:rank]


def nullspace(matrix: np.ndarray, prime: int) -> np.ndarray:
    reduced, pivots = rref(matrix, prime)
    free = [j for j in range(matrix.shape[1]) if j not in pivots]
    basis = np.zeros((matrix.shape[1], len(free)), np.int64)
    for k, j in enumerate(free):
        basis[j, k] = 1
        for t, i in enumerate(pivots):
            basis[i, k] = -reduced[t, j] % prime
    # Check the actual basis rather than relying only on its construction.
    if np.any((matrix @ basis) % prime):
        raise AssertionError("Nullspace residual is nonzero")
    return basis


@njit(cache=True)
def plucker_matrix(basis, pair_indices, prime):
    """Coefficients of p_ab*p_cd-p_ac*p_bd+p_ad*p_bc after substitution."""
    ell = basis.shape[1]
    out = np.zeros((len(pair_indices), ell * (ell + 1) // 2), np.int64)
    for row in range(len(pair_indices)):
        a, b, c, d, e, f = pair_indices[row]
        col = 0
        for u in range(ell):
            for v in range(u, ell):
                value = (basis[a, u] * basis[b, v] - basis[c, u] * basis[d, v]
                         + basis[e, u] * basis[f, v])
                if u != v:
                    value += (basis[a, v] * basis[b, u] - basis[c, v] * basis[d, u]
                              + basis[e, v] * basis[f, u])
                out[row, col] = value % prime
                col += 1
    return out


class IncidenceTest:
    def __init__(self, n: int, prime: int, gauge: tuple[int, int, int] = (0, 1, 2)):
        if not (3 <= n and isprime(prime) and (prime - 1) % n == 0):
            raise ValueError("Need a prime congruent to 1 modulo n")
        if len(set(gauge)) != 3 or any(j not in range(n) for j in gauge):
            raise ValueError("Invalid gauge rows")
        self.n, self.prime, self.gauge = n, prime, tuple(gauge)
        generator = int(primitive_root(prime))
        self.root = pow(generator, (prime - 1) // n, prime)
        if pow(self.root, n, prime) != 1 or any(pow(self.root, k, prime) == 1 for k in range(1, n)):
            raise AssertionError("Root is not primitive")
        self.free = [j for j in range(n) if j not in gauge]
        self.pairs = list(combinations(self.free, 2))
        pair_id = {q: j for j, q in enumerate(self.pairs)}
        self.plucker_indices = np.array([
            (pair_id[a, b], pair_id[c, d], pair_id[a, c], pair_id[b, d], pair_id[a, d], pair_id[b, c])
            for a, b, c, d in combinations(self.free, 4)], np.int64)
        t = [pow(self.root, j, prime) for j in range(n)]
        self.t = t
        minors = {}
        for a, b, c in combinations(range(n), 3):
            x, y, z = t[a], t[b], t[c]
            # det of rows (1,t,t^-1), in increasing row order.
            minors[a, b, c] = ((y - x) * (z - x) * (z - y) * pow(x * y * z, -1, prime)) % prime
            if minors[a, b, c] == 0:
                raise AssertionError("Three distinct conic points became collinear")
        self.row_ids, rows = {}, []
        for five in combinations(range(n), 5):
            row = np.zeros(len(self.pairs), np.int64)
            for i, j in combinations(range(5), 2):
                pair = (five[i], five[j])
                if pair not in pair_id:
                    continue
                triple = tuple(five[k] for k in range(5) if k not in (i, j))
                sign = -1 if (i + j) % 2 == 0 else 1
                row[pair_id[pair]] = sign * minors[triple] % prime
            mask = sum(1 << j for j in five)
            self.row_ids[mask] = len(rows)
            rows.append(row)
        self.rows = np.array(rows, np.int64)

    def incidence_matrix(self, cycle: list[int], reduced_rows: bool = False) -> np.ndarray:
        """All five-minors, or a sufficient basis anchored at three facet points."""
        if len(cycle) != self.n or len(set(cycle)) != self.n:
            raise ValueError("Need n distinct active-facet masks")
        if any(not isinstance(m, int) or not 0 < m < 256 or m.bit_count() != 4 for m in cycle):
            raise ValueError("Each active-facet mask must have exactly four bits")
        faces = [[j for j, mask in enumerate(cycle) if mask & (1 << i)] for i in range(8)]
        subsets = set()
        for face in faces:
            if len(face) < 5:
                continue
            if reduced_rows:
                triples = [tuple(face[:3]) + pair for pair in combinations(face[3:], 2)]
            else:
                triples = combinations(face, 5)
            subsets.update(sum(1 << j for j in a) for a in triples)
        indices = [self.row_ids[mask] for mask in sorted(subsets)]
        return self.rows[indices]

    def check(self, cycle: list[int], *, reduced_rows: bool = False) -> dict:
        pairs = [(a, b) for a in range(self.n) for b in range(a + 1, self.n)
                 if cycle[a] ^ cycle[b] == 255]
        # The complementary pairs form a matching. Their endpoint spikes are
        # independent modulo V when at least three other points remain.
        endpoints = [j for pair in pairs for j in pair]
        if len(set(endpoints)) != len(endpoints) or len(endpoints) > self.n - 3:
            raise AssertionError("The independence lemma's hypotheses fail")
        matrix = self.incidence_matrix(cycle, reduced_rows)
        basis = nullspace(matrix, self.prime)
        ell, s = basis.shape[1], len(pairs)
        if ell < s:
            raise AssertionError("Known complementary spike bivectors missing from kernel")
        quadratic = plucker_matrix(basis, self.plucker_indices, self.prime)
        reduced, _ = rref(quadratic, self.prime)
        qrank, target = len(reduced), comb(ell + 1, 2) - s
        return {"n": self.n, "prime": self.prime, "root": self.root,
                "gauge": list(self.gauge), "reduced_rows": reduced_rows,
                "linear_rows": len(matrix), "linear_columns": matrix.shape[1],
                "nullity_mod_prime": ell, "complementary_pairs": [list(p) for p in pairs],
                "quadratic_rank": qrank, "quadratic_target": target,
                "excluded_as_a_bounded_lift": qrank == target}
