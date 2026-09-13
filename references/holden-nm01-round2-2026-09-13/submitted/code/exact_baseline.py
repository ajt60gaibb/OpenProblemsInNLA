#!/usr/bin/env python3
"""Exact rational reference algorithms for NM-01.

The search is exponential in variable rank, polynomial for each fixed rank.
It does not check the SSC promise. Correctness on promised inputs is proved
in paper/nm01_note.pdf. A support certificate certifies FEASIBILITY/value,
not optimality in the absence of the promise and the exhaustive search.

No third-party packages are required. JSON rationals must be strings or ints;
binary floating-point inputs are rejected.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from itertools import combinations
from math import gcd, lcm
from pathlib import Path
from typing import Any, Sequence
import json

Matrix = list[list[F]]

class InputError(ValueError):
    """Invalid input or a failed necessary condition of the promise."""


def rational(x: Any) -> F:
    if isinstance(x, bool) or not isinstance(x, (int, str, F)):
        raise InputError('Use integers or rational strings, not floats.')
    try:
        return F(x)
    except (ValueError, ZeroDivisionError) as exc:
        raise InputError(f'Invalid rational: {x!r}') from exc


def matrix(a: Sequence[Sequence[Any]]) -> Matrix:
    if (not isinstance(a, Sequence) or isinstance(a, (str, bytes))
            or not a or any(not isinstance(row, Sequence) or
                           isinstance(row, (str, bytes)) for row in a)
            or not a[0] or any(len(row) != len(a[0]) for row in a)):
        raise InputError('A nonempty rectangular matrix is required.')
    return [[rational(x) for x in row] for row in a]


def transpose(a: Matrix) -> Matrix:
    return [list(row) for row in zip(*a)]


def eye(n: int) -> Matrix:
    return [[F(i == j) for j in range(n)] for i in range(n)]


def matmul(a: Matrix, b: Matrix) -> Matrix:
    if len(a[0]) != len(b):
        raise InputError('Incompatible matrix dimensions.')
    bt = transpose(b)
    return [[sum((x*y for x, y in zip(row, col)), F(0))
             for col in bt] for row in a]


def rref(a: Matrix) -> tuple[Matrix, list[int]]:
    out = [row[:] for row in a]
    nr, nc, k = len(out), len(out[0]), 0
    pivots: list[int] = []
    for j in range(nc):
        pivot = next((i for i in range(k, nr) if out[i][j]), None)
        if pivot is None:
            continue
        out[k], out[pivot] = out[pivot], out[k]
        v = out[k][j]
        out[k] = [x/v for x in out[k]]
        for i in range(nr):
            if i != k and out[i][j]:
                v = out[i][j]
                out[i] = [x-v*y for x, y in zip(out[i], out[k])]
        pivots.append(j)
        k += 1
        if k == nr:
            break
    return out, pivots


def rank(a: Matrix) -> int:
    return len(rref(a)[1])


def determinant(a: Matrix) -> F:
    n = len(a)
    if any(len(row) != n for row in a):
        raise InputError('Determinant requires a square matrix.')
    out = [row[:] for row in a]
    ans = F(1)
    for j in range(n):
        p = next((i for i in range(j, n) if out[i][j]), None)
        if p is None:
            return F(0)
        if p != j:
            out[p], out[j] = out[j], out[p]
            ans = -ans
        v = out[j][j]
        ans *= v
        for i in range(j+1, n):
            q = out[i][j]/v
            for k in range(j+1, n):
                out[i][k] -= q*out[j][k]
            out[i][j] = F(0)
    return ans


def inverse(a: Matrix) -> Matrix:
    n = len(a)
    if any(len(row) != n for row in a):
        raise InputError('Inverse requires a square matrix.')
    aug = [row[:] + ident for row, ident in zip(a, eye(n))]
    rr, piv = rref(aug)
    if piv[:n] != list(range(n)):
        raise InputError('Singular matrix.')
    return [row[n:] for row in rr]


def primitive(v: list[F]) -> tuple[int, ...]:
    den = lcm(*(x.denominator for x in v))
    vals = [int(x*den) for x in v]
    g = gcd(*vals)
    if g == 0:
        raise InputError('Zero normal.')
    return tuple(x//g for x in vals)


def facet_from_support(y: Matrix, support: Sequence[int]) -> tuple[int, ...] | None:
    r, n = len(y), len(y[0])
    if (not isinstance(support, Sequence) or isinstance(support, (str, bytes))
            or len(support) != r-1):
        return None
    if any(not isinstance(j, int) or isinstance(j, bool) or j < 0 or j >= n for j in support):
        return None
    if len(set(support)) != r-1:
        return None
    rows = [[y[i][j] for i in range(r)] for j in support]
    rr, piv = rref(rows)
    if len(piv) != r-1:
        return None
    free = next(i for i in range(r) if i not in piv)
    v = [F(0)]*r
    v[free] = F(1)
    for i, j in enumerate(piv):
        v[j] = -rr[i][free]
    normal = primitive(v)
    signs: set[int] = set()
    for j in range(n):
        s = sum(normal[i]*y[i][j] for i in range(r))
        if s:
            signs.add(1 if s > 0 else -1)
        if len(signs) == 2:
            return None
    if signs == {-1}:
        return tuple(-x for x in normal)
    return normal if signs == {1} else None


def facets(y: Matrix) -> dict[tuple[int, ...], tuple[int, ...]]:
    """Enumerate all affine facets as homogeneous normals on e^T y = 1."""
    r, n = len(y), len(y[0])
    if rank(y) != r or any(sum(col) != 1 for col in transpose(y)):
        raise InputError('Facet enumeration needs rank r and column sums one.')
    found: dict[tuple[int, ...], tuple[int, ...]] = {}
    for support in combinations(range(n), r-1):
        normal = facet_from_support(y, support)
        if normal is not None and normal not in found:
            found[normal] = support
    return found


def reduce_input(x: Matrix, r: int) -> tuple[Matrix, Matrix, list[int]]:
    m, n = len(x), len(x[0])
    if not isinstance(r, int) or isinstance(r, bool) or not 2 <= r <= min(m, n):
        raise InputError('Require 2 <= r <= min(m,n).')
    piv = rref(x)[1]
    if len(piv) != r:
        raise InputError('The rank promise fails.')
    b = [[row[j] for j in piv] for row in x]
    row_ids = rref(transpose(b))[1]
    b0 = [b[i] for i in row_ids]
    x0 = [x[i] for i in row_ids]
    y = matmul(inverse(b0), x0)
    if matmul(b, y) != x:
        raise InputError('Rank factorization check failed.')
    if any(sum(col) != 1 for col in transpose(y)):
        raise InputError('The affine-normalization promise fails.')
    return b, y, piv


def candidate(y: Matrix, normals: Sequence[Sequence[int]]) -> Matrix | None:
    r = len(y)
    if len(normals) != r:
        return None
    c = [[F(x) for x in row] for row in normals]
    if determinant(c) == 0:
        return None
    s = [sum(row) for row in inverse(transpose(c))]
    if min(s) <= 0:
        return None
    a = [[s[i]*v for v in c[i]] for i in range(r)]
    if any(sum(col) != 1 for col in transpose(a)):
        raise ArithmeticError('Internal column-normalization error.')
    if any(v < 0 for row in matmul(a, y) for v in row):
        return None
    return a


def verify_support_certificate(x: Matrix, r: int, tau: F,
                               supports: Sequence[Sequence[int]]) -> dict[str, Any]:
    """Polynomial-time YES verifier. It does not claim to verify SSC/optimality."""
    b, y, piv = reduce_input(x, r)
    if (tau < 0 or not isinstance(supports, Sequence)
            or isinstance(supports, (str, bytes)) or len(supports) != r):
        return {'accepted': False, 'reason': 'Invalid threshold or support count.'}
    normals = [facet_from_support(y, support) for support in supports]
    if any(v is None for v in normals):
        return {'accepted': False, 'reason': 'A listed support is not a facet support.'}
    a = candidate(y, normals)  # type: ignore[arg-type]
    if a is None:
        return {'accepted': False, 'reason': 'No normalized feasible simplex.'}
    value = determinant(matmul(transpose(b), b))/determinant(a)**2
    return {'accepted': value <= tau, 'candidate_value': str(value),
            'threshold': str(tau), 'basis_columns': piv,
            'certificate_scope': 'feasibility and threshold; not SSC or optimality'}


def solve(x: Matrix, r: int, tau: F | None = None) -> dict[str, Any]:
    b, y, piv = reduce_input(x, r)
    if tau is not None and tau < 0:
        raise InputError('The threshold must be nonnegative.')
    normals_to_supports = facets(y)
    normal_list = sorted(normals_to_supports)
    gram = determinant(matmul(transpose(b), b))
    best: F | None = None
    best_a: Matrix | None = None
    best_normals = None
    examined = feasible = 0
    for ns in combinations(normal_list, r):
        examined += 1
        a = candidate(y, ns)
        if a is None:
            continue
        feasible += 1
        value = gram/determinant(a)**2
        if best is None or value < best:
            best, best_a, best_normals = value, a, ns
    if best is None or best_a is None or best_normals is None:
        return {'status': 'no_facet_supported_simplex',
                'meaning': 'This input does not satisfy the NM-01 promise.',
                'facets': len(normal_list), 'candidate_sets_examined': examined}
    w = matmul(b, inverse(best_a))
    h = matmul(best_a, y)
    if matmul(w, h) != x or any(v < 0 for row in h for v in row):
        raise ArithmeticError('Internal factorization check failed.')
    if determinant(matmul(transpose(w), w)) != best:
        raise ArithmeticError('Internal objective check failed.')
    out: dict[str, Any] = {
        'status': 'exact_on_promised_inputs',
        'runtime_scope': 'polynomial for fixed r; exponential for variable r',
        'promise_checked': False,
        'value': str(best),
        'basis_columns': piv,
        'support_certificate': [list(normals_to_supports[v]) for v in best_normals],
        'W': [[str(v) for v in row] for row in w],
        'H': [[str(v) for v in row] for row in h],
        'facets': len(normal_list),
        'candidate_sets_examined': examined,
        'feasible_candidate_sets': feasible,
    }
    if tau is not None:
        out.update(threshold=str(tau), answer=('YES' if best <= tau else 'NO'))
    return out


def check_ssc_small(h: Matrix) -> dict[str, Any]:
    """Complete, exponential small-instance check of BOTH SSC conventions.

    Enumerates the vertices of the normalized dual through primal facets,
    then all candidate orthonormal bases of its spherical boundary vertices.
    This is a verifier for tests, NOT a polynomial-time SSC checker.
    """
    r = len(h)
    if any(v < 0 for row in h for v in row) or rank(h) < r:
        return {'ssc1': False, 'weak_ssc': False, 'strong_ssc': False}
    fs = facets(h)
    if any(sum(v) <= 0 for v in fs):
        return {'ssc1': False, 'weak_ssc': False, 'strong_ssc': False,
                'reason': 'The simplex barycenter is not strictly interior.'}
    dual = [[F(v, sum(row)) for v in row] for row in fs]
    norms = [sum(x*x for x in q) for q in dual]
    ssc1 = all(t <= 1 for t in norms)
    if not ssc1:
        return {'ssc1': False, 'weak_ssc': False, 'strong_ssc': False,
                'max_dual_norm_squared': str(max(norms))}
    boundary = [q for q, t in zip(dual, norms) if t == 1]
    coordinate = {tuple(row) for row in eye(r)}
    strong = all(tuple(q) in coordinate for q in boundary)
    nontrivial = None
    for rows in combinations(boundary, r):
        if all(sum(x*y for x, y in zip(rows[i], rows[j])) == 0
               for i in range(r) for j in range(i)):
            if {tuple(row) for row in rows} != coordinate:
                nontrivial = rows
                break
    return {'ssc1': True, 'weak_ssc': nontrivial is None,
            'strong_ssc': strong, 'boundary_vertices': len(boundary),
            'max_dual_norm_squared': str(max(norms)),
            'nontrivial_orthogonal_rows': (None if nontrivial is None else
                [[str(v) for v in row] for row in nontrivial])}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, help='JSON with X, r, optional tau')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--verify', type=Path, help='JSON containing support_certificate')
    args = parser.parse_args()
    try:
        payload = json.loads(args.input.read_text())
        if not isinstance(payload, dict):
            raise InputError('Input JSON must be an object with X and r.')
        x, r = matrix(payload['X']), payload['r']
        tau = rational(payload['tau']) if 'tau' in payload else None
        if args.verify:
            if tau is None:
                raise InputError('Verification requires tau in input.')
            cert_payload = json.loads(args.verify.read_text())
            if not isinstance(cert_payload, dict):
                raise InputError('Certificate JSON must be an object.')
            cert = cert_payload['support_certificate']
            result = verify_support_certificate(x, r, tau, cert)
        else:
            result = solve(x, r, tau)
        rendered = json.dumps(result, indent=2) + '\n'
        if args.output:
            args.output.write_text(rendered)
        else:
            print(rendered, end='')
    except (InputError, KeyError, OSError, json.JSONDecodeError) as exc:
        parser.exit(2, f'error: {exc}\n')

if __name__ == '__main__':
    main()
