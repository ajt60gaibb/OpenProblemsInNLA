#!/usr/bin/env python3
"""Independent exact transcription diagnostics, not a universal or Lean proof.

Work in Q[s,z]/(s^2-3, 1+z+...+z^(k-1)), with star(s)=s,
star(z)=z^(k-1). No approximate complex exponential or norm is evaluated.
This is not imported from the author's Q(sqrt(3),i) checker.
"""
from fractions import Fraction as F
from pathlib import Path
import json

records = []
for k in [2, 3, 5, 9]:
    d = k - 1

    class E:
        def __init__(self, terms=None):
            raw = {} if terms is None else {ij: F(v) for ij, v in terms.items() if v}
            reduced = {}
            for (a, b), c in raw.items():
                aa = a % 2
                reduced[aa, b] = reduced.get((aa, b), F(0)) + c * 3 ** (a // 2)
            for b in range(max((b for a, b in reduced), default=-1), d - 1, -1):
                for a in [0, 1]:
                    c = reduced.pop((a, b), F(0))
                    for j in range(d):
                        ij = (a, b - d + j)
                        reduced[ij] = reduced.get(ij, F(0)) - c
            self.c = {ij: v for ij, v in reduced.items() if v}

        @staticmethod
        def coerce(x):
            return x if isinstance(x, E) else E({(0, 0): F(x)})

        def __add__(self, other):
            other = E.coerce(other)
            keys = self.c.keys() | other.c.keys()
            return E({ij: self.c.get(ij, F(0)) + other.c.get(ij, F(0)) for ij in keys})

        __radd__ = __add__

        def __neg__(self):
            return E({ij: -v for ij, v in self.c.items()})

        def __sub__(self, other):
            return self + -E.coerce(other)

        def __mul__(self, other):
            other = E.coerce(other)
            terms = {}
            for (a, b), x in self.c.items():
                for (c, e), y in other.c.items():
                    ij = (a + c, b + e)
                    terms[ij] = terms.get(ij, F(0)) + x * y
            return E(terms)

        __rmul__ = __mul__

        def __pow__(self, n):
            assert n >= 0
            answer = E.coerce(1)
            for _ in range(n):
                answer = answer * self
            return answer

        def star(self):
            return E({(a, b * (k - 1)): v for (a, b), v in self.c.items()})

        def __eq__(self, other):
            return self.c == E.coerce(other).c

    zero, one = E.coerce(0), E.coerce(1)
    s, z = E({(1, 0): 1}), E({(0, 1): 1})
    assert s * s == 3 and z ** k == 1 and z * z.star() == 1
    assert sum(z ** j for j in range(k)) == 0
    vectors = [[one * F(1, 2), s * F(1, 2) * z ** j] for j in range(k)]
    e1 = [one, zero]
    outer = lambda u, v: [[u[a] * v[b].star() for b in range(2)] for a in range(2)]
    mm = lambda A, B: [[sum(A[a][r] * B[r][b] for r in range(2)) for b in range(2)] for a in range(2)]
    adj = lambda A: [[A[b][a].star() for b in range(2)] for a in range(2)]
    add = lambda A, B: [[A[a][b] + B[a][b] for b in range(2)] for a in range(2)]
    sub = lambda A, B: [[A[a][b] - B[a][b] for b in range(2)] for a in range(2)]
    scale = lambda c, A: [[A[a][b] * c for b in range(2)] for a in range(2)]
    Z = [[zero, zero], [zero, zero]]
    I = [[one, zero], [zero, one]]
    def ms(matrices):
        answer = Z
        for A in matrices:
            answer = add(answer, A)
        return answer
    matrices = [outer(e1, v) for v in vectors]
    projections = [outer(v, v) for v in vectors]
    for v, A, P in zip(vectors, matrices, projections):
        assert sum(x.star() * x for x in v) == 1
        assert adj(P) == P
        assert mm(P, P) == P == mm(adj(A), A)
    total = ms(matrices)
    R = [[one * F(k, 2), zero], [zero, zero]]
    T = ms(projections)
    assert total == R and mm(R, R) == mm(adj(total), total)
    assert T == [[one * F(k, 4), zero], [zero, one * F(3 * k, 4)]]
    gap = sub(R, T)
    assert gap == [[one * F(k, 4), zero], [zero, one * F(-3 * k, 4)]]
    variance = scale(F(1, 2), ms(mm(adj(sub(A, B)), sub(A, B)) for A in matrices for B in matrices))
    assert variance == sub(scale(k, ms(mm(adj(A), A) for A in matrices)), mm(adj(total), total))
    shifted = sub(R, scale(F(k, 2), I))
    correction = ms(sub(P, mm(P, P)) for P in projections)
    lhs = scale(k, sub(add(scale(F(k, 4), I), T), R))
    rhs = add(add(scale(k, correction), variance), mm(shifted, shifted))
    assert lhs == rhs
    records.append({'k': k, 'quotient_dimension_over_Q_at_most': 2 * d, 'exact_root_relations': True, 'all_unit_vector_inner_products': True, 'all_Gram_projection_identities': True, 'actual_matrix_sum_and_modulus_candidates': True, 'exact_gap_diagonal': [str(F(k, 4)), str(F(-3 * k, 4))], 'ordered_pair_identity_and_positive_decomposition': True})

result = {'status': 'PASS: exact finite transcription diagnostics only', 'arithmetic': 'fractions.Fraction and the displayed polynomial quotient; no floating arithmetic', 'cases': records, 'limitations': 'No universal k proof, analytic exponential evaluation, CFC/PSD theorem, or operator-norm theorem is supplied by this script. Those remain the eight mandatory Lean obligations.'}
out = Path(__file__).with_name('algebra-result.json')
out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
