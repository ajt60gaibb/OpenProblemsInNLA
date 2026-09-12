#!/usr/bin/env python3
"""Exact finite audit of TR-07's analytic proof (Python standard library only).

These are identity checks and finite examples, NOT a universal proof certificate.
No test relies on floating-point eigenvalues. Explicit checks remain active under
python -O. The analytic manuscript proves the dimension-uniform theorem.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
import json
from math import comb, prod
from pathlib import Path
import random
from typing import Sequence

Matrix = list[list[F]]
Vector = tuple[int, ...]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def zero(n: int, m: int | None = None) -> Matrix:
    return [[F(0) for _ in range(n if m is None else m)] for _ in range(n)]


def eye(n: int) -> Matrix:
    return [[F(i == j) for j in range(n)] for i in range(n)]


def trans(a: Matrix) -> Matrix:
    return [list(row) for row in zip(*a)]


def add(a: Matrix, b: Matrix) -> Matrix:
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def scale(a: Matrix, c: F | int) -> Matrix:
    return [[c * x for x in row] for row in a]


def mul(a: Matrix, b: Matrix) -> Matrix:
    if not a:
        return []
    bt = trans(b)
    return [[sum((x * y for x, y in zip(row, col)), F(0)) for col in bt] for row in a]


def power(a: Matrix, n: int) -> Matrix:
    out = eye(len(a))
    while n:
        if n & 1:
            out = mul(out, a)
        a = mul(a, a)
        n //= 2
    return out


def dot(a: Sequence, b: Sequence) -> F:
    return sum((F(x) * F(y) for x, y in zip(a, b)), F(0))


def mv(a: Matrix, v: Sequence) -> tuple[F, ...]:
    return tuple(dot(row, v) for row in a)


def trace(a: Matrix) -> F:
    return sum((a[i][i] for i in range(len(a))), F(0))


def inverse(a: Matrix) -> Matrix:
    n = len(a)
    z = [list(row) + erow for row, erow in zip(a, eye(n))]
    for j in range(n):
        pivot = next((i for i in range(j, n) if z[i][j]), None)
        require(pivot is not None, 'Singular matrix in exact inverse')
        z[j], z[pivot] = z[pivot], z[j]
        c = z[j][j]
        z[j] = [x / c for x in z[j]]
        for i in range(n):
            if i != j:
                c = z[i][j]
                z[i] = [x - c * y for x, y in zip(z[i], z[j])]
    return [row[n:] for row in z]


def inertia(a: Matrix) -> tuple[int, int, int]:
    """Negative, zero, positive counts, by exact 1x1/2x2 congruences."""
    a = [list(map(F, row)) for row in a]
    require(a == trans(a), 'Inertia input is not symmetric')
    neg = null = pos = 0
    while a:
        n = len(a)
        pivot = next((i for i in range(n) if a[i][i]), None)
        if pivot is not None:
            order = [pivot] + [i for i in range(n) if i != pivot]
            a = [[a[i][j] for j in order] for i in order]
            d = a[0][0]
            neg += d < 0
            pos += d > 0
            a = [[a[i][j] - a[i][0] * a[0][j] / d
                  for j in range(1, n)] for i in range(1, n)]
            continue
        off = next(((i, j) for i in range(n) for j in range(i + 1, n) if a[i][j]), None)
        if off is None:
            null += n
            break
        i, j = off
        order = [i, j] + [z for z in range(n) if z not in (i, j)]
        a = [[a[u][v] for v in order] for u in order]
        d = a[0][1]  # block [[0,d],[d,0]] has inertia (1,0,1)
        neg += 1
        pos += 1
        a = [[a[u][v] - (a[u][0] * a[1][v] + a[u][1] * a[0][v]) / d
              for v in range(2, n)] for u in range(2, n)]
    return neg, null, pos


def gram(columns: Sequence[Sequence]) -> Matrix:
    return [[dot(v, w) for w in columns] for v in columns]


def count(columns: Sequence[Sequence], threshold_squared: F) -> int:
    g = gram(columns)
    for i in range(len(g)):
        g[i][i] -= threshold_squared
    neg, null, _ = inertia(g)
    return neg + null


def prune(vectors: Sequence[Vector], weights: Sequence[F]) -> tuple[list[int], list[int]]:
    k = len(vectors[0])
    live = list(range(len(vectors)))
    charged: list[int] = []
    while True:
        bad = next((i for i in range(k)
                    if 0 < sum((weights[j] for j in live if vectors[j][i]), F(0)) < F(1, 4 * k)), None)
        if bad is None:
            break
        charged.append(bad)
        live = [j for j in live if not vectors[j][bad]]
    require(len(charged) == len(set(charged)), 'Coordinate charged twice')
    require(sum((weights[j] for j in live), F(0)) >= F(3, 4), 'Excess pruning loss')
    for i in range(k):
        mass = sum((weights[j] for j in live if vectors[j][i]), F(0))
        require(mass == 0 or mass >= F(1, 4 * k), 'Raw incidence lower bound failed')
    return live, charged


def covariance(vectors: Sequence[Vector], weights: Sequence[F]):
    k = len(vectors[0])
    sig = [[sum((p * v[i] * v[j] for v, p in zip(vectors, weights)), F(0))
            for j in range(k)] for i in range(k)]
    require(all(sig[i][i] > 0 for i in range(k)), 'Inactive coordinate passed to covariance')
    d = [[sig[i][i] if i == j else F(0) for j in range(k)] for i in range(k)]
    t = [[sig[i][j] / sig[j][j] for j in range(k)] for i in range(k)]
    return sig, d, t


def test_inertia() -> dict:
    cases = [([], (0, 0, 0)), ([[0]], (0, 1, 0)),
             ([[0, 2], [2, 0]], (1, 0, 1)),
             ([[1, 1], [1, 1]], (0, 1, 1)),
             ([[-1, 0], [0, 3]], (1, 0, 1))]
    for a, expected in cases:
        require(inertia(a) == expected, 'Inertia self-test failed')
    rng = random.Random(20260912)
    tests = 0
    for n in range(1, 7):
        for _ in range(8):
            # Unit triangular congruence of a known diagonal form.
            u = [[F(1 if i == j else rng.randint(-3, 3) if i < j else 0)
                  for j in range(n)] for i in range(n)]
            diag = [rng.choice([-2, 0, 3]) for _ in range(n)]
            d = [[F(diag[i] if i == j else 0) for j in range(n)] for i in range(n)]
            expected = (sum(x < 0 for x in diag), sum(x == 0 for x in diag), sum(x > 0 for x in diag))
            require(inertia(mul(trans(u), mul(d, u))) == expected, 'Congruence inertia failed')
            tests += 1
    return {'elementary_cases': len(cases), 'exact_congruence_cases': tests}


def test_pruning() -> dict:
    v = [(1, 1, 0, 0, 0, 0), (0, 0, 1, 1, 0, 0),
         (1, 0, 1, 0, 0, 0), (0, 1, 0, 0, 1, 0)]
    w = [F(90, 100), F(3, 100), F(3, 100), F(4, 100)]
    live, charges = prune(v, w)
    require(live == [0] and len(charges) == 3, 'Cascade example was not exercised')
    rng = random.Random(4172026)
    total = 0
    for k, s in [(3, 1), (4, 2), (5, 3), (6, 2)]:
        allv = []
        for support in combinations(range(k), s):
            for signs in product([-1, 1], repeat=s):
                u = [0] * k
                for i, sign in zip(support, signs):
                    u[i] = sign
                allv.append(tuple(u))
        for _ in range(12):
            vectors = rng.sample(allv, min(10, len(allv)))
            raw = [rng.choice([1, 2, 3, 100, 10000]) for _ in vectors]
            weights = [F(x, sum(raw)) for x in raw]
            prune(vectors, weights)
            total += 1
    return {'cascade_survivor_mass': '9/10', 'cascade_charges': charges,
            'additional_exact_laws': total}


def test_filter_and_paths() -> dict:
    vectors = [(1, 1, 0, 0), (1, -1, 0, 0), (0, 1, 1, 0),
               (0, 0, 1, 1), (1, 0, 0, -1)]
    weights = [F(x, 18) for x in [1, 2, 3, 5, 7]]
    k, s = 4, 2
    sig, d, t = covariance(vectors, weights)
    require(t != trans(t), 'Nonnormality-sensitive example accidentally symmetric')
    require(trace(d) == s, 'trace D mismatch')
    require(inertia(add(scale(d, s), scale(sig, -1)))[0] == 0, 'Covariance domination failed')
    require(mul(t, sig) == mul(sig, trans(t)), 'Covariance intertwining failed')
    h = scale(t, F(1, s))
    residual = add(eye(k), scale(h, -1))
    errors = []
    for L in range(1, 7):
        f = power(residual, L)
        lhs = trace(mul(f, mul(sig, trans(f))))
        direct = sum((p * dot(mv(f, v), mv(f, v)) for v, p in zip(vectors, weights)), F(0))
        require(lhs == direct == trace(mul(power(f, 2), sig)), 'Filter trace identity failed')
        require(lhs <= F(s * s, 2 * L + 1), 'Filter bound failed')
        polynomial = zero(k)
        for j in range(1, L + 1):
            polynomial = add(polynomial, scale(power(h, j), (-1) ** (j + 1) * comb(L, j)))
        require(polynomial == add(eye(k), scale(f, -1)), 'Polynomial identity failed')
        errors.append(str(lhs))

    states = list(dict.fromkeys(vectors + [tuple(-x for x in v) for v in vectors]))
    idx = {v: i for i, v in enumerate(states)}
    P, K = zero(len(states)), zero(len(states))
    # Original law has 1/50 bad mass on an extra disjoint support. Only 49/50
    # belongs to G. Hit probabilities must use original, NOT conditioned, mass.
    g = F(49, 50)
    hit = [1 - (1 - g * d[i][i]) ** 2 for i in range(k)]
    amin = min(hit)
    for aidx, v in enumerate(states):
        for i in range(k):
            if v[i] == 0:
                continue
            for w, mass in zip(vectors, weights):
                if w[i] == 0:
                    continue
                new = tuple(v[i] * w[i] * x for x in w)
                transition = mass / (s * d[i][i])
                P[aidx][idx[new]] += transition
                K[aidx][idx[new]] += hit[i] * transition
        require(sum(P[aidx]) == 1, 'Ideal transition not stochastic')
        mean = tuple(sum((P[aidx][j] * states[j][i] for j in range(len(states))), F(0)) for i in range(k))
        require(mean == mv(h, v), 'Signed transition mean failed')

    # First-hit law, explicitly enumerated using the bad atom as well.
    original_weights = [g * w for w in weights] + [1 - g]
    first_hit_words = 0
    for i in range(k):
        actual = [F(0) for _ in vectors]
        for word in product(range(len(original_weights)), repeat=2):
            mass = prod(original_weights[j] for j in word)
            first_hit_words += 1
            for j in word:
                if j < len(vectors) and vectors[j][i]:
                    actual[j] += mass
                    break
        for j, v in enumerate(vectors):
            expected = hit[i] * weights[j] / d[i][i] if v[i] else 0
            require(actual[j] == expected, 'Direct original-law first-hit identity failed')

    trajectory_atoms = 0
    for L in range(1, 4):
        S = 2 ** L - 1
        Hpoly = add(eye(k), scale(power(residual, L), -1))
        overall_bias = overall_variance = F(0)
        for root, root_mass in zip(vectors, weights):
            # Keep the accumulated polynomial as well as the terminal state:
            # domination is checked on the full reconstruction, not only its mean.
            law = {(idx[root], (0,) * k): F(1)}
            successful = dict(law)
            for j in range(1, L + 1):
                coefficient = (-1) ** (j + 1) * comb(L, j)
                next_law, next_success = defaultdict(F), defaultdict(F)
                for (state, accum), mass in law.items():
                    for z, transition in enumerate(P[state]):
                        if transition:
                            key = (z, tuple(accum[i] + coefficient * states[z][i] for i in range(k)))
                            next_law[key] += mass * transition
                for (state, accum), mass in successful.items():
                    for z, transition in enumerate(K[state]):
                        if transition:
                            key = (z, tuple(accum[i] + coefficient * states[z][i] for i in range(k)))
                            next_success[key] += mass * transition
                law, successful = next_law, next_success
            trajectory_atoms += len(law)
            require(sum(law.values()) == 1, 'Trajectory law mass failed')
            require(all(successful.get(key, F(0)) >= amin ** L * mass
                        for key, mass in law.items()), 'Reconstruction-law domination failed')
            mean = tuple(sum((mass * accum[i] for (_, accum), mass in law.items()), F(0)) for i in range(k))
            require(mean == mv(Hpoly, root), 'Single-trajectory polynomial mean failed')
            second = sum((mass * dot(accum, accum) for (_, accum), mass in law.items()), F(0))
            variance = second - dot(mean, mean)
            require(F(0) <= variance <= s * S * S, 'Trajectory variance bound failed')
            bias = tuple(F(x) - y for x, y in zip(root, mean))
            overall_bias += root_mass * dot(bias, bias)
            overall_variance += root_mass * variance
        for b in (1, 2, 5):
            require(overall_bias + overall_variance / b <= F(s * s, 2 * L + 1) + F(s * S * S, b),
                    'Averaged reconstruction error bound failed')

    # Explicitly expose the conditioning trap: K^2 normalized is not P^2.
    PP, KK = power(P, 2), power(K, 2)
    row_mass = sum(KK[0])
    mismatch = next((j for j in range(len(states)) if KK[0][j] / row_mass != PP[0][j]), None)
    require(mismatch is not None, 'Expected conditioning-bias witness not found')

    # Singular population covariance is also allowed; D still has positive diagonal.
    singular_v = [(1, 1, 0, 0), (0, 0, 1, 1)]
    singular_w = [F(1, 3), F(2, 3)]
    ss, dd, tt = covariance(singular_v, singular_w)
    require(inertia(ss)[1] == 2 and all(dd[i][i] for i in range(4)), 'Singular-covariance example failed')
    for L in range(1, 5):
        f = power(add(eye(4), scale(tt, F(-1, 2))), L)
        require(trace(mul(f, mul(ss, trans(f)))) <= F(4, 2 * L + 1), 'Singular-covariance filter failed')

    return {'filter_powers': 6, 'filter_errors': errors, 'signed_states': len(states),
            'original_law_first_hit_words': first_hit_words,
            'full_reconstruction_atoms_checked': trajectory_atoms,
            'trajectory_lengths': [1, 2, 3], 'averaging_replica_counts': [1, 2, 5],
            'raw_good_mass': str(g), 'minimum_hit_probability': str(amin),
            'conditioning_is_not_ideal_witness': {
                'initial_state': states[0], 'terminal_state': states[mismatch],
                'ideal_probability': str(PP[0][mismatch]),
                'probability_conditional_on_all_hits': str(KK[0][mismatch] / row_mass)},
            'singular_covariance_nullity': 2}


def test_witnesses() -> dict:
    rng = random.Random(72026)
    tests = 0
    smallest_count = 999
    max_coefficient = 0
    k, m, q = 5, 3, 2
    eps, eta = F(1, 4), F(1, 2)
    for factor in (0, 1, 10, 10 ** 6):
        for _ in range(5):
            reservoir = [[F(rng.randint(-2, 2)) for _ in range(q)] for _ in range(k)]
            x = [[F(factor * rng.randint(-2, 2)) for _ in range(m)] for _ in range(q)]
            e = [[eps if i == j else F(0) for j in range(m)] for i in range(k)]
            centers = add(mul(reservoir, x), e)
            a = [cr + rr for cr, rr in zip(centers, reservoir)]
            v = eye(m) + scale(x, -1)
            require(mul(a, v) == e, 'Witness residual is not exact')
            vtv = mul(trans(v), v)
            require(vtv == add(eye(m), mul(trans(x), x)), 'Witness identity block failed')
            require(inertia(add(vtv, scale(eye(m), -1)))[0] == 0, 'Witness lower Gram bound failed')
            compression_trace = trace(mul(inverse(vtv), mul(trans(e), e)))
            require(compression_trace <= m * eps * eps, 'Orthonormalization trace bound failed')
            nsmall = count(trans(a), eta * eta)
            require(2 * nsmall >= m, 'Exact inertia contradicts witness lemma')
            smallest_count = min(smallest_count, nsmall)
            max_coefficient = max(max_coefficient, max(abs(int(z)) for row in x for z in row))
            tests += 1
    return {'exact_cases': tests, 'maximum_coefficient': max_coefficient,
            'minimum_observed_small_eigenvalue_count': smallest_count,
            'threshold_squared': str(eta * eta)}


def test_counts_and_subset_martingale() -> dict:
    vectors = [(1, 1, 0), (1, -1, 0), (1, 0, 1), (1, 0, -1), (0, 1, 1), (0, 1, -1)]
    thresholds = [F(0), F(1, 4), F(1), F(2), F(4)]
    cache: dict[tuple, int] = {}

    def f(word, threshold):
        key = tuple(sorted(word)), threshold
        if key not in cache:
            cache[key] = count([vectors[i] for i in key[0]], threshold)
        return cache[key]

    replacements = deletions = 0
    for r in range(1, 4):
        for word in product(range(6), repeat=r):
            for threshold in thresholds:
                val = f(word, threshold)
                for j in range(r):
                    reduced = word[:j] + word[j + 1:]
                    require(f(reduced, threshold) <= val <= f(reduced, threshold) + 1,
                            'Exact deletion interlacing failed')
                    deletions += 1
                    for new in range(6):
                        changed = word[:j] + (new,) + word[j + 1:]
                        require(abs(val - f(changed, threshold)) <= 1, 'One-Lipschitz count failed')
                        replacements += 1

    prefix_checks = expectation_comparisons = 0
    for r in range(1, 4):
        for threshold in thresholds:
            iid = sum((f(word, threshold) for word in product(range(6), repeat=r)), F(0)) / (6 ** r)
            wor = sum((f(word, threshold) for word in combinations(range(6), r)), F(0)) / comb(6, r)
            require(wor >= iid - F(r * (r - 1), 12), 'Exact expectation comparison failed')
            expectation_comparisons += 1
            for j in range(r):
                for prefix in combinations(range(6), j):
                    unused = [x for x in range(6) if x not in prefix]
                    conditional_means = []
                    for a in unused:
                        remaining = [x for x in unused if x != a]
                        completions = list(combinations(remaining, r - j - 1))
                        mean = sum((f(prefix + (a,) + rest, threshold) for rest in completions), F(0)) / len(completions)
                        conditional_means.append(mean)
                    require(max(conditional_means) - min(conditional_means) <= 1,
                            'Doob increment range exceeds one')
                    prefix_checks += 1
    return {'exact_gram_matrices_and_thresholds': len(cache),
            'column_replacement_comparisons': replacements,
            'column_deletion_comparisons': deletions,
            'without_replacement_prefix_range_checks': prefix_checks,
            'iid_vs_without_replacement_expectation_checks': expectation_comparisons}


def test_couplings() -> dict:
    cases = []
    for n in range(2, 8):
        for r in range(1, min(n, 4) + 1):
            law = {((), 0): F(1)}
            for _ in range(r):
                nxt = defaultdict(F)
                for (history, h), mass in law.items():
                    unused = [i for i in range(n) if i not in history]
                    for j in range(n):
                        if j not in history:
                            nxt[(history + (j,), h)] += mass / n
                        else:
                            for i in unused:
                                nxt[(history + (i,), h + 1)] += mass / (n * len(unused))
                law = nxt
            marginal = defaultdict(F)
            for (history, h), mass in law.items():
                marginal[history] += mass
            expected_probability = F(1, prod(n - i for i in range(r)))
            require(sum(law.values()) == 1, 'Coupling lost probability mass')
            require(len(marginal) == 1 / expected_probability, 'Wrong ordered sample coverage')
            require(all(p == expected_probability for p in marginal.values()), 'Coupling is not uniform')
            eh = sum((h * mass for (_, h), mass in law.items()), F(0))
            require(eh == F(r * (r - 1), 2 * n), 'Wrong expected collision replacements')
            cases.append({'n': n, 'r': r, 'ordered_samples': len(marginal), 'expected_changes': str(eh)})
    return {'number_of_cases': len(cases), 'cases': cases}


def test_constant_inequalities() -> dict:
    count_ceilings = count_hit_bounds = 0
    # Do NOT try to expand a**J0 for physically enormous J0. Only exact local
    # inequalities are checked; finiteness/positivity follow analytically.
    for s in (1, 2, 3):
        for eps in (F(1), F(2), F(4), F(8)):
            x = 4 * s * s / (eps * eps)
            L = (x.numerator + x.denominator - 1) // x.denominator
            S = 2 ** L - 1
            x = 8 * s * S * S / (eps * eps)
            b = (x.numerator + x.denominator - 1) // x.denominator
            require(F(s * s, 2 * L + 1) + F(s * S * S, b) <= eps * eps / 4,
                    'Ceiling constants do not give desired mean-square error')
            count_ceilings += 1
    for J0 in range(1, 10):
        for beta in (F(1), F(1, 2), F(1, 10)):
            a = beta / (16 * J0 + beta)
            for k in range(max(2, (4 * J0 * beta.denominator + beta.numerator - 1) // beta.numerator), 400):
                r = max(4 * J0, (beta.numerator * k + beta.denominator - 1) // beta.denominator)
                if r > k:
                    continue
                m = r // 2
                ell = (r - m) // J0
                require(ell >= F(r, 4 * J0), 'Reservoir chunk floor bound failed')
                raw_p = F(1, 4 * k)
                hit = 1 - (1 - raw_p) ** ell
                require(hit >= (ell * raw_p) / (1 + ell * raw_p) >= a, 'Uniform hit bound failed')
                count_hit_bounds += 1
    return {'ceiling_error_bounds': count_ceilings, 'exact_hit_and_floor_bounds': count_hit_bounds}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('verification_report.json'))
    args = parser.parse_args()
    report = {
        'status': 'PASS',
        'scope': 'Exact finite identities and examples, NOT a universal proof certificate.',
        'arithmetic': 'Python standard-library Fraction; exact symmetric inertia; no floating point.',
        'inertia_selftests': test_inertia(),
        'pruning': test_pruning(),
        'covariance_and_conditional_trajectories': test_filter_and_paths(),
        'simultaneous_witnesses': test_witnesses(),
        'count_lipschitz_and_martingale': test_counts_and_subset_martingale(),
        'coupling': test_couplings(),
        'constants': test_constant_inequalities(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
