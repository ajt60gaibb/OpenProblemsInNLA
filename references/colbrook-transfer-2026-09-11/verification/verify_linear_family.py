"""Deterministic-seed algebraic and regression tests; not a replacement for proof."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
from linear_family_sketch import (make_plan, solve_from_oracles,
                                  orthonormalize_family, exact_second_moment)

ROOT = Path(__file__).resolve().parents[1]
rng = np.random.default_rng(20260911)
records = []

# Check the matrix second-moment bound across diverse small instances.
max_ratio = 0.0
for trial in range(80):
    q, m, n = 5, 7, 6
    raw = rng.standard_normal((q, m, n))
    raw[:, :2, :] *= 10.0**rng.uniform(0, 2)
    p = orthonormalize_family(raw)
    rsum = np.einsum('imn,ikn->mk', p, p)
    w, v = np.linalg.eigh(rsum)
    r = trial % 4
    u = v[:, m-r:] if r else np.empty((m, 0))
    t = p - np.einsum('mr,irn->imn', u, np.einsum('mr,imn->irn', u, p))
    leverage = float(np.linalg.eigvalsh(np.einsum('imn,ikn->mk', t, t))[-1])
    variance = exact_second_moment(t)
    largest = float(np.linalg.eigvalsh(variance)[-1])
    smallest = float(np.linalg.eigvalsh(variance)[0])
    assert smallest >= -1e-10
    assert largest <= 2*leverage + 1e-10
    max_ratio = max(max_ratio, largest/(2*leverage))
records.append({'test': 'exact_Gaussian_fourth_moment_bound', 'instances': 80,
                'maximum_ratio_to_bound': max_ratio, 'passed': True})

# Exact common-row family: a single left query gives its exact Frobenius projection.
n, q = 40, 24
p = np.zeros((q, n, n))
p[np.arange(q), 0, np.arange(q)] = 1
A = rng.standard_normal((n, n))
plan = make_plan(p, seed=1)
B, c, info = solve_from_oracles(plan, lambda g: A@g, lambda u: A.T@u)
Bstar = np.einsum('i,imn->mn', np.einsum('imn,mn->i', plan.basis, A), plan.basis)
assert plan.query_count == 1
assert np.linalg.norm(B-Bstar) < 1e-10
records.append({'test': 'common_row_exact_projection', **info, 'passed': True})

# Practical sample sizes exercise the randomized, not merely exact, branch.
# These are intentionally below the conservative theorem constants.
trial_records = []
for family in ('dense', 'diagonal', 'mixed'):
    n, q = 32, 20
    raw = rng.standard_normal((q, n, n))
    if family == 'diagonal':
        raw[:] = 0
        raw[np.arange(q), np.arange(q), np.arange(q)] = 1
    elif family == 'mixed':
        raw[:, :2, :] *= 30
    p = orthonormalize_family(raw)
    for trial in range(100):
        coefficients = rng.standard_normal(q)
        Bstar = np.einsum('i,imn->mn', coefficients, p)
        E = rng.standard_normal((n, n))
        E -= np.einsum('i,imn->mn', np.einsum('imn,mn->i', p, E), p)
        E /= np.linalg.norm(E)
        A = Bstar + E
        plan = make_plan(p, seed=trial+1000,
                         practical_rank=2 if family == 'mixed' else 0,
                         practical_samples=24)
        B, c, info = solve_from_oracles(plan, lambda g: A@g, lambda u: A.T@u)
        squared_error = float(np.linalg.norm(A-B)**2)
        decomposition_error = abs(squared_error-(1+np.linalg.norm(B-Bstar)**2))
        assert decomposition_error < 1e-9
        trial_records.append({'family': family, 'trial': trial,
                              'squared_relative_error': squared_error,
                              'minimum_gram_eigenvalue': info['minimum_gram_eigenvalue']})
records.append({'test': 'practical_randomized_regression', 'instances': 300,
                'theorem_sample_sizes_used': False,
                'maximum_squared_relative_error': max(x['squared_relative_error'] for x in trial_records),
                'maximum_decomposition_error_tolerance': 1e-9, 'passed': True})

# Zero residual: exact recovery from a well-conditioned sketch.
p = orthonormalize_family(rng.standard_normal((12, 18, 18)))
A = np.einsum('i,imn->mn', rng.standard_normal(12), p)
plan = make_plan(p, seed=5, practical_rank=0, practical_samples=12)
B, _, info = solve_from_oracles(plan, lambda g: A@g, lambda u: A.T@u)
assert info['minimum_gram_eigenvalue'] > .5
assert np.linalg.norm(A-B) < 1e-11
records.append({'test': 'zero_residual_exact_recovery', **info, 'passed': True})

output = {'seed': 20260911, 'tests': records, 'practical_trials': trial_records,
          'all_passed': True,
          'caveat': 'Floating-point checks are supporting evidence only; the manuscript contains the proof.'}
(ROOT/'results'/'linear_family_verification.json').write_text(json.dumps(output, indent=2))
print(json.dumps({'all_passed': True, 'tests': records}, indent=2))
