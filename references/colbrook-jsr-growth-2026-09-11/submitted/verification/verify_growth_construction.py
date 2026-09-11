#!/usr/bin/env python3
"""Exact identities and supplementary diagnostics for proposed solution MF-12.

The manuscript proves the all-words, all-length result. Numerical samples do not.
Dependencies: NumPy, SymPy (which includes mpmath). Python 3.10+.
"""
from __future__ import annotations

import argparse
import datetime as dt
from fractions import Fraction
import json
import math
from pathlib import Path
from typing import Any

import mpmath as mp
import numpy as np
import sympy as sp

if not __debug__:
    raise RuntimeError("Run this verifier without -O: assertions are part of the checks")

U = sp.Matrix([[1, -1, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1]])
V = sp.Matrix([[1, 0], [0, 0], [1, 0], [0, 0], [0, 1], [0, 1]])
P = V * U


def symbolic_checks() -> dict[str, Any]:
    q = sp.Symbol('q', integer=True, nonnegative=True)
    t, lam, mu = sp.symbols('t lambda mu', positive=True)
    jordan = t * sp.Matrix([[1, 1], [0, 1]])
    candidate_power = t**q * sp.Matrix([[1, q], [0, 1]])
    assert candidate_power.subs(q, 0) == sp.eye(2)
    assert sp.simplify(jordan * candidate_power - candidate_power.subs(q, q + 1)) == sp.zeros(2)
    aq = sp.diag(1, candidate_power.subs(t, lam), candidate_power.subs(t, mu), 1)
    assert sp.simplify(U * aq * V - sp.Matrix([[1 - q * lam**q, q * mu**q], [0, 1]])) == sp.zeros(2)
    assert U * V == sp.eye(2)
    assert P * P == P
    assert U * U.T == sp.diag(3, 1)
    assert V.T * V == 2 * sp.eye(2)
    return {
        'arithmetic': 'exact symbolic SymPy',
        'jordan_base_case_and_induction_identity': True,
        'compressed_power_identity_symbolic_q': True,
        'UV_identity': True, 'projection_identity': True,
        'U_and_V_norm_gram_identities': True,
    }


def numerical_pair(lam: float, mu: float) -> tuple[np.ndarray, np.ndarray]:
    if not 0 < lam <= 0.25 or not lam < mu < 1:
        raise ValueError('require 0 < lambda <= 1/4 and lambda < mu < 1')
    a = np.diag([1.0, lam, lam, mu, mu, 1.0])
    a[1, 2] = lam
    a[3, 4] = mu
    return a, np.array(P, dtype=float)


def exact_log_floor(n: int, lam: Fraction) -> int:
    """Largest q with lambda**(-q) <= n, corrected using integer arithmetic."""
    if n < 1 or not 0 < lam < 1:
        raise ValueError('require n >= 1 and 0 < lambda < 1')
    numerator, denominator = lam.numerator, lam.denominator
    q = max(0, int(math.log(n) / math.log(denominator / numerator)))
    while denominator**(q + 1) <= n * numerator**(q + 1):
        q += 1
    while denominator**q > n * numerator**q:
        q -= 1
    return q


def parameters() -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    for value in ['0.001', '0.05', '0.1', '0.25', '0.5', '0.75', '0.9', '0.95', '0.999']:
        result.append({'label': 'real-alpha-' + value, 'lambda': Fraction(1, 4), 'alpha': mp.mpf(value)})
    for denominator in range(2, 10):
        for numerator in range(1, denominator):
            result.append({
                'label': f'dyadic-alpha-{numerator}/{denominator}',
                'lambda': Fraction(1, 2**denominator),
                'alpha': mp.mpf(numerator) / denominator,
                'exact_mu': Fraction(1, 2**(denominator - numerator)),
            })
    result.append({
        'label': 'rational-pair-irrational-alpha', 'lambda': Fraction(1, 4),
        'exact_mu': Fraction(1, 3), 'alpha': 1 - mp.log(3) / mp.log(4),
    })
    return result


def run(trials: int, seed: int) -> dict[str, Any]:
    if trials < 1:
        raise ValueError('trials must be positive')
    started_utc = dt.datetime.now(dt.timezone.utc).isoformat()
    mp.mp.dps = 100
    exact = symbolic_checks()
    rng = np.random.default_rng(seed)
    records = []
    lengths = list(range(1, 200)) + [10**j for j in range(3, 16)] + [10**20, 10**40, 10**80, 10**160]
    float_v = np.array(V, dtype=float)
    float_u = np.array(U, dtype=float)
    total_lower_checks = 0
    for parameter in parameters():
        fraction_lam = parameter['lambda']
        lam = mp.mpf(fraction_lam.numerator) / fraction_lam.denominator
        alpha = parameter['alpha']
        mu = lam**(1 - alpha)
        if 'exact_mu' in parameter:
            value = parameter['exact_mu']
            rational_mu = mp.mpf(value.numerator) / value.denominator
            assert mp.almosteq(mu, rational_mu)
            mu = rational_mu
        a, p = numerical_pair(float(lam), float(mu))
        lower_constant = -mp.expm1(-mp.mpf(1) / 4) * lam**alpha / mp.sqrt(2)
        upper_constant = 2 * mp.sqrt(6) / (1 - mu)**2
        max_middle_ratio = 0.0
        max_telescope_residual = 0.0
        max_factorization_error = 0.0
        max_full_word_ratio = 0.0
        max_word_length = 0
        powers = [np.linalg.matrix_power(a, q) for q in range(101)]
        for _ in range(trials):
            qs = rng.integers(0, 101, size=int(rng.integers(0, 40)))
            middle = np.eye(2)
            loss_mass = 0.0
            for q in qs:
                ell = int(q) * float(lam)**int(q)
                gain = int(q) * float(mu)**int(q)
                middle = np.array([[1 - ell, gain], [0.0, 1.0]]) @ middle
                loss_mass = ell + (1 - ell) * loss_mass
            budget = int(np.sum(qs))
            max_telescope_residual = max(max_telescope_residual, abs(loss_mass - (1 - middle[0, 0])))
            if budget:
                ratio = float(middle[0, 1] / budget**float(alpha))
                max_middle_ratio = max(max_middle_ratio, ratio)
                assert ratio <= 1 + 2e-12
            else:
                assert middle[0, 1] == 0
            # Multiply the full six-dimensional word, not only its compression.
            # W = A^r P A^q_k P ... A^q_1 P A^t, including empty middle lists.
            r, t = (int(x) for x in rng.integers(0, 101, size=2))
            word = p @ powers[t]
            for q in qs:
                word = p @ powers[int(q)] @ word
            word = powers[r] @ word
            factored = powers[r] @ float_v @ middle @ float_u @ powers[t]
            observed_norm = float(np.linalg.norm(word, 2))
            factorization_error = float(np.linalg.norm(word - factored, 2)) / max(1.0, observed_norm)
            assert factorization_error <= 2e-11
            max_factorization_error = max(max_factorization_error, factorization_error)
            length = r + t + budget + len(qs) + 1
            max_word_length = max(max_word_length, length)
            word_ratio = observed_norm / (float(upper_constant) * length**float(alpha))
            assert word_ratio <= 1 + 2e-12
            max_full_word_ratio = max(max_full_word_ratio, word_ratio)
        # Pure A words and consecutive P words are also explicitly covered.
        for length in (1, 2, 10, 100):
            for word in (powers[length], np.linalg.matrix_power(p, length)):
                assert np.linalg.norm(word, 2) <= float(upper_constant) * length**float(alpha) * (1 + 2e-12)
        smallest_lower_factor = mp.inf
        examples = []
        for n in lengths:
            q = exact_log_floor(n, fraction_lam)
            if q == 0:
                assert lower_constant * mp.mpf(n)**alpha < 1
                total_lower_checks += 1
                continue
            k, remainder = divmod(n, q + 1)
            ell = q * lam**q
            gain = q * mu**q
            assert k * ell >= mp.mpf(1) / 4
            z = (gain / ell) * -mp.expm1(k * mp.log1p(-ell))
            normalized = z / (mp.sqrt(2) * mp.mpf(n)**alpha)
            factor = normalized / lower_constant
            smallest_lower_factor = min(smallest_lower_factor, factor)
            assert factor >= 1 - mp.mpf('1e-80')
            if n <= 100:
                word = np.linalg.matrix_power(a, remainder) @ np.linalg.matrix_power(p @ np.linalg.matrix_power(a, q), k)
                observed = (word @ float_v[:, 1])[0]
                assert np.isclose(observed, float(z), rtol=1e-10, atol=1e-10)
            if n in [10**20, 10**80, 10**160]:
                examples.append({'n': str(n), 'q': q, 'k': str(k), 'normalized_constructed_lower': mp.nstr(normalized, 18)})
            total_lower_checks += 1
        records.append({
            'label': parameter['label'], 'lambda': str(fraction_lam),
            'mu': mp.nstr(mu, 20), 'alpha': mp.nstr(alpha, 20),
            'lower_constant': mp.nstr(lower_constant, 20),
            'upper_constant': mp.nstr(upper_constant, 20),
            'random_gap_lists': trials,
            'random_full_words': trials,
            'maximum_full_word_length': max_word_length,
            'maximum_full_word_factorization_relative_error': max_factorization_error,
            'maximum_full_word_over_proved_upper_bound': max_full_word_ratio,
            'maximum_middle_over_budget_alpha': max_middle_ratio,
            'maximum_telescope_residual': max_telescope_residual,
            'minimum_constructed_lower_over_proved_lower': mp.nstr(smallest_lower_factor, 20),
            'large_length_examples': examples,
        })
        print(parameter['label'], 'passed', flush=True)
    # Tensor and integer-exponent checks use small explicit products.
    tensor_checks = 0
    a, p = numerical_pair(0.25, 0.5)
    for m in range(1, 5):
        jordan = np.eye(m + 1) + np.eye(m + 1, k=1)
        for n in range(1, 11):
            base = np.eye(6)
            lifted = np.eye(6 * (m + 1))
            for bit in rng.integers(0, 2, n):
                factor = (a, p)[int(bit)]
                base = factor @ base
                lifted = np.kron(factor, jordan) @ lifted
            jp = np.linalg.matrix_power(jordan, n)
            assert np.allclose(lifted, np.kron(base, jp), rtol=1e-12, atol=1e-12)
            assert np.isclose(np.linalg.norm(lifted, 2), np.linalg.norm(base, 2) * np.linalg.norm(jp, 2), rtol=1e-12)
            assert (n / m)**m <= np.linalg.norm(jp, 2) * (1 + 1e-12)
            assert np.linalg.norm(jp, 2) <= (m + 1) * n**m * (1 + 1e-12)
            tensor_checks += 1
    return {
        'status': 'all checks passed; numerical diagnostics are not a substitute for the proof',
        'seed': seed, 'mpmath_decimal_digits': mp.mp.dps,
        'started_utc': started_utc,
        'completed_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
        'symbolic': exact,
        'parameter_sets': len(records), 'random_gap_lists': len(records) * trials,
        'random_full_words': len(records) * trials,
        'pure_A_and_P_word_checks': len(records) * 8,
        'lower_bound_lengths_checked': total_lower_checks, 'tensor_checks': tensor_checks,
        'records': records,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--random-trials', type=int, default=1000, help='per parameter set')
    parser.add_argument('--seed', type=int, default=26091112)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('growth_construction_checks.json'))
    args = parser.parse_args()
    result = run(args.random_trials, args.seed)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False) + '\n', encoding='utf-8')
    print('ALL CHECKS PASSED:', result['random_gap_lists'], 'gap lists and full words,', result['lower_bound_lengths_checked'], 'lower bounds,', result['tensor_checks'], 'tensor products')
    print('Output:', args.output)


if __name__ == '__main__':
    main()
