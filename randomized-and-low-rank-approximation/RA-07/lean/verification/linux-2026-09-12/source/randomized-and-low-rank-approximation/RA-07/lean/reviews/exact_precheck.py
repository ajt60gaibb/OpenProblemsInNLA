"""Supplementary finite exact statement diagnostics; never a universal proof."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json

def product(values):
    answer = F(1)
    for value in values:
        answer *= value
    return answer

def elementary(values, j):
    return sum((product(c) for c in combinations(values, j)), F(0))

def product_coefficients(values):
    coefficients = [F(1)]
    for value in values:
        coefficients = ([coefficients[0]] +
            [coefficients[k] + value * coefficients[k - 1]
             for k in range(1, len(coefficients))] + [value * coefficients[-1]])
    return coefficients

def derivative(coefficients):
    return [F(k) * coefficients[k] for k in range(1, len(coefficients))] or [F(0)]

rows = []
for n in range(3, 8):
    for values in [[F(7, 5)] * n, [F(i + 1) for i in range(n)],
                   [F(1, 10) if i % 2 else F(11, 3) for i in range(n)]]:
        e = [elementary(values, j) for j in range(n + 2)]
        coefficients = product_coefficients(values)
        assert coefficients == e[:-1] and e[-1] == 0
        assert all(value > 0 for value in e[:-1])
        ratios = [F(j + 1) * e[j + 1] / e[j] for j in range(n + 1)]
        current, factorial = coefficients, 1
        for j in range(n + 2):
            if j:
                factorial *= j
            assert current[0] == factorial * e[j]
            current = derivative(current)
        gaps = [ratios[j - 1] - 2 * ratios[j] + ratios[j + 1] for j in range(2, n)]
        assert all(gap >= 0 for gap in gaps)
        if len(set(values)) == 1:
            assert all(gap == 0 for gap in gaps)
        rows.append({'lambda': values, 'e': e, 'F': ratios,
                     'canonical_second_differences': gaps})

power_checks = []
for m in range(2, 8):
    mu = [F(i + 1, 3) for i in range(m)]
    sums = [sum(value ** r for value in mu) for r in [1, 2, 3]]
    gap = sum(a * b * (a - b) ** 2 for a, b in combinations(mu, 2))
    denominator = sums[0] * (sums[0] ** 2 - sums[1])
    assert sums[0] * sums[2] - sums[1] ** 2 == gap
    assert gap >= 0 and denominator > 0
    power_checks.append({'m': m, 'sums': sums, 'pair_gap': gap, 'denominator': denominator})

assert rows[1]['canonical_second_differences'] == [F(13, 33)]
s1, s2, s3 = F(11, 3), F(67, 9), F(440, 27)
assert 2 * (s1 * s3 - s2 * s2) / (s1 * (s1 * s1 - s2)) == F(13, 33)
result = {'scope': 'Supplementary exact finite diagnostics only, not a universal proof or Lean certificate',
          'tuples': rows, 'power_sum_checks': power_checks,
          'degree_two_example': {'lambda': [1, 2, 3], 'Q_coefficients': [6, 22, 18],
                                 'sums': [s1, s2, s3], 'second_difference': F(13, 33)},
          'all_checks_pass': True}
Path(__file__).with_name('exact-precheck.json').write_text(json.dumps(result, indent=2, default=str) + '\n')
print('PASS: 15 tuples, exact subset/product/derivative identities, endpoint and all-equal checks, six finite pair certificates.')
