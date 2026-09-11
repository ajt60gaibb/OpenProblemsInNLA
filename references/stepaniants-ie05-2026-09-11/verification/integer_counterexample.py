"""Independent exact rational certificate for a possible IE-05 counterexample."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json


def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), F(0))


def certificate(perturbed):
    n = 8
    lower = [[F(int(i == j)) if i <= j else F(-1)
              for j in range(n)] for i in range(n)]
    if perturbed:
        lower[7][1] = F(0)
    cols = []
    norms = []
    for j in range(n):
        original = [lower[i][j] for i in range(n)]
        col = original[:]
        for previous, norm in zip(cols, norms):
            coefficient = dot(previous, original) / norm
            col = [x - coefficient * y for x, y in zip(col, previous)]
        h = dot(col, col)
        assert h > 0
        assert all(dot(col, previous) == 0 for previous in cols)
        assert dot(col, original) == h
        cols.append(col)
        norms.append(h)
    vectors = [[cols[j][i] for j in range(n)] for i in range(n)]
    # Q_ij = vectors_ij / sqrt(norms_j). Exact orthogonality was
    # checked above; Gram-Schmidt proves L=QR with positive R diagonal.
    initial = max((vectors[i][j] ** 2 / norms[j], i + 1, j + 1)
                  for i in range(n) for j in range(n))
    active = [row[:] for row in vectors]
    stage_maxima = []
    multipliers = []
    for k in range(n):
        pivot = active[k][k]
        assert pivot == 1
        # A positive column scaling does not alter this test or ratios.
        assert all(abs(active[i][k]) <= abs(pivot) for i in range(k, n))
        val, row, col = max((active[i][j] ** 2 / norms[j], i + 1, j + 1)
                            for i in range(k, n) for j in range(k, n))
        stage_maxima.append({'stage': k + 1, 'squared_entry': val,
                             'row': row, 'column': col})
        for i in range(k + 1, n):
            multiplier = active[i][k] / pivot
            assert multiplier == lower[i][k]
            multipliers.append({'pivot': k + 1, 'row': i + 1,
                                'multiplier': multiplier})
            for j in range(k + 1, n):
                active[i][j] -= multiplier * active[k][j]
            active[i][k] = F(0)
    best = max(stage_maxima, key=lambda e: e['squared_entry'])
    return {'perturbed': perturbed, 'lower': lower, 'rational_columns': cols,
            'squared_column_norms': norms, 'squared_input_maximum': initial[0],
            'input_maximum_row_column': list(initial[1:]),
            'stage_maxima': stage_maxima, 'multipliers': multipliers,
            'squared_largest_active_entry': best['squared_entry'],
            'largest_active_entry_location': {k: best[k] for k in ['stage', 'row', 'column']},
            'squared_growth': best['squared_entry'] / initial[0]}


def encode(value):
    if isinstance(value, F):
        return str(value)
    raise TypeError(type(value))


original = certificate(False)
changed = certificate(True)
separator = F(167, 2)
assert original['squared_growth'] < separator ** 2 < changed['squared_growth']
gap = changed['squared_growth'] - original['squared_growth']
assert gap > 0
report = {'result': 'PASS: strict IE-05 counterexample at n=8',
          'arithmetic': 'fractions.Fraction only; no floating-point decisions',
          'separator': separator, 'squared_growth_gap': gap,
          'original': original, 'perturbed': changed}
output = Path(__file__).with_suffix('.json')
output.write_text(json.dumps(report, default=encode, indent=2) + '\n')
print(json.dumps({key: report[key] for key in ['result', 'separator', 'squared_growth_gap']},
                 default=encode, indent=2))
for title, item in [('candidate', original), ('counterexample', changed)]:
    print(title, 'growth squared:', item['squared_growth'])
    print(title, 'locations:', item['input_maximum_row_column'], item['largest_active_entry_location'])
print('certificate SHA256:', hashlib.sha256(output.read_bytes()).hexdigest())
