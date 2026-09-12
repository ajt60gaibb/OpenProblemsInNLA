"""Independent exact diagnostic from the manuscript's one-based tensor entries.
No sampled eigenvalues, numerical roots, or inference of universal truth.
"""
from collections import defaultdict
from itertools import product
from math import prod
from pathlib import Path
import json

generators = [2, 0, 1, 0, 2, 0, -1]
rows = []
for i in range(1, 4):
    coefficients = defaultdict(int)
    for j, k in product(range(1, 4), repeat=2):
        exponent = tuple((j == a) + (k == a) for a in range(1, 4))
        coefficients[exponent] += generators[i + j + k - 3]
    rows.append({key: value for key, value in coefficients.items() if value})
expected = [{(2,0,0): 2, (0,2,0): 1, (1,0,1): 2, (0,0,2): 2},
            {(1,1,0): 2, (0,1,1): 4},
            {(2,0,0): 1, (0,2,0): 2, (1,0,1): 4, (0,0,2): -1}]
assert rows == expected
# Independently expand the first slice's four square summands.
square_sum = {(2,0,0): 2, (0,2,0): 1, (1,0,1): 2, (0,0,2): 2}
assert rows[0] == square_sum

upper, survivors = [], []
for i in range(1, 3):
    total = 0
    surviving = []
    for contracted in product(range(1, 3), repeat=5):
        factor = prod([0, 1][j - 1] for j in contracted)
        index = i + sum(contracted) - 6
        total += generators[index] * factor
        if factor:
            surviving.append({'tuple_one_based': contracted, 'generator_index': index})
    upper.append(total)
    survivors.append(surviving)
assert upper == [0, -1]
assert [len(values) for values in survivors] == [1, 1]
assert [values[0]['generator_index'] for values in survivors] == [5, 6]
assert upper == [-coordinate ** 5 for coordinate in [0, 1]]

def add(first, second):
    result = [0] * max(len(first), len(second))
    for i, value in enumerate(first): result[i] += value
    for i, value in enumerate(second): result[i] += value
    return result

def multiply(first, second):
    result = [0] * (len(first) + len(second) - 1)
    for i, a in enumerate(first):
        for j, b in enumerate(second): result[i + j] += a * b
    return result

vector = [[1], [0], [0, 1]]
contractions = []
for row in rows:
    result = [0]
    for exponent, coefficient in row.items():
        term = [coefficient]
        for i, power in enumerate(exponent):
            for _ in range(power): term = multiply(term, vector[i])
        result = add(result, term)
    contractions.append(result)
eigenvalue = [2, 2, 2]
residuals = [add(multiply(eigenvalue, multiply(coordinate, coordinate)),
                 [-a for a in contraction])
             for coordinate, contraction in zip(vector, contractions)]
assert all(value == 0 for value in residuals[0] + residuals[1])
assert residuals[2] == [-1, -4, 3, 2, 2]
assert residuals[2][0] == -1 and sum(residuals[2]) == 2
out = {'status': 'PASS: exact finite transcription and endpoint diagnostics only',
       'one_based_source_lower_entries_checked': 27,
       'lower_coefficients': [{str(key): value for key, value in row.items()} for row in rows],
       'first_slice_is_four_squares': True,
       'one_based_source_upper_entries_checked': 64,
       'upper_contraction': upper, 'surviving_terms': survivors,
       'lower_eigenpair_residuals': residuals,
       'root_endpoints': [-1, 2],
       'universal_proof_and_IVT_provided_by_Lean_not_this_script': True}
destination = Path(__file__).with_name('reconstruction.json')
destination.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
