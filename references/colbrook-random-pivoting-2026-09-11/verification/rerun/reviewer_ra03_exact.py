"""Independent full-sized residual checks, without importing submitted code."""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import hashlib
import json


def energy(a):
    return sum((x*x for row in a for x in row), F(0))


def determinant(a):
    total = F(0)
    for p in permutations(range(len(a))):
        inversions = sum(p[i] > p[j] for i in range(len(p)) for j in range(i+1, len(p)))
        term = F((-1)**inversions)
        for i, j in enumerate(p):
            term *= a[i][j]
        total += term
    return total


def expectation(a, steps, check_paths=False):
    det_squared = determinant(a)**2 if check_paths else None
    histories = 0
    mass = F(0)
    value = F(0)

    def visit(b, remaining, probability, normalizers):
        nonlocal histories, mass, value
        norm = energy(b)
        if not remaining or norm == 0:
            weighted_error = probability*norm
            if check_paths:
                assert weighted_error == det_squared/normalizers
            histories += 1
            mass += probability
            value += weighted_error
            return
        conditional_mass = F(0)
        for i in range(len(b)):
            for j in range(len(b)):
                pivot = b[i][j]
                if not pivot:
                    continue
                p = pivot*pivot/norm
                conditional_mass += p
                residual = tuple(tuple(b[u][v]-b[u][j]*b[i][v]/pivot
                                       for v in range(len(b))) for u in range(len(b)))
                assert all(x == 0 for x in residual[i])
                assert all(row[j] == 0 for row in residual)
                visit(residual, remaining-1, probability*p, normalizers*norm)
        assert conditional_mass == 1

    visit(a, steps, F(1), F(1))
    assert mass == 1
    return {'expectation': str(value), 'positive_histories': histories, 'total_probability': str(mass)}


def main():
    two = tuple(tuple(F(x) for x in row) for row in ((2, 1), (1, 2)))
    literal = expectation(two, 1, True)
    assert F(literal['expectation']) == F(18, 5) > 2

    path_matrix = tuple(tuple(F(x) for x in row) for row in ((4, 1, 2), (1, 3, 1), (2, 1, 5)))
    path_check = expectation(path_matrix, 2, True)
    assert path_check['positive_histories'] == 36

    source = tuple(tuple(F(x) for x in row) for row in ((4, 1, 1), (1, 1, F(1, 2)), (1, F(1, 2), 1)))
    groups = (0, 0, 0, 0, 1, 2)
    roots = (2, 1, 1)
    replica = tuple(tuple(source[i][j]/(roots[i]*roots[j]) for j in groups) for i in groups)
    assert all(replica[i][i] == 1 for i in range(6))
    assert energy(source) == energy(replica)
    copies = []
    for steps in (1, 2):
        original_result = expectation(source, steps)
        replicated_result = expectation(replica, steps)
        assert original_result['expectation'] == replicated_result['expectation']
        copies.append({'steps': steps, 'original': original_result, 'replica': replicated_result})

    counts = []
    for r in range(1, 8):
        surviving = 0
        for history in permutations(range(1, r+2), r):
            if all(s+1 not in history[:s] for s in range(r)):
                surviving += 1
        assert surviving == 2**r
        counts.append({'r': r, 'single_list_count': surviving, 'pair_count': surviving**2})

    base = Path(__file__).resolve().parents[1]
    manuscript = base/'nla_submission_RA02_RA03/manuscript/sharp_random_pivoting.tex'
    data = manuscript.read_bytes().decode('utf-8').replace('\r\n', '\n').encode('utf-8')
    result = {'status': 'PASS', 'arithmetic': 'stdlib Fraction; original-label full residual recursion',
              'source_bytes': len(data), 'source_sha256': hashlib.sha256(data).hexdigest(),
              'literal_counterexample': literal, 'individual_adaptive_path_identity': path_check,
              'replication': copies, 'surviving_counts': counts,
              'scope': 'Independent finite diagnostics supplement the symbolic all-r review.'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
