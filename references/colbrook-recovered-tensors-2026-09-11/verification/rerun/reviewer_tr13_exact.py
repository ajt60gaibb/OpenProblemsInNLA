"""Independent small exact audit; no submission imports and no third-party modules."""
from fractions import Fraction
from pathlib import Path
import hashlib
import json


def rank(matrix):
    rows = [[Fraction(x) for x in row] for row in matrix]
    pivot = 0
    for col in range(len(rows[0])):
        found = next((i for i in range(pivot, len(rows)) if rows[i][col]), None)
        if found is None:
            continue
        rows[pivot], rows[found] = rows[found], rows[pivot]
        scale = rows[pivot][col]
        rows[pivot] = [x / scale for x in rows[pivot]]
        for i in range(pivot + 1, len(rows)):
            factor = rows[i][col]
            if factor:
                rows[i] = [x - factor*y for x, y in zip(rows[i], rows[pivot])]
        pivot += 1
        if pivot == len(rows):
            break
    return pivot


def normalized_hash(path):
    data = path.read_bytes().decode('utf-8').replace('\r\n', '\n').encode('utf-8')
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def main():
    cases = []
    for m, n in ((3, 3), (3, 4), (5, 3), (5, 4), (5, 6), (7, 5), (9, 4)):
        ell, k = n - 1, (m - 1)//2
        a, s = k*ell + 1, ell//2
        D = m*ell
        h = [0]*(D + 1)
        h[a - 1] = h[2*a + s - 1] = 1
        slices = [[[h[u + v + offset] for v in range(a)] for u in range(a)]
                  for offset in (0, s, 2*s)]
        K = []
        for u in range(a):
            K.append([-x for x in slices[1][u]] + slices[0][u] + [0]*a)
        for u in range(a):
            K.append([-x for x in slices[2][u]] + [0]*a + slices[0][u])
        for u in range(a):
            K.append([0]*a + [-x for x in slices[2][u]] + slices[1][u])
        observed = rank(K)
        expected = 2*((D + 2)//2)
        assert observed == expected
        cases.append({'m': m, 'n': n, 'full_K_rank': observed, 'expected': expected})

    binary = []
    for m in (3, 5, 7, 9, 11):
        k = (m - 1)//2
        matrix = [[int(u + v == k) for v in range(k + 2)] for u in range(k + 1)]
        observed = rank(matrix)
        assert observed == k + 1
        binary.append({'m': m, 'rank': observed})

    moments = []
    for D in (5, 6, 10, 15):
        r = (D + 2)//2
        nodes = list(range(r))
        jac = []
        for i in range(D + 1):
            row = []
            for t in nodes:
                row.extend((t**i, i*t**(i - 1) if i else 0))
            jac.append(row)
        observed = rank(jac)
        assert observed == D + 1
        moments.append({'D': D, 'r': r, 'moment_jacobian_rank': observed})

    base = Path(__file__).resolve().parents[1]
    result = {
        'status': 'PASS',
        'arithmetic': 'stdlib fractions.Fraction; no submission imports',
        'scope': 'Small exact diagnostic, not the all-parameter proof',
        'source': normalized_hash(base/'tensor_recovered/manuscripts/TR-13/main.tex'),
        'supplied_code': normalized_hash(base/'tensor_recovered/code/verify_tr13.py'),
        'koszul_cases': cases,
        'binary_cases': binary,
        'moment_jacobian_cases': moments,
    }
    output = Path(__file__).with_name('reviewer_tr13_exact.json')
    output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
