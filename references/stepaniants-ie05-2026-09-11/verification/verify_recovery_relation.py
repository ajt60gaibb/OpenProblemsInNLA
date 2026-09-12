#!/usr/bin/env python3
"""Compare the two exact IE-05 witnesses; inputs are the two frozen proofs."""
from argparse import ArgumentParser
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import re


def mm(a, b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def solve(l, m):
    t = [row[:] for row in m]
    for i in range(len(l)):
        for j in range(len(l)):
            t[i][j] -= sum(l[i][k]*t[k][j] for k in range(i))
    return t


def matrices(text):
    return [[[int(v) for v in row.split('&')] for row in body.strip().split(r'\\')]
            for body in re.findall(r'\\begin\{pmatrix\}(.*?)\\end\{pmatrix\}', text, re.S)]


def main():
    parser = ArgumentParser()
    parser.add_argument('--current-proof', type=Path, required=True)
    parser.add_argument('--recovered-proof', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    a, b = args.current_proof.read_bytes(), args.recovered_proof.read_bytes()
    assert hashlib.sha256(a).hexdigest() == '18d49f30a3ef26f4c88a85c8ea1fc9e5c4e1702b4be6061d39aec892e96a4af7'
    assert hashlib.sha256(b).hexdigest() == 'a3ba2afb7bac18bc2cb6594b194755be32203324a01bbab460507b8c9af53c2d'
    h, t, h0 = matrices(a.decode())
    m0, mstar = matrices(b.decode())
    assert m0 == h0
    l = [[1 if i == j else -1 if i > j else 0 for j in range(8)] for i in range(8)]
    l[7][1] = 0
    ls = [[1 if i == j else -1 if i > j else 0 for j in range(8)] for i in range(8)]
    ls[6][1] = 0
    p = [[int(i == j) for j in range(8)] for i in range(8)]
    p[6], p[7] = p[7], p[6]
    j = [[int(i == k) for k in range(8)] for i in range(8)]
    j[6][6] = -1
    k = [row[:] for row in j]
    k[6][7] = 1
    assert mm(mm(p, l), k) == ls
    assert mm(mm(p, h), j) == mstar
    norms = [sum(h[i][col]**2 for i in range(8)) for col in range(8)]
    assert norms == [sum(mstar[i][col]**2 for i in range(8)) for col in range(8)]
    for m in [h, mstar]:
        assert mm(list(map(list, zip(*m))), m) == [[norms[i] if i == col else 0 for col in range(8)] for i in range(8)]
    ts = solve(ls, mstar)
    assert t == solve(l, h)
    assert all(ts[i][col] == 0 for i in range(8) for col in range(i))
    assert all(ts[i][i] == t[i][i] > 0 for i in range(8))
    stages = []
    final_blocks = []
    for start in range(8):
        sa = mm([row[start:] for row in l[start:]], [row[start:] for row in t[start:]])
        sb = mm([row[start:] for row in ls[start:]], [row[start:] for row in ts[start:]])
        for s in [sa, sb]:
            assert s[0][0] > 0 and all(abs(row[0]) <= s[0][0] for row in s)
        if start <= 6:
            permuted = [row[:] for row in sa]
            permuted[-2], permuted[-1] = permuted[-1], permuted[-2]
            for row in permuted:
                row[6-start] *= -1
            assert sb == permuted
        else:
            assert sa == sb == [[5272]]
        qa = max(F(sa[i][col]**2, norms[col+start]) for i in range(8-start) for col in range(8-start))
        qb = max(F(sb[i][col]**2, norms[col+start]) for i in range(8-start) for col in range(8-start))
        assert qa == qb
        stages.append(str(qa))
        if start == 6:
            final_blocks = [sa, sb]
    assert final_blocks == [[[3063,2683],[-3063,2589]],[[3063,2589],[-3063,2683]]]
    assert F(stages[-1])/F(stages[0]) == F(5272,63)**2
    result = {'verdict':'PASS: same exact IE-05 witness under row permutation and a column sign',
              'current_proof_sha256':hashlib.sha256(a).hexdigest(),
              'recovered_proof_sha256':hashlib.sha256(b).hexdigest(),
              'relation':'Q_recovered = P_(7,8) Q_current diag(1,1,1,1,1,1,-1,1)',
              'input_relation':'L_recovered = P_(7,8) L_current K, K=I except K77=-1,K78=1',
              'canonical_baseline_matrix_identical':True,
              'column_squared_norms_identical':norms,
              'positive_integer_upper_factor_diagonals_identical':[t[i][i] for i in range(8)],
              'first_available_row_is_admissible_at_every_stage_for_both':True,
              'all_eight_squared_active_maxima_identical':stages,
              'unnormalized_stage7_blocks':final_blocks,
              'common_growth':'5272/63',
              'consequence':'Corroborating equivalent reconstruction; not a second solved problem or new IE-05 submission.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(result['verdict'])
    print(result['relation'])
    print('All eight active-stage maxima and both first-tie paths verified exactly.')


if __name__ == '__main__':
    main()
