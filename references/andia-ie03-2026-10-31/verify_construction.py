#!/usr/bin/env python3
"""Exact construction from the paper; Python standard library only.

The five explicit lists of integer pivot pairs below specify all 4096
row/column positions through four W4 lifts. No character decoding is used.
124 local pivots are checked against the whole active matrix with Fractions.
The paper applies the standard doubling argument twice to justify each
fourfold lift and every comparison covered by it.
The W2 and W4 panel identities and all five quarter-sign core identities
and binary ranks are checked exactly. By default, also check every entry
of the supplied explicit matrix.npy.
Use --write-matrix to regenerate that file, or --pivots FILE to export all pivots.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import ast
import csv
import hashlib
import struct
import time

# Each pair is a zero-based CURRENT ACTIVE row and column position.
# The five tuples apply at root orders 16, 64, 256, 1024, and 4096.
# Each fourfold lift occurs before the next tuple is read.
LOCAL_PIVOTS = (
    # Root order 16: 10 directly checked pivots.
    (
        (14, 8), (12, 6), (10, 4), (9, 2), (7, 4), (6, 10),
        (8, 6), (7, 4), (5, 1), (3, 1),
    ),
    # Root order 64: 16 directly checked pivots.
    (
        (19, 17), (15, 1), (11, 8), (3, 18), (18, 13), (6, 4),
        (16, 9), (15, 10), (0, 0), (3, 1), (0, 1), (1, 2),
        (8, 6), (8, 7), (6, 9), (5, 7),
    ),
    # Root order 256: 22 directly checked pivots.
    (
        (3, 1), (10, 8), (13, 15), (16, 26), (19, 18), (22, 11),
        (25, 20), (3, 5), (3, 3), (3, 4), (9, 14), (9, 19),
        (11, 10), (9, 10), (6, 8), (12, 6), (9, 13), (12, 7),
        (12, 10), (4, 8), (9, 4), (5, 10),
    ),
    # Root order 1024: 28 directly checked pivots.
    (
        (3, 1), (6, 16), (9, 35), (16, 23), (19, 30), (22, 26),
        (25, 12), (32, 18), (28, 4), (9, 8), (9, 6), (9, 7),
        (11, 18), (11, 8), (8, 1), (7, 1), (16, 14), (21, 22),
        (16, 6), (2, 7), (12, 7), (1, 12), (17, 16), (11, 3),
        (14, 2), (8, 10), (12, 7), (8, 5),
    ),
    # Root order 4096: 48 directly checked pivots.
    (
        # These first 34 pairs leave the 14-square quarter-sign state.
        (3, 1), (6, 16), (9, 4), (16, 7), (23, 21), (26, 24),
        (12, 35), (32, 10), (35, 16), (38, 36), (18, 25), (24, 29),
        (24, 27), (24, 28), (17, 13), (16, 14), (19, 29), (3, 26),
        (29, 14), (4, 27), (18, 25), (21, 19), (6, 0), (2, 9),
        (18, 16), (13, 3), (4, 5), (1, 2), (19, 7), (16, 0),
        (8, 2), (15, 3), (10, 7), (7, 6),
        # These final 14 pairs give the diagonal suffix after reordering.
        (8, 4), (2, 6), (10, 11), (3, 8), (1, 5), (2, 5),
        (7, 2), (0, 1), (0, 1), (0, 0), (0, 0), (0, 0),
        (0, 0), (0, 0),
    ),
)


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def w(i, j):
    return 1 - 2*((i & j).bit_count() % 2)


def cap(S):
    return max(abs(v) for row in S for v in row)


def step(S, i, j):
    p = S[i][j]
    return [[S[a][b]-S[a][j]*S[i][b]/p
             for b in range(len(S)) if b != j]
            for a in range(len(S)) if a != i]


def check_panel():
    """Finite exact checks for the doubling lemma and its fourfold version."""
    for size, pivots in ((2, (1, -2)), (4, (1, -2, -2, 4))):
        W = [[F(w(i,j)) for j in range(size)] for i in range(size)]
        A = [row[:] for row in W]
        for k, h in enumerate(pivots):
            R = [[A[i-k][j-k] if min(i,j) >= k else F(0)
                  for j in range(size)] for i in range(size)]
            P = [[W[i][j]-R[i][j] for j in range(size)] for i in range(size)]
            require(A[0][0] == h and cap(R) == abs(h), 'Panel identity')
            require(1+cap(P) <= abs(h), 'Panel bound')
            A = step(A,0,0)


def binary_rank(D):
    """Rank over F_2 after making the first sign row and column positive."""
    basis = {}
    for row in D:
        bits = sum((row[j]*D[0][j]*row[0]*D[0][0] < 0) << j
                   for j in range(len(row)))
        while bits:
            leading = bits.bit_length()-1
            if leading in basis:
                bits ^= basis[leading]
            else:
                basis[leading] = bits
                break
    return len(basis)


def check_quarter_state(S, rows, columns, root_order):
    """Check S=(root_order/4)Q and the exact identity D^T Q=4I."""
    size = len(S)
    scale = F(root_order,4)
    require(all(abs(value) == scale for row in S for value in row),
            'Not a full quarter-sign state')
    Q = [[int(value/scale) for value in row] for row in S]
    D = [[w(r,c) for c in columns] for r in rows]
    require(all(sum(D[k][i]*Q[k][j] for k in range(size)) == 4*(i==j)
                for i in range(size) for j in range(size)),
            'Quarter-state complementary inverse identity')
    require(binary_rank(D) == size-2, 'Wrong dephased binary rank')


def permutation_sign(p):
    visited = set()
    cycles = 0
    for i in range(len(p)):
        if i in visited:
            continue
        cycles += 1
        while i not in visited:
            visited.add(i)
            i = p[i]
    return (-1)**(len(p)-cycles)


def construct(verbose=True):
    check_panel()
    n = 16
    R = list(range(n)); C = R[:]
    S = [[F(w(i,j)) for j in C] for i in R]
    word, pivots, snapshots = [], [], []
    local = 0
    core = None
    expected_ends = (6,8,10,12,0)
    for phase, choices in enumerate(LOCAL_PIVOTS):
        if phase:
            m = len(S)
            S = [[S[i][j]*w(a,b) for j in range(m) for b in range(4)]
                 for i in range(m) for a in range(4)]
            word = [(r+n*z,c+n*z) for r,c in word for z in range(4)]
            pivots = [p*h for p in pivots for h in (1,-2,-2,4)]
            R = [r+n*z for r in R for z in range(4)]
            C = [c+n*z for c in C for z in range(4)]
            n *= 4
        snapshots.append({'order':n,'start':[row[:] for row in S]})
        for choice, (i,j) in enumerate(choices):
            if phase == 4 and len(S) == 14:
                check_quarter_state(S,R,C,n)
                core = (R[:], C[:], [row[:] for row in S])
                snapshots[-1]['end'] = [row[:] for row in S]
            p = S[i][j]
            require(p != 0 and abs(p) == cap(S), f'Local pivot failure, phase {phase+1}, pair {choice+1}')
            word.append((R.pop(i),C.pop(j)))
            pivots.append(p)
            S = step(S,i,j)
            local += 1
        require(len(S) == expected_ends[phase], 'Unexpected endpoint')
        if S:
            check_quarter_state(S,R,C,n)
            snapshots[-1]['end'] = [row[:] for row in S]
        if verbose:
            print(f'Root {n:4d}: {len(choices):2d} local whole-active checks; {len(S):2d} remaining')
    rows, cols = map(list, zip(*word))
    require(n == len(word) == 4096 and not R and not C, 'Incomplete word')
    require(local == 124, 'Incorrect local count')
    require(sorted(rows) == sorted(cols) == list(range(n)), 'Not permutations')
    product = F(1)
    for p in pivots:
        product *= p
    require(product == permutation_sign(rows)*permutation_sign(cols)*(1 << 24576),
            'Signed determinant product')
    require(max(map(abs,pivots)) == 4608, 'Wrong growth')
    first = next(i+1 for i,p in enumerate(pivots) if abs(p) > n)
    require(first == 4089 and word[first-1] == (191,3552) and pivots[first-1] == 4608, 'Wrong overshoot')
    require(max(map(abs,pivots[:-14])) == 1024, 'Wrong prefix maximum')
    expected_tail = [F(x) for x in ('1','-2','-2','2','4','-4','9/2','-10/9','6/5','-4/3','1','2','-2','-4')]
    require(pivots[-14:] == [1024*x for x in expected_tail], 'Wrong suffix')
    X,Y,T = core
    require(all(abs(v) == 1024 for row in T for v in row), 'Wrong core scaling')
    for i in range(14):
        for j in range(14):
            require(sum(w(X[k],Y[i])*T[k][j] for k in range(14)) == n*(i==j), 'Complementary inverse identity')
    # Present the terminal block in its FINAL pivot order, so its suffix is diagonal.
    ir = [X.index(r) for r in rows[-14:]]
    jc = [Y.index(c) for c in cols[-14:]]
    T = [[T[i][j] for j in jc] for i in ir]
    Q = [[v/1024 for v in row] for row in T]
    for expected in expected_tail:
        require(Q[0][0] == expected and abs(expected) == cap(Q), 'Diagonal core suffix')
        Q = step(Q,0,0)
    core = (rows[-14:], cols[-14:], T)
    return rows, cols, pivots, snapshots, core


def matrix_rows(rows, cols):
    for r in rows:
        yield bytes(1 if w(r,c) == 1 else 255 for c in cols)


def write_matrix(path, rows, cols):
    """Write the documented NPY 1.0 format without importing NumPy."""
    header = "{'descr': '|i1', 'fortran_order': False, 'shape': (4096, 4096), }"
    header = header.encode('ascii')
    header += b' ' * ((-10-len(header)-1) % 64) + b'\n'
    with path.open('wb') as f:
        f.write(b'\x93NUMPY\x01\x00'+struct.pack('<H',len(header))+header)
        for row in matrix_rows(rows,cols):
            f.write(row)


def check_matrix(path, rows, cols):
    with path.open('rb') as f:
        require(f.read(8) == b'\x93NUMPY\x01\x00', 'Expected NPY 1.0 file')
        size = struct.unpack('<H',f.read(2))[0]
        header = ast.literal_eval(f.read(size).decode('ascii').strip())
        require(header == {'descr':'|i1','fortran_order':False,'shape':(4096,4096)}, 'Wrong matrix format')
        for i, expected in enumerate(matrix_rows(rows,cols)):
            require(f.read(4096) == expected, f'Wrong matrix row {i}')
        require(f.read(1) == b'', 'Trailing data')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--matrix', type=Path,
                    default=Path(__file__).resolve().with_name('matrix.npy'),
                    help='explicit matrix file to compare or regenerate')
    ap.add_argument('--write-matrix', action='store_true', help='regenerate matrix.npy before checking it')
    ap.add_argument('--pivots', type=Path, help='optional CSV of the full original-label history')
    args = ap.parse_args()
    begun = time.monotonic()
    rows,cols,pivots,_,_ = construct()
    matrix = args.matrix
    if args.write_matrix:
        write_matrix(matrix,rows,cols)
    check_matrix(matrix,rows,cols)
    if args.pivots:
        with args.pivots.open('w',newline='') as f:
            writer = csv.writer(f)
            writer.writerow(['step','row_label','column_label','signed_pivot','whole_active_maximum'])
            for k,(r,c,p) in enumerate(zip(rows,cols,pivots),1):
                writer.writerow([k,r,c,str(p),str(abs(p))])
    signature = hashlib.sha256(('\n'.join(map(str,pivots))+'\n').encode()).hexdigest()
    print('PASS: all 16,777,216 file entries match the explicit Walsh-permutation formula')
    print('PASS: both label lists are permutations; character orthogonality gives H H^T = 4096 I')
    print('PASS: W2/W4 panel identities; all five quarter-state inverse identities and binary ranks')
    print('PASS: 124 rational local checks plus four proved W4 lifts certify all 4096 pivots')
    print('PASS: signed determinant product and dephased binary rank 12 of the final 14-square')
    print('Growth = 4608 = (9/8)*4096; first overshoot = +4608 at step 4089, labels (191,3552)')
    print('Signed pivot sequence SHA256:',signature)
    print(f'Elapsed seconds: {time.monotonic()-begun:.3f}')


if __name__ == '__main__':
    main()
