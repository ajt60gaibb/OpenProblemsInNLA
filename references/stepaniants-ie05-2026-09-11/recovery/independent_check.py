#!/usr/bin/env python3
"""Alternative exact IE-05 checker, without importing verify_exact.py.

Starts from hard-coded integer columns, rather than generating them with
Gram--Schmidt. Computes each Schur complement directly with a leading-block
inverse, rather than reusing the elimination recurrence of the main verifier.
This is an alternative implementation, not an external peer review.
Python 3.10+; standard library only.
"""
from fractions import Fraction as F

BASE = [
 [1,-5,-8,-12,-16,-16,0,64],
 [-1,13,-4,-6,-8,-8,0,32],
 [-1,-3,51,-3,-4,-4,0,16],
 [-1,-3,-11,169,-2,-2,0,8],
 [-1,-3,-11,-43,511,-1,0,4],
 [-1,-3,-11,-43,-171,1365,0,2],
 [-1,-3,-11,-43,-171,-683,1,1],
 [-1,-3,-11,-43,-171,-683,-1,1]]
MODIFIED = [
 [1,-1,-3,-21,-41,-101,325,63],
 [-1,3,1,17,71,291,-1179,31],
 [-1,-1,13,-19,-56,-196,752,16],
 [-1,-1,-3,189,-28,-98,376,8],
 [-1,-1,-3,-51,581,-49,188,4],
 [-1,-1,-3,-51,-213,1507,94,2],
 [-1,1,-5,-55,-183,-683,2683,1],
 [-1,-1,-3,-51,-213,-873,-2589,1]]


def inverse(a):
    n = len(a)
    b = [[F(x) for x in a[i]]+[F(i==j) for j in range(n)] for i in range(n)]
    for k in range(n):
        r = next(i for i in range(k,n) if b[i][k] != 0)
        b[k],b[r] = b[r],b[k]
        pivot = b[k][k]
        b[k] = [x/pivot for x in b[k]]
        for i in range(n):
            if i != k:
                m = b[i][k]
                b[i] = [x-m*y for x,y in zip(b[i],b[k])]
    return [row[n:] for row in b]


def check(m, modified):
    n = len(m)
    s = [sum(m[i][j]**2 for i in range(n)) for j in range(n)]
    for j in range(n):
        assert s[j] > 0
        for k in range(j):
            assert sum(m[i][j]*m[i][k] for i in range(n)) == 0
    # Solve L T = M by direct triangular substitution.
    lower = [[F(1 if i==j else -1 if i>j else 0) for j in range(n)] for i in range(n)]
    if modified:
        lower[6][1] = 0
    t = [[F(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            t[i][j] = m[i][j]-sum(lower[i][k]*t[k][j] for k in range(i))
            if j < i:
                assert t[i][j] == 0
        assert t[i][i] > 0
    maxima = []
    for k in range(n):
        leading_inverse = inverse([row[:k] for row in m[:k]]) if k else []
        schur = []
        for i in range(k,n):
            row = []
            for j in range(k,n):
                correction = sum((m[i][u]*leading_inverse[u][v]*m[v][j]
                                  for u in range(k) for v in range(k)),F(0))
                row.append(F(m[i][j])-correction)
            schur.append(row)
        assert schur[0][0] > 0
        assert all(abs(row[0]) <= schur[0][0] for row in schur)
        # The first-tie path is valid at each directly reconstructed stage.
        maxima.append(max(schur[i][j]**2/s[k+j]
                          for i in range(n-k) for j in range(n-k)))
    result = max(maxima)/maxima[0]
    expected = F(27793984,3969) if modified else F(17948132,2601)
    assert result == expected
    print(('COUNTEREXAMPLE' if modified else 'BASELINE')+': '+str(result))
    return result


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without -O: assertions are part of the checks.')
    a,b = check(BASE,False),check(MODIFIED,True)
    assert b > a
    print('PASS: direct integer-column orthogonality, positive QR factors,')
    print('      block-inverse Schur complements, pivot admissibility, and strict comparison.')
