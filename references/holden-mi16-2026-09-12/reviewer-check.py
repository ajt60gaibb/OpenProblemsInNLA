#!/usr/bin/env python3
"""Independent bounded exact-arithmetic checks of MI-16 exceptional spectra.

Uses only Python's standard library and imports no submitted proof code.
These finite checks supplement the independent mathematical proof audit.
"""
from fractions import Fraction as F
from math import factorial, comb


def simplex_value(t, x):
    elementary = [F(1)] + [F(0)] * len(t)
    for coordinate in t:
        for j in range(len(t), 0, -1):
            elementary[j] += coordinate * elementary[j - 1]
    return sum(factorial(j) * (-x) ** j * elementary[j]
               for j in range(len(elementary)))


def compositions(total, parts):
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest


def main():
    checks = 0
    for n in range(2, 7):
        for x in (F(1, 4), F(2, 3), F(3, 4), F(1)):
            target = max(simplex_value((F(1, 2),) * 2, x),
                         simplex_value((F(1, n),) * n, x))
            for composition in compositions(8, n):
                point = tuple(F(a, 8) for a in composition)
                actual = simplex_value(point, x)
                assert actual <= target, (n, x, point)
                if actual == target:
                    positive = [a for a in point if a]
                    assert len(set(positive)) == 1 and len(positive) in (2, n), (n, x, point)
                checks += 1
    for k in range(3, 41):
        for x in (F(0), F(1, 4), F(3, 4), F(1)):
            integral = sum(comb(k - 1, j) * (-x / F(k)) ** j * factorial(j + 2)
                           for j in range(k))
            assert integral > 0, (k, x, integral)
            checks += 1
        if k % 2 == 0:
            moments = [F(1), F(k - 3)]
            for j in range(1, k - 1):
                moments.append((k - 3 - j) * moments[-1] + k * j * moments[-2])
            direct = F(sum(comb(k - 1, j) * k ** (k - 1 - j) * (-1) ** j * factorial(j + 2)
                           for j in range(k)), 2)
            assert moments[-1] == direct, (k, moments[-1], direct)
            checks += 1
    print('PASS', checks, 'independently written exact rational checks')


if __name__ == '__main__':
    main()
