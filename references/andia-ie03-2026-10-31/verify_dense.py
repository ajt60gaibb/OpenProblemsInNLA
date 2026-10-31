import numpy as np
from math import gcd
from fractions import Fraction

H = np.load("matrix.npy")
n = 4096

# (1) Hadamard
assert H.shape == (n, n) and np.all((H == 1) | (H == -1))
assert np.array_equal(H.astype(float) @ H.T, n * np.eye(n))

# (2) Completely pivoted Gaussian elimination
A, d, growth = H.astype(np.int64), 1, Fraction(0)

for _ in range(n):
    p = int(A[0, 0])
    m = max(int(A.max()), -int(A.min()))
    assert abs(p) == m  # Top left entry is maximal
    growth = max(growth, Fraction(m, d))
    if len(A) == 1:
        break
    assert 2 * m * m < 2**63  # Prevent integer overflow
    B = p * A[1:, 1:] - A[1:, :1] * A[:1, 1:]
    if p < 0:
        B = -B

    d *= abs(p)
    g = gcd(d, int(np.gcd.reduce(B.ravel())))
    A, d = B // g, d // g

# (3) Growth exceeds the Hadamard order
assert growth > n
print("PASS: Hadamard, completely pivoted, growth =", growth)