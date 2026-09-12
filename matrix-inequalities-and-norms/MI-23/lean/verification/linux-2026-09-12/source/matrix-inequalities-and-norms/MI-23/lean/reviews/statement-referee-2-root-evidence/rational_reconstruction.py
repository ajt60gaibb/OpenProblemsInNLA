"""Independent exact witness reconstruction, not a Lean or spectral proof."""
from fractions import Fraction as F
import json

def mat(rows):
    return [[F(x) for x in row] for row in rows]

def diag(a, b, c):
    return mat([[a, 0, 0], [0, b, 0], [0, 0, c]])

def mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(3)) for j in range(3)]
            for i in range(3)]

def transpose(a):
    return list(map(list, zip(*a)))

def frobenius_squared(a):
    return sum(x*x for row in a for x in row)

D = diag(16, F(1, 12), 1)
T = mat([[2, 1, 2], [1, 25, -10], [2, -10, 10]])
lower = mat([[1, 0, 0], [F(1, 2), 1, 0], [1, F(-22, 49), 1]])
pivots = diag(2, F(49, 2), F(150, 49))
assert mul(mul(lower, pivots), transpose(lower)) == T

T2 = mul(T, T)
T4 = mul(T2, T2)
T7 = mul(mul(T4, T2), T)
T8 = mul(T4, T4)
A = mul(D, D)
B = mul(mul(D, T8), D)
G = mul(mul(D, T), D)
H = mul(mul(D, T7), D)
GH = mul(G, H)
AB = mul(A, B)
entry = GH[0][2]
frob = frobenius_squared(AB)
gap = entry**2 - frob
assert entry == F(1260589125202, 9) and entry > 140000000000
assert frob == F(2009446159144992718181231562721, 107495424)
assert frob < F(138000000000)**2
assert gap == F(99434824489435745411095588895, 107495424) and gap > 0
assert F(1, 8) < F(1, 4)
print(json.dumps({
    "status": "PASS: exact finite witness reconstruction only",
    "T2": T2, "T4": T4, "T7": T7, "T8": T8,
    "positive_LDL_pivots": [F(2), F(49, 2), F(150, 49)],
    "lower_triangular_factor": lower,
    "A": A, "B": B, "G": G, "H": H,
    "GH_entry_paper_13_lean_02": entry,
    "frobenius_squared_AB": frob,
    "squared_gap": gap,
    "unproved_analytic_obligations": [
        "actual CFC rational powers and generalized means agree with G and H",
        "actual ordered product eigenvalues represent full original log-majorization",
        "largest eigenvalue of G^2 H^2 is the genuine operator norm of GH squared",
        "entry lower bound and Frobenius upper bound for the genuine operator norm",
        "all witness positivity and universal-conjecture negation in Lean",
    ],
}, default=str, indent=2))
