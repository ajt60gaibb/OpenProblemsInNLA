#!/usr/bin/env python3
"""
Comprehensive symbolic, 100-digit mpmath, and randomized numerical audit
of all theorems and lemmas in "No Finite-Dimensional Extremizer for Subquadratic Lee Constants".
"""
import json
import numpy as np
import sympy as sp
import mpmath as mp

mp.mp.dps = 105


def schatten_p_mp(M, p):
    G = M.T * M
    evals = mp.eigsy(G, eigvals_only=True)
    return mp.power(sum(mp.power(max(ev, mp.mpf(0)), p / 2) for ev in evals), 1 / p)


def abs_mp(M):
    G = M.T * M
    evals, evecs = mp.eigsy(G)
    n = M.rows
    res = mp.zeros(n, n)
    for k in range(n):
        s = mp.sqrt(max(evals[k], mp.mpf(0)))
        for i in range(n):
            for j in range(n):
                res[i, j] += s * evecs[i, k] * evecs[j, k]
    return res


def check_symbolic_theorem3():
    y, z = sp.symbols("y z", positive=True)
    # p = 3/2
    R6 = (y**2 + 1)**3 * (y**6 + 1) / (y**3 + 1)**4
    dR6 = sp.factor(sp.diff(R6, y))
    exp_dR6 = -6*y*(y - 1)*(y**2 + 1)**3*(y**4 - y**3 - 2*y**2 - y + 1) / (y**3 + 1)**5
    assert sp.simplify(dR6 - exp_dR6) == 0
    R6_z = z**4 * (z**2 - 3) / ((z + 2)**2 * (z - 1)**4)
    assert sp.simplify(R6 - R6_z.subs(z, y + 1/y)) == 0
    z_star = (1 + sp.sqrt(17)) / 2
    assert sp.simplify(R6_z.subs(z, z_star) - (107 + 51*sp.sqrt(17))/256) == 0

    # p = 4/3
    R4 = (y**3 + 1)**2 * (y**6 + 1) / (y**4 + 1)**3
    dR4 = sp.factor(sp.diff(R4, y))
    exp_dR4 = -6*y**2*(y - 1)*(y + 1)*(y**2 - y + 1)*(y**6 - y**5 - y**4 - y**2 - y + 1) / (y**4 + 1)**4
    assert sp.simplify(dR4 - exp_dR4) == 0
    R4_z = (z**3 - 3*z + 2)*(z**3 - 3*z) / (z**2 - 2)**3
    assert sp.simplify(R4 - R4_z.subs(z, y + 1/y)) == 0
    assert sp.simplify((y**6 - y**5 - y**4 - y**2 - y + 1)/y**3 - ((y+1/y)**3 - (y+1/y)**2 - 4*(y+1/y) + 2)) == 0

    # p = 5/4: verify unique critical point on y > 1 via Sturm's theorem on P18(y)
    P18 = sp.Poly(y**18 + y**17 + y**16 - y**15 - 2*y**14 - 2*y**13 - 2*y**12
                  + 2*y**10 + 2*y**9 + 2*y**8 - 2*y**6 - 2*y**5 - 2*y**4 - y**3 + y**2 + y + 1, y)
    n_roots_gt1 = sp.count_roots(P18, 1, None)
    assert n_roots_gt1 == 1, f"Expected 1 root > 1 for P18, got {n_roots_gt1}"
    R10 = (y**12 + 1)**5 * (y**20 + 1)**3 / (y**15 + 1)**8
    dR10 = sp.factor(sp.diff(R10, y))
    assert sp.simplify(sp.diff(R10, y) + 60*y**11*(y-1)*(y**4+1)**7*(y**8-y**4+1)**4*(y**16-y**12+y**8-y**4+1)**2*P18.as_expr()/(y**15+1)**9) == 0
    print("[PASS] Symbolic identities for Theorem 3 (p = 3/2, 4/3, 5/4 + Sturm uniqueness)")


def check_100digit_witnesses():
    # p = 3/2
    p32 = mp.mpf(3)/2
    C2_32 = mp.power((107 + 51*mp.sqrt(17))/256, mp.mpf(1)/6)
    A1 = mp.matrix([[49, 62, -1], [11, 14, 0], [0, 0, 0]])
    B1 = mp.matrix([[81, 0, 0], [0, 0, 0], [0, 0, 0]])
    r1 = schatten_p_mp(A1 + B1, p32) / schatten_p_mp(abs_mp(A1) + abs_mp(B1), p32)
    assert r1 > C2_32

    # p = 4/3
    p43 = mp.mpf(4)/3
    z43 = mp.findroot(lambda z: z**3 - z**2 - 4*z + 2, mp.mpf('2.34'))
    C2_43 = mp.power((z43**3 - 3*z43 + 2)*(z43**3 - 3*z43) / (z43**2 - 2)**3, mp.mpf(1)/4)
    A2 = mp.matrix([[62, 64, -1], [23, 24, 0], [0, 0, 0]])
    B2 = mp.matrix([[95, 0, 0], [0, 0, 0], [0, 0, 0]])
    r2 = schatten_p_mp(A2 + B2, p43) / schatten_p_mp(abs_mp(A2) + abs_mp(B2), p43)
    assert r2 > C2_43

    # p = 5/4
    p54 = mp.mpf(5)/4
    def dlogR(t, p):
        a = p / (2 - p)
        return (1/(2*(t+1)) + (2-p)/(2*p)*a*mp.power(t, a-1)/(mp.power(t, a)+1) - mp.power(t, p-1)/(mp.power(t, p)+1))
    t54 = mp.findroot(lambda t: dlogR(t, p54), mp.mpf('4.0'))
    C2_54 = mp.sqrt(t54 + 1) * mp.power(mp.power(t54, mp.mpf(5)/3) + 1, mp.mpf(3)/10) / mp.power(mp.power(t54, p54) + 1, mp.mpf(4)/5)
    A3 = mp.matrix([[336, 311, 0], [147, 137, 1], [0, 0, 0]])
    B3 = mp.matrix([[500, 0, 0], [0, 0, 0], [0, 0, 0]])
    r3 = schatten_p_mp(A3 + B3, p54) / schatten_p_mp(abs_mp(A3) + abs_mp(B3), p54)
    assert r3 > C2_54

    print(f"[PASS] 100-digit witness p=3/2: ratio={mp.nstr(r1, 25)} > C2={mp.nstr(C2_32, 25)}, gap={mp.nstr(r1-C2_32, 15)}")
    print(f"[PASS] 100-digit witness p=4/3: ratio={mp.nstr(r2, 25)} > C2={mp.nstr(C2_43, 25)}, gap={mp.nstr(r2-C2_43, 15)}")
    print(f"[PASS] 100-digit witness p=5/4: ratio={mp.nstr(r3, 25)} > C2={mp.nstr(C2_54, 25)}, gap={mp.nstr(r3-C2_54, 15)}")


def check_lemmas_numerical():
    rng = np.random.default_rng(2026)

    # 1. Lemma 4(a): 5,000 random complex PSD matrices
    max_diff = -1e9
    for t in range(5000):
        n = int(rng.integers(2, 8))
        p = float(rng.uniform(1.02, 1.98))
        M = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
        if t % 2 == 0:
            r = int(rng.integers(1, n))
            H = M[:, :r] @ M[:, :r].conj().T
        else:
            H = M @ M.conj().T
        v = rng.standard_normal(n) + 1j * rng.standard_normal(n)
        v /= np.linalg.norm(v)
        eps = float(10.0 ** rng.uniform(-4, 1))
        eH, VH = np.linalg.eigh(H)
        eH = np.maximum(eH, 0.0)
        eHe = np.maximum(np.linalg.eigvalsh(H + eps * np.outer(v, v.conj())), 0.0)
        lhs = np.sum(eHe**p) / p
        vHq = float(np.real(np.sum((eH**(p-1)) * np.abs(VH.conj().T @ v)**2)))
        rhs = np.sum(eH**p) / p + eps * vHq + (eps**p) / p
        max_diff = max(max_diff, lhs - rhs)
    assert max_diff <= 1e-11, f"Lemma 4(a) violation: {max_diff}"
    print(f"[PASS] Lemma 4(a) on 5,000 random complex PSD matrices: max(LHS - RHS) = {max_diff:.3e}")

    # 2. Lemma 2: 100 random rank-deficient sum tuples (ker(S) cap ran(H) != {0}) in high precision
    # Construct A1, A2 with S = A1 + A2 having z = e_n in ker(S) cap ran(H)
    passed_l2 = 0
    for trial in range(100):
        n = int(rng.integers(2, 5))
        p = mp.mpf(int(rng.integers(11, 19))) / 10
        A1_np = rng.standard_normal((n, n))
        A2_np = rng.standard_normal((n, n))
        # Force (A1 + A2) e_{n-1} = 0 while A1 e_{n-1} != 0
        A2_np[:, -1] = -A1_np[:, -1]
        A1 = mp.matrix(A1_np.tolist())
        A2 = mp.matrix(A2_np.tolist())
        S = A1 + A2
        z = mp.matrix([0]*(n-1) + [1])
        az = A1 * z
        w = az / mp.norm(az)
        # Apply R(theta) for small eta = 1 - cos(theta) = 1e-12
        eta = mp.mpf('1e-12')
        cos_t = 1 - eta
        sin_t = mp.sqrt(2*eta - eta**2)
        # M(eta) = S^T S - eta (A1^T w w^T A2 + A2^T w w^T A1)
        E = -(A1.T * w * w.T * A2 + A2.T * w * w.T * A1)
        M0 = S.T * S
        Meta = M0 + eta * E
        e0 = mp.eigsy(M0, eigvals_only=True)
        e1 = mp.eigsy(Meta, eigvals_only=True)
        norm0_p = sum(mp.power(max(e, mp.mpf(0)), p/2) for e in e0)
        norm1_p = sum(mp.power(max(e, mp.mpf(0)), p/2) for e in e1)
        if norm1_p > norm0_p:
            passed_l2 += 1
    assert passed_l2 == 100
    print(f"[PASS] Lemma 2 strict increase on {passed_l2}/100 random rank-deficient tuples (105-digit mpmath)")

    # 3. Universal 2x2 Cauchy-Schwarz inequality on 5,000 random complex tuples
    max_cs = -1e9
    for _ in range(5000):
        n = int(rng.integers(2, 5))
        m = int(rng.integers(2, 6))
        R = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
        R = R.conj().T @ R
        Xs = []
        for _ in range(m):
            M = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
            Xs.append(M.conj().T @ M)
        H = sum(Xs)
        lhs = sum(np.sum(np.linalg.svd(R @ X, compute_uv=False)) for X in Xs)
        rhs = np.sqrt(np.real(np.trace(R @ R @ H)) * np.real(np.trace(H)))
        max_cs = max(max_cs, lhs - rhs)
    assert max_cs <= 1e-11
    print(f"[PASS] Cauchy-Schwarz dual inequality on 5,000 random complex tuples: max(LHS - RHS) = {max_cs:.3e}")


if __name__ == "__main__":
    check_symbolic_theorem3()
    check_100digit_witnesses()
    check_lemmas_numerical()
    print("\nALL SYMBOLIC, 105-DIGIT, AND NUMERICAL CHECKS PASSED!")
