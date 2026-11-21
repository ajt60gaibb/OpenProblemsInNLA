#!/usr/bin/env python3
"""
Verification script for Section 7 of the paper

    "Marginal growth rates of matrix products need not be weakly increasing
     or regularly varying"

(the pairs M#_theta of Definition 7.1 and Theorem 1.5).  Nothing in the paper depends on this
script.  Numbers of statements and equations refer to the paper.

  Part 1  Lemma 7.2, Proposition 7.3(a),(c), formula (7.2), and the entries of F0#, F1#
          (Section 7.1, Appendix A)                                               -- exact
  Part 2  all words of length n <= NMAX: Propositions 7.3(b) and 7.4, Lemma 7.5   -- floating point
  Part 3  the upper bound of Proposition 7.4 for large n (random multisets)       -- floating point
  Part 4  Section 7.3: Lemmas 7.6, 7.7 and the inequalities in the proof of
          Proposition 7.8, on several hundred angles                              -- floating point / multiprecision
  Part 5  Lemma 7.9 and the numbers in the proof of Theorem 1.5                   -- multiprecision / exact

Usage:  python3 verify_mf11_almost_linear.py [NMAX]     (default 16; needs numpy and mpmath)
The script stops with an AssertionError at the first failed check, and prints
"ALL CHECKS PASSED" at the end otherwise.
"""
from fractions import Fraction as Fr
import math, random, sys, time
import numpy as np
import mpmath as mp

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 16
mp.mp.dps = 80
rnd = random.Random(20261114)
T0 = time.time()
NCHECK = 0
SQ2 = math.sqrt(2)


def check(cond, *msg):
    global NCHECK
    NCHECK += 1
    if not cond:
        raise AssertionError(' '.join(str(m) for m in msg))


def done(text):
    print("  %-84s OK  (%.0f s)" % (text, time.time() - T0))


# =====================================================================================
# exact helpers
# =====================================================================================
def zeros(r, c): return [[Fr(0)] * c for _ in range(r)]
def eye(n):
    M = zeros(n, n)
    for i in range(n): M[i][i] = Fr(1)
    return M
def E(i, j, n=7):
    M = zeros(n, n); M[i - 1][j - 1] = Fr(1); return M
def add(*Ms): return [[sum(M[i][j] for M in Ms) for j in range(len(Ms[0][0]))] for i in range(len(Ms[0]))]
def sc(a, M): return [[Fr(a) * x for x in row] for row in M]
def mul(A, B):
    r, k, c = len(A), len(B), len(B[0]); assert len(A[0]) == k
    out = zeros(r, c)
    for i in range(r):
        for l in range(k):
            a = A[i][l]
            if a:
                Bl = B[l]; row = out[i]
                for j in range(c):
                    if Bl[j]: row[j] += a * Bl[j]
    return out
def mpow(A, n):
    R = eye(len(A))
    for _ in range(n): R = mul(R, A)
    return R
def tr(A): return [list(r) for r in zip(*A)]
def hstack(*Ms): return [sum((list(M[i]) for M in Ms), []) for i in range(len(Ms[0]))]
def vstack(*Ms): return [list(r) for M in Ms for r in M]
def blockdiag(*Ms):
    n = sum(len(M) for M in Ms); out = zeros(n, n); o = 0
    for M in Ms:
        for i in range(len(M)):
            for j in range(len(M)): out[o + i][o + j] = M[i][j]
        o += len(M)
    return out
def cols(idx):
    M = zeros(7, len(idx))
    for k, i in enumerate(idx): M[i - 1][k] = Fr(1)
    return M

I7 = eye(7)
X = add(E(4, 1), E(5, 2), E(6, 3))
Y = add(E(7, 1), sc(-1, E(6, 7)))
Z = add(E(2, 1), E(3, 2), E(5, 4), E(6, 5))
U = add(I7, X)
XZ, ZZ = mul(X, Z), mul(Z, Z)
XZZ = mul(X, ZZ)
EY, EZ = cols([7, 6]), cols([2, 3, 5, 6])
UZ = mul(tr(EZ), mul(U, EZ))

def build(c, s):
    cI, sI = sc(c, I7), sc(s, I7)
    rot = vstack(hstack(cI, sc(-1, sI)), hstack(sI, cI))
    jord = vstack(hstack(sc(Fr(1, 2), eye(2)), sc(Fr(1, 2), eye(2))), hstack(zeros(2, 2), sc(Fr(1, 2), eye(2))))
    S = blockdiag(rot, jord, sc(Fr(1, 4), eye(4)))
    T = blockdiag(U, U, eye(2), eye(2), UZ)
    J = vstack(I7, zeros(7, 7), zeros(2, 7), mul(tr(EY), Y), mul(tr(EZ), Z))
    L = hstack(I7, zeros(7, 7), EY, zeros(7, 2), EZ)
    return S, T, J, L, mul(T, S), mul(T, mul(J, mul(L, S)))

def cpow(c, s, m):
    zr, zi = Fr(1), Fr(0)
    for _ in range(m): zr, zi = zr * c - zi * s, zr * s + zi * c
    return zr

def Ks(m, c, s): return add(sc(cpow(c, s, m), I7), sc(Fr(m, 2 ** m), Y), sc(Fr(1, 4 ** m), Z))

# =====================================================================================
print("== Part 1: the pair M#_theta and the reduction (Lemma 7.2, Proposition 7.3) -- exact ==")
for (c, s) in ((Fr(3, 5), Fr(4, 5)), (Fr(5, 13), Fr(12, 13)), (Fr(-7, 25), Fr(24, 25)),
               (Fr(20, 29), Fr(21, 29)), (Fr(1), Fr(0)), (Fr(0), Fr(1)), (Fr(-1), Fr(0))):
    S, T, J, L, F0, F1 = build(c, s)
    dim = len(F0); check(dim == 22)
    check(mul(T, S) == mul(S, T) and mul(T, J) == mul(J, U) and mul(L, T) == mul(U, L))     # Lemma 7.2(i)
    Sm = eye(dim)
    for m in range(0, 12):                                                                     # Lemma 7.2(iii)
        check(mul(L, mul(Sm, J)) == Ks(m, c, s), 'K#', m); Sm = mul(Sm, S)
    check(mul(F0, F1) != mul(F1, F0))                                                          # Lemma 7.2(v)
    check(np.linalg.matrix_rank(np.array(F1, dtype=float)) == 7)
    check(abs(np.linalg.det(np.array(F0, dtype=float))) > 0)
    fS, fJ, fL, fU = (np.array(M_, dtype=float) for M_ in (S, J, L, U))
    check(abs(np.linalg.norm(fS, 2) - 1) < 1e-12)                                              # Lemma 7.2(ii)
    check(np.linalg.norm(fJ, 2) <= math.sqrt(3) + 1e-12 and np.linalg.norm(fL, 2) <= math.sqrt(3) + 1e-12)
    fF0 = np.array(F0, dtype=float)
    for n in (1, 2, 3, 7, 12):                                                                 # Lemma 7.2(iv)
        a = np.linalg.norm(np.linalg.matrix_power(fF0, n), 2); b = np.linalg.norm(np.linalg.matrix_power(fU, n), 2)
        check(abs(a - b) < 1e-9 and n <= b <= n + 1 + 1e-12)
    allowed = {Fr(0), c, -c, s, -s, Fr(1, 2), -Fr(1, 2), Fr(1, 4)}                              # entries (Section 7.1, Appendix A)
    check({x for r in F0 for x in r} <= allowed and {x for r in F1 for x in r} <= allowed)
    for _ in range(12):                                                                        # Proposition 7.3(a)
        n = rnd.randint(1, 12)
        letters = [rnd.randint(0, 1) for _ in range(n)]
        if 1 not in letters: letters[rnd.randrange(n)] = 1
        prod_ = eye(dim)
        for i in letters: prod_ = mul(F1 if i else F0, prod_)
        pos = [k + 1 for k, i in enumerate(letters) if i]
        k0, kh, gaps = pos[0], pos[-1], [pos[i] - pos[i - 1] for i in range(1, len(pos))]
        core = mpow(U, n)
        for m in reversed(gaps): core = mul(core, Ks(m, c, s))
        check(prod_ == mul(mpow(S, n - kh), mul(J, mul(core, mul(L, mpow(S, k0))))))
# Proposition 7.3(c) on random data: the normal form with alpha_i = m_i 2^-m_i, beta_i = 4^-m_i
for _ in range(60):
    c, s = rnd.choice(((Fr(3, 5), Fr(4, 5)), (Fr(5, 13), Fr(12, 13)), (Fr(8, 17), Fr(15, 17))))
    h = rnd.randint(0, 6); n = rnd.randint(0, 40)
    ms = [rnd.randint(1, 6) for _ in range(h)]
    lhs = mpow(U, n)
    for m in ms: lhs = mul(lhs, Ks(m, c, s))
    qs = [cpow(c, s, m) for m in ms]
    def Px(ex):
        v = Fr(1)
        for r_, q in enumerate(qs):
            if r_ not in ex: v *= q
        return v
    P = Px(())
    al = [Fr(m, 2 ** m) for m in ms]; be = [Fr(1, 4 ** m) for m in ms]
    y1 = sum(al[i] * Px((i,)) for i in range(h)); z1 = sum(be[i] * Px((i,)) for i in range(h))
    y2 = sum(al[i] * al[k] * Px((i, k)) for i in range(h) for k in range(i + 1, h))
    z2 = sum(be[i] * be[k] * Px((i, k)) for i in range(h) for k in range(i + 1, h))
    check([lhs[r_][0] for r_ in range(7)] == [P, z1, z2, n * P, n * z1, n * z2 - y2, y1])
    crit = sum(Px((i, k)) * (Fr(n, 4 ** (ms[i] + ms[k])) - Fr(ms[i] * ms[k], 2 ** (ms[i] + ms[k])))
               for i in range(h) for k in range(i + 1, h))
    check(n * z2 - y2 == crit)                                                                 # (7.2)
done("Lemma 7.2, Proposition 7.3(a),(c), (7.2), the entries of F0#, F1#")

# =====================================================================================
# floating point tools
# =====================================================================================
fl = lambda M: np.array(M, dtype=float)
Xn, Yn, Zn, Un, EYn, EZn, UZn = map(fl, (X, Y, Z, U, EY, EZ, UZ))
I7n = np.eye(7)

def bd(*Ms):
    n = sum(M.shape[0] for M in Ms); out = np.zeros((n, n)); o = 0
    for M in Ms:
        k = M.shape[0]; out[o:o + k, o:o + k] = M; o += k
    return out

def pair(theta):
    c, s = math.cos(math.pi * theta), math.sin(math.pi * theta)
    rot = np.block([[c * I7n, -s * I7n], [s * I7n, c * I7n]])
    jord = np.block([[0.5 * np.eye(2), 0.5 * np.eye(2)], [np.zeros((2, 2)), 0.5 * np.eye(2)]])
    S = bd(rot, jord, 0.25 * np.eye(4))
    T = bd(Un, Un, np.eye(2), np.eye(2), UZn)
    J = np.vstack([I7n, np.zeros((7, 7)), np.zeros((2, 7)), EYn.T @ Yn, EZn.T @ Zn])
    L = np.hstack([I7n, np.zeros((7, 7)), EYn, np.zeros((7, 2)), EZn])
    return T @ S, T @ J @ L @ S

def alpha(m): return m * 2.0 ** -m
def beta(m): return 4.0 ** -m
def r_(m): return m * 2.0 ** m
def Np(p): return p * p * 4 ** p

def taus(theta, M):
    th = mp.mpf(theta); out = [None]
    for m in range(1, M + 1):
        x = m * th; d = abs(x - mp.nint(x))
        out.append(math.inf if d == 0 else float(1 / (1 - abs(mp.cos(mp.pi * d)))))
    return out

def Mtrunc(n): return min(n - 1, int(2 * math.log2(max(n, 2))) + 30)

def phi_parts(T, n, M=None, exclude=None, cancel=True):
    if M is None: M = Mtrunc(n)
    M = min(M, n - 1)
    nus = [None] + [min(n / m, T[m]) for m in range(1, M + 1)]
    p1 = n * max([nus[m] * beta(m) for m in range(1, M + 1)], default=0.0)
    p2 = 0.0
    for m in range(1, M + 1):
        for mq in range(m, M + 1):
            if exclude is not None and (m, mq) == exclude: continue
            cc = r_(m) * r_(mq)
            fac = abs(n / cc - 1) if cancel else max(1.0, n / cc)
            v = nus[m] * nus[mq] * alpha(m) * alpha(mq) * fac
            if v > p2: p2 = v
    return n, p1, p2

def Phi(T, n, M=None): return sum(phi_parts(T, n, M))
def xp(T, p): return min(T[p] * 4.0 ** -p, p)
def Rp(T, p): return max([T[k] * 4.0 ** -k for k in range(1, p)], default=0.0)
def Deltap(T, p):
    R = Rp(T, p)
    return 0.0 if R == math.inf else xp(T, p) / max(1.0, R)

def coords(theta, n, counts):
    """a#_n(mu) e_1 for the multiset counts {m: c_m}, via the normal form; returns 7-vector"""
    a = I7n.copy()
    for m, cnt in counts.items():
        K = math.cos(math.pi * m * theta) * I7n + alpha(m) * Yn + beta(m) * Zn
        a = a @ np.linalg.matrix_power(K, cnt)
    a = (I7n + n * Xn) @ a
    return a

# =====================================================================================
print("\n== Part 2: all words of length n <= %d (floating point) ==" % NMAX)
angles2 = {'sqrt2': math.sqrt(2), 'golden': (math.sqrt(5) - 1) / 2, 'pi': math.pi, 'e': math.e,
           '1/3': 1 / 3, '0': 0.0, '1/2': 0.5, '2/5': 0.4, '3/8+1e-9': 3 / 8 + 1e-9,
           '1/4+2^-20': 0.25 + 2 ** -20, '0.05': 0.05, '1/7+1e-5': 1 / 7 + 1e-5, '1-2^-12': 1 - 2 ** -12}

def partitions_upto(total, maxpart):
    out = [{}]
    def rec(rem, mx, cur):
        for m in range(min(rem, mx), 0, -1):
            cur[m] = cur.get(m, 0) + 1
            out.append(dict(cur)); rec(rem - m, m, cur)
            cur[m] -= 1
            if cur[m] == 0: del cur[m]
    rec(total, maxpart, {})
    return out

LO, HI = 1e9, 0.0
for name, th in angles2.items():
    F0, F1 = pair(th)
    T = taus(th, NMAX + 2)
    cur = np.eye(22)[None]
    for n in range(1, NMAX + 1):
        cur = np.concatenate([np.einsum('ij,njk->nik', F0, cur), np.einsum('ij,njk->nik', F1, cur)])
        g = np.linalg.norm(cur, ord=2, axis=(1, 2)).max()
        Ph = Phi(T, n, M=n - 1)
        check(g <= 21 * Ph * (1 + 1e-12), name, n)                                         # Proposition 7.4
        check(n <= g * (1 + 1e-12))
        LO, HI = min(LO, g / Ph), max(HI, g / Ph)
        # Proposition 7.3(b): Gamma <= g <= max(n+1, 3 max ||a||) <= 3 sqrt7 Gamma
        Gam, amax = 0.0, 0.0
        for cnts in partitions_upto(n - 1, n - 1):
            a = coords(th, n, cnts)
            Gam = max(Gam, np.linalg.norm(a[:, 0])); amax = max(amax, np.linalg.norm(a, 2))
            # Lemma 7.5 (when applicable to cnts)
            if len(cnts) == 1:
                (m, t), = cnts.items()
                if t - 1 <= T[m] / 2:
                    check(g >= t / 2 * n * beta(m) * (1 - 1e-12))
                    if t >= 2:
                        check(g >= t * t / 8 * abs(n * beta(m) ** 2 - alpha(m) ** 2) * (1 - 1e-12))
        check(Gam <= g * (1 + 1e-12) and g <= max(n + 1, 3 * amax) * (1 + 1e-12) and max(n + 1, 3 * amax) <= 3 * math.sqrt(7) * Gam * (1 + 1e-12))
    print("    theta = %-10s  g(%d) = %9.4f" % (name, NMAX, g))
print("    over all angles and n <= %d:  %.4f <= g/Phi# <= %.4f   (Proposition 7.4: <= 21)" % (NMAX, LO, HI))
done("Propositions 7.3(b), 7.4, Lemma 7.5 (n <= %d)" % NMAX)

# =====================================================================================
print("\n== Part 3: the upper bound of Proposition 7.4 for large n ==")
worst = 0.0
for th in (math.sqrt(2), math.pi, 3 / 8 + 1e-9, 1 / 7 + 1e-5, 0.25 + 2 ** -20, 2 / 5, 0.05):
    T = taus(th, 200)
    for _ in range(40):
        n = rnd.randint(50, 10 ** 7)
        gaps = rnd.sample(range(1, min(60, n)), rnd.randint(1, 4))
        cnts, budget = {}, n - 1
        for m in gaps:
            cap = budget // m
            if cap <= 0: continue
            t = rnd.randint(1, max(1, min(cap, int(min(T[m], 10 ** 6)) + 1)))
            cnts[m] = t; budget -= t * m
        if not cnts: continue
        a = coords(th, n, cnts)
        r = 3 * np.linalg.norm(a, 2) / Phi(T, n)
        worst = max(worst, r)
        check(np.abs(a[:, 0]).sum() <= 6.8 * Phi(T, n) * (1 + 1e-9))     # l1 of the coordinates <= 6.8 Phi
print("    3 ||a_n(mu)|| / Phi# <= %.4f on random multisets (proof: <= 20.4)" % worst)
done("the upper bound in the proof of Proposition 7.4")

# =====================================================================================
print("\n== Part 4: Section 7.3 (Lemmas 7.6, 7.7 and the proof of Proposition 7.8) ==")
angles4 = []
for p in range(2, 25):
    for h in range(1, p):
        if rnd.random() < 0.3:
            for ex in (8, 12, 20, 2 * p + 2, 3 * p):
                angles4.append(mp.mpf(h) / p + mp.mpf(2) ** (-ex) * (1 if rnd.random() < .5 else -1))
angles4 += [mp.sqrt(2), mp.pi, mp.e, (mp.sqrt(5) - 1) / 2, mp.mpf(1) / 3, mp.mpf(0), mp.mpf(2) / 5]
stats = dict(res=0, nstrong=0, strong=0.0, r1=1e300, r2=1e300)
for th in angles4:
    T = taus(th, 400)
    for p in range(4, 12):
        N = Np(p); De, x = Deltap(T, p), xp(T, p)
        # Lemma 7.6
        dp = abs(p * th - mp.nint(p * th))
        if dp <= mp.mpf(2) ** -0.5 * mp.mpf(2) ** -p:
            hh = int(mp.nint(p * th)); dg = math.gcd(hh, p)
            if dg >= 2:
                pp = p // dg
                check(abs(pp * th - mp.nint(pp * th)) <= dp / dg * (1 + mp.mpf(10) ** -30), "Lemma 7.6(i)")
                check(T[pp] >= 16 / math.pi ** 2 * T[p] * (1 - 1e-12), "Lemma 7.6(i)")
            else:
                for k in range(1, 2 * p):
                    if k != p:
                        check(abs(k * th - mp.nint(k * th)) >= mp.mpf(1) / (2 * p) and T[k] <= 2 * p * p * (1 + 1e-9), "Lemma 7.6(ii)")
            stats['res'] += 1
        if De < 1:
            continue
        # Lemma 7.7 under its hypothesis Delta#_p >= 1
        R = Rp(T, p)
        check(math.gcd(int(mp.nint(p * th)), p) == 1, "Lemma 7.7(i)")
        check(all(T[k] <= 2 * p * p * (1 + 1e-9) for k in range(1, 2 * p) if k != p), "Lemma 7.7(i)")
        PN = Phi(T, N)
        check(PN <= 3 * N * x * max(1, R) * (1 + 1e-12), "Lemma 7.7(ii)")
        stats['strong'] = max(stats['strong'], PN / (N * x * max(1, R))); stats['nstrong'] += 1
        # the proof of Proposition 7.8: products with t = t_p(n) gaps of length p at n = N/2 and n = l N
        for (n, lb, tl, l) in [(N // 2, N * x * x / 1024, 4.0 ** p * x / 8, 0)] + \
                [(l * N, (l - 1) * N * x * x / 128, 4.0 ** p * x / 4, l) for l in (2, 3, 5)]:
            t = (n - 1) // p if T[p] == math.inf else min((n - 1) // p, 1 + int(T[p] // 2))
            check(t >= 2 and t >= tl * (1 - 1e-12) and t * p <= n - 1 and t - 1 <= T[p] / 2, "t in Proposition 7.8")
            e = 0.0 if T[p] == math.inf else 1.0 / T[p]
            qpow = math.exp((t - 2) * math.log1p(-e)) if e < 1 else 0.0
            crit = t * (t - 1) / 2 * qpow * abs(n * 16.0 ** -p - p * p * 4.0 ** -p)      # coordinate n z2 - y2
            check(crit >= lb * (1 - 1e-9), "Proposition 7.8: lower bound", p, n)
            r = crit / (21 * PN)
            if l == 0:
                check(r >= De / 64512 * (1 - 1e-9), "Proposition 7.8, N/2"); stats['r1'] = min(stats['r1'], r / De)
            else:
                check(r >= (l - 1) * De / 8064 * (1 - 1e-9), "Proposition 7.8, l N"); stats['r2'] = min(stats['r2'], r / ((l - 1) * De))
print("    %d angles; Lemma 7.6 in %d cases; %d cases with Delta#_p >= 1: Phi#(N)/(N x max(1,R)) <= %.4f (proof: 3)"
      % (len(angles4), stats['res'], stats['nstrong'], stats['strong']))
print("    proof of Proposition 7.8: min Gamma#(N/2)/(21 Phi#(N) Delta#_p) = %.3e (>= 1/64512 = %.3e),"
      " min Gamma#(lN)/(21 Phi#(N) (l-1) Delta#_p) = %.3e (>= 1/8064 = %.3e)" % (stats['r1'], 1 / 64512, stats['r2'], 1 / 8064))
check(stats['nstrong'] >= 30)
# constants
check(1024 * 63 == 64512 and 128 * 63 == 8064 and all(4 ** p / 8 >= 2 for p in range(4, 60)))
check(all(2 * SQ2 * p <= 2 ** p for p in range(4, 200)) and all(2 * p * p * 4.0 ** -(p + 1) <= 1 for p in range(4, 200)))
check(all(p ** 3 * (p + 1) <= p * p * 4 ** p and p ** 4 * (p + 1) <= p * p * 4 ** p for p in range(4, 200)))
done("Lemmas 7.6, 7.7 and the inequalities in the proof of Proposition 7.8")

# =====================================================================================
print("\n== Part 5: Lemma 7.9 and the numbers in the proof of Theorem 1.5 ==")
mp.mp.dps = 400
# Lemma 7.9 for a lacunary sum with p_1 = 16 and p_2 = 2^24 (exact partial sum)
ps = [16, 2 ** 24, 2 ** 52, 2 ** 108]                 # p_{j+1} >= 8 p_j^2; the last term only bounds the tail
thl = sum(mp.mpf(1) / p_ for p_ in ps)
al = lambda k: mp.mpf(2) ** k * abs(k * thl - mp.nint(k * thl))
check(all(ps[j + 1] >= 8 * ps[j] ** 2 for j in range(3)))
for j in range(2):
    p_, pn = ps[j], ps[j + 1]
    check(mp.mpf(2) ** p_ * p_ / pn < al(p_) <= mp.mpf(2) ** (p_ + 1) * p_ / pn, "Lemma 7.9(i)", j)
check(all(al(k) >= mp.mpf(2) ** k / 32 for k in range(1, 16)), "Lemma 7.9(ii)")
for k in list(range(17, 3000)) + [rnd.randrange(17, 2 ** 24) for _ in range(3000)]:
    check(al(k) >= min(mp.mpf(2) ** 16 / 16, mp.mpf(2) ** 32 / (2 * 2 ** 24)), "Lemma 7.9(iii)", k)
# theta# of Theorem 1.5: lambda_j = log2 p_j, lambda_j >= 2 j^2, and the facts used in the proof
e = [None, 4]
for j in range(1, 4): e.append(e[j] + 2 ** e[j] + j * j if j < 3 else None)
check(e[2] == 21 and all(e[j] >= 2 * j * j for j in (1, 2)))
check(e[1] + 1 + 1 <= 16 and all(2 ** (2 * j * j) >= 2 * (j + 1) ** 2 for j in range(2, 60)))
check(all(1.5 * lam + 1 <= 2 ** lam for lam in range(21, 400)))
# alpha#_k for theta# and k <= 200: theta# = 1/16 + 2^-21 + (tail < 2^-(2^21)); exact rational with error bound
th2 = Fr(1, 16) + Fr(1, 2 ** 21)
for k in range(1, 201):
    x = k * th2; d = min(x - math.floor(x), math.ceil(x) - x)
    ak = 2 ** k * d                     # the tail changes k*theta by less than 2^-(2^21) * 201, negligible here
    if k < 16: check(ak >= Fr(1, 16))
    elif k == 16: check(Fr(1, 2) <= ak <= 1)       # (2^-1, 2^0] up to the negligible tail (which is positive)
    else: check(ak >= 1)
    gam_upper = 1 / (2 * float(ak) ** 2)
    check(gam_upper <= max(128, k / 2))
# the growth bound of Theorem 1.5 at computable n (only the first resonance p_1 = 16 is visible)
thS = mp.mpf(1) / 16 + mp.mpf(2) ** -21
T = taus(thS, 300)
worstS = 0.0
for ex in np.linspace(0.3, 30, 300):
    n = max(1, int(10 ** ex))
    L = math.log2(2 * n)
    worstS = max(worstS, Phi(T, n) / (n * L * L))
    check(Phi(T, n) <= 16577 * n * L * L)
check(1 + 128 + 128 ** 2 + 64 == 16577 and 21 * 16577 <= 3.5e5)
print("    theta#: Phi#(n) / (n log2(2n)^2) <= %.4f for n <= 10^30 (proof: <= 16577)" % worstS)
# the irregularity part: Delta#_{p_j} >= 4^(2j-1)/pi^2 and the resulting ratios
for j in range(3, 8):
    check(mp.mpf(4) ** (j * j) / (2 * mp.pi ** 2) / (mp.mpf(4) ** ((j - 1) ** 2) / 2) == mp.mpf(4) ** (2 * j - 1) / mp.pi ** 2)
    check(mp.mpf(4) ** ((j - 1) ** 2) / 2 >= 128 and mp.mpf(4) ** (2 * j - 1) / mp.pi ** 2 >= 1)
done("Lemma 7.9 and the numbers in the proof of Theorem 1.5")

print("\n%d checks in %.0f s.  ALL CHECKS PASSED" % (NCHECK, time.time() - T0))
