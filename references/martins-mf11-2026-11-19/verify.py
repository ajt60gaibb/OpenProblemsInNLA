from fractions import Fraction as Fr
import math, random, sys, time
import numpy as np
import mpmath as mp

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 16
mp.mp.dps = 120
rnd = random.Random(20261111)
T0 = time.time()
NCHECK = 0


def check(cond, *msg):
    """count and assert one check"""
    global NCHECK
    NCHECK += 1
    if not cond:
        raise AssertionError(' '.join(str(m) for m in msg))


def done(text):
    print("  %-86s OK  (%.0f s)" % (text, time.time() - T0))


# =====================================================================================
# exact rational matrix helpers
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
def iszero(M): return all(x == 0 for row in M for x in row)
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
BAS = [I7, Z, ZZ, X, XZ, XZZ, Y]                 # B_1, ..., B_7

# =====================================================================================
print("== Part 1: the algebra A (Lemmas 2.1 and 2.3) -- exact ==")
# Lemma 2.1(i)
check(mul(X, Y) == mul(Y, X) and mul(X, Z) == mul(Z, X) and mul(Y, Z) == mul(Z, Y))
check(iszero(mul(X, X)) and iszero(mpow(Y, 3)) and iszero(mpow(Z, 3)) and iszero(mul(X, Y)) and iszero(mul(Y, Z)))
check(XZ == add(E(5, 1), E(6, 2)) and ZZ == add(E(3, 1), E(6, 4)))
check(XZZ == E(6, 1) and mul(Y, Y) == sc(-1, E(6, 1)))
# Lemma 2.1(ii): products of basis elements are 0 or +-B_k; the nonzero ones; B_i e_1 = e_i; ||B_i|| = 1
nonzero = {}
for i in range(7):
    for j in range(7):
        P = mul(BAS[i], BAS[j])
        hits = [(k, s) for k in range(7) for s in (1, -1) if P == sc(s, BAS[k])]
        check(iszero(P) or len(hits) == 1)
        if not iszero(P) and i > 0 and j > 0: nonzero[(i + 1, j + 1)] = hits[0]
check(set(nonzero) == {(2, 2), (2, 4), (4, 2), (2, 5), (5, 2), (3, 4), (4, 3), (7, 7)})   # Z.Z, Z.X, Z.XZ, Z^2.X, Y.Y
check(nonzero[(7, 7)] == (5, -1) and nonzero[(2, 5)] == (5, 1) and nonzero[(3, 4)] == (5, 1))
for i, B in enumerate(BAS):
    check([B[r][0] for r in range(7)] == [Fr(1) if r == i else Fr(0) for r in range(7)])
    check(abs(np.linalg.norm(np.array(B, dtype=float), 2) - 1) < 1e-12)
for _ in range(300):                                                       # (2.5)
    al = np.array([rnd.uniform(-1, 1) for _ in range(7)])
    a = sum(al[i] * np.array(BAS[i], dtype=float) for i in range(7))
    na = np.linalg.norm(a, 2)
    check(abs(np.linalg.norm(a[:, 0]) - np.linalg.norm(al)) < 1e-12)
    check(np.linalg.norm(al) <= na + 1e-12 and na <= np.abs(al).sum() + 1e-12 <= math.sqrt(7) * np.linalg.norm(al) + 2e-12)
# Lemma 2.1(iii)
for n in (0, 1, 2, 7, 19): check(mpow(U, n) == add(I7, sc(n, X)))
# Lemma 2.1(iv): V_Y = YV = span{e6, e7}, V_Z = ZV = span{e2, e3, e5, e6}, invariant under A, U = id on V_Y
EY, EZ = cols([7, 6]), cols([2, 3, 5, 6])
PY, PZ = mul(EY, tr(EY)), mul(EZ, tr(EZ))
check(mul(PY, Y) == Y and mul(PZ, Z) == Z)
check(np.linalg.matrix_rank(np.array(Y, dtype=float)) == 2 and np.linalg.matrix_rank(np.array(Z, dtype=float)) == 4)
for B in BAS:
    check(mul(PY, mul(B, EY)) == mul(B, EY) and mul(PZ, mul(B, EZ)) == mul(B, EZ))
check(mul(U, EY) == EY)
# Remark 2.2: the relations of R[x,y,z]/(x^2, xy, yz, z^3, y^2 + x z^2) hold, and A is 7-dimensional
check(iszero(add(mul(Y, Y), XZZ)))
check(np.linalg.matrix_rank(np.array([sum(B, []) for B in BAS], dtype=float)) == 7)
# products of three factors from {Y, Z} vanish (used in the proof of Lemma 2.3)
for A_ in (Y, Z):
    for B_ in (Y, Z):
        for C_ in (Y, Z): check(iszero(mul(A_, mul(B_, C_))))
# Lemma 2.3: the normal form (2.9), exact, on random data
for _ in range(80):
    h = rnd.randint(0, 6); n = rnd.randint(0, 40)
    qs = [Fr(rnd.randint(-5, 5), rnd.randint(1, 5)) for _ in range(h)]
    als = [Fr(rnd.randint(-4, 4), rnd.randint(1, 9)) for _ in range(h)]
    bes = [Fr(rnd.randint(-4, 4), rnd.randint(1, 9)) for _ in range(h)]
    lhs = mpow(U, n)
    for q, a_, b_ in zip(qs, als, bes): lhs = mul(lhs, add(sc(q, I7), sc(a_, Y), sc(b_, Z)))
    def Qx(ex):
        v = Fr(1)
        for r, q in enumerate(qs):
            if r not in ex: v *= q
        return v
    Q = Qx(())
    y1 = sum(als[i] * Qx((i,)) for i in range(h)); z1 = sum(bes[i] * Qx((i,)) for i in range(h))
    y2 = sum(als[i] * als[k] * Qx((i, k)) for i in range(h) for k in range(i + 1, h))
    z2 = sum(bes[i] * bes[k] * Qx((i, k)) for i in range(h) for k in range(i + 1, h))
    rhs = add(sc(Q, I7), sc(n * Q, X), sc(y1, Y), sc(z1, Z), sc(n * z1, XZ), sc(z2, ZZ), sc(n * z2 - y2, XZZ))
    check(lhs == rhs)
    check([lhs[r][0] for r in range(7)] == [Q, z1, z2, n * Q, n * z1, n * z2 - y2, y1])
done("Lemma 2.1 (i)-(iv), (2.5), Remark 2.2, Lemma 2.3")

# =====================================================================================
print("\n== Part 2: the matrices and the reduction of words -- exact ==")
UZ = mul(tr(EZ), mul(U, EZ))
def build(c, s):
    """S, T, J, L, F0, F1 of (3.1)-(3.5) for (cos, sin) = (c, s)"""
    cI, sI, O = sc(c, I7), sc(s, I7), zeros(7, 7)
    rot = vstack(hstack(cI, sc(-1, sI)), hstack(sI, cI))
    S = blockdiag(rot, sc(Fr(1, 2), eye(2)), sc(Fr(1, 8), eye(4))); T = blockdiag(U, U, eye(2), UZ)
    J = vstack(I7, O, mul(tr(EY), Y), mul(tr(EZ), Z)); L = hstack(I7, O, EY, EZ)
    return S, T, J, L, mul(T, S), mul(T, mul(J, mul(L, S)))
def cpow(c, s, m):
    zr, zi = Fr(1), Fr(0)
    for _ in range(m): zr, zi = zr * c - zi * s, zr * s + zi * c
    return zr
def Kmat(m, c, s): return add(sc(cpow(c, s, m), I7), sc(Fr(1, 2 ** m), Y), sc(Fr(1, 8 ** m), Z))

if True:
    for (c, s) in ((Fr(3, 5), Fr(4, 5)), (Fr(5, 13), Fr(12, 13)), (Fr(-7, 25), Fr(24, 25)), (Fr(1), Fr(0)), (Fr(0), Fr(1))):
        S, T, J, L, F0, F1 = build(c, s)
        dim = len(F0); check(dim == 20)
        check(mul(T, S) == mul(S, T) and mul(T, J) == mul(J, U) and mul(L, T) == mul(U, L))      # Lemma 3.1(i)
        Sm = eye(dim)
        for m in range(0, 9):                                                                      # Lemma 3.1(iii)
            check(mul(L, mul(Sm, J)) == Kmat(m, c, s)); Sm = mul(Sm, S)
        check(mul(F0, F1) != mul(F1, F0))                                                          # Lemma 3.1(iv)
        check(np.linalg.matrix_rank(np.array(F1, dtype=float)) == 7)
        check(abs(np.linalg.det(np.array(F0, dtype=float))) > 0)
        if s:                                                                                      # Lemma 3.1(ii)
            fS, fJ, fL = (np.array(M_, dtype=float) for M_ in (S, J, L))
            check(abs(np.linalg.norm(fS, 2) - 1) < 1e-12 and np.linalg.norm(fJ, 2) <= math.sqrt(3) + 1e-12
                  and np.linalg.norm(fL, 2) <= math.sqrt(3) + 1e-12)
        def reduce_word(letters):                         # letters[k-1] = i_k;   Proposition 3.2
            n = len(letters)
            prod_ = eye(dim)
            for i in letters: prod_ = mul(F1 if i else F0, prod_)        # F_{i_n} ... F_{i_1}
            pos = [k + 1 for k, i in enumerate(letters) if i]
            k0, kh, gaps = pos[0], pos[-1], [pos[i] - pos[i - 1] for i in range(1, len(pos))]
            check(k0 >= 1 and kh <= n and all(m >= 1 for m in gaps) and sum(gaps) == kh - k0)
            core = mpow(U, n)
            for m in reversed(gaps): core = mul(core, Kmat(m, c, s))
            check(prod_ == mul(mpow(S, n - kh), mul(J, mul(core, mul(L, mpow(S, k0))))))
            return k0, gaps, n - kh
        for _ in range(10):
            n = rnd.randint(1, 12)
            letters = [rnd.randint(0, 1) for _ in range(n)]
            if 1 not in letters: letters[rnd.randrange(n)] = 1
            reduce_word(letters)
        check(reduce_word([0, 1, 0, 0, 1, 1, 0, 1, 0]) == (2, [3, 1, 2], 1))                       # Example 3.3
        # formula (4.14) for t copies of the gap m, and the corresponding word F_1 (F_0^{m-1} F_1)^t F_0^{k_0-1}
        for m in (1, 2, 3):
            for n in (7, 13, 22):
                t = (n - 1) // m; q = cpow(c, s, m)
                core = mul(mpow(U, n), mpow(Kmat(m, c, s), t))
                check(core[4][0] == t * (q ** (t - 1) if t >= 1 else 0) * n * Fr(1, 8 ** m))
                check(core[5][0] == Fr(t * (t - 1), 2) * (q ** (t - 2) if t >= 2 else 0) * (n * Fr(1, 16 ** m) - 1) * Fr(1, 4 ** m))
                s_ = n - t * m
                W = F1; blk = mul(mpow(F0, m - 1), F1)
                for _ in range(t): W = mul(W, blk)
                W = mul(W, mpow(F0, s_ - 1))
                check(W == mul(J, mul(core, mul(L, mpow(S, s_)))))
        if True:                                                           # Appendix A
            O = zeros(7, 7)
            F0A = blockdiag(vstack(hstack(sc(c, U), sc(-s, U)), hstack(sc(s, U), sc(c, U))), sc(Fr(1, 2), eye(2)), sc(Fr(1, 8), UZ))
            Yb, Zb = mul(tr(EY), Y), mul(tr(EZ), mul(Z, U))
            F1A = mul(vstack(U, O, Yb, Zb), hstack(sc(c, I7), sc(-s, I7), sc(Fr(1, 2), EY), sc(Fr(1, 8), EZ)))
            check(F0 == F0A and F1 == F1A)
            check(Yb == [[Fr(v) for v in r] for r in ((1, 0, 0, 0, 0, 0, 0), (0, 0, 0, 0, 0, 0, -1))])
            check(Zb == [[Fr(v) for v in r] for r in ((1, 0, 0, 0, 0, 0, 0), (0, 1, 0, 0, 0, 0, 0), (1, 0, 0, 1, 0, 0, 0), (0, 1, 0, 0, 1, 0, 0))])
            check(UZ == [[Fr(v) for v in r] for r in ((1, 0, 0, 0), (0, 1, 0, 0), (1, 0, 1, 0), (0, 1, 0, 1))])
            check(mul(Y, U) == Y)
            # every entry of F0, F1 lies in {0, +-1, +-1/2, +-1/8} + {0, +-c, +-s} (Section 1.2)
            vals = {x for row in F0 + F1 for x in row}
            check(all(x in {Fr(0), Fr(1), -Fr(1), Fr(1, 2), -Fr(1, 2), Fr(1, 8), -Fr(1, 8), c, -c, s, -s} for x in vals))
done("Lemma 3.1, Proposition 3.2, Example 3.3, (4.14), Appendix A")

# =====================================================================================
# floating point tools used in Parts 3-7
# =====================================================================================
fl = lambda M: np.array(M, dtype=float)
Xn, Yn, Zn, Un, EYn, EZn, UZn = map(fl, (X, Y, Z, U, EY, EZ, UZ))
BASn = [fl(B) for B in BAS]
EULER = math.e


class Ang:
    """theta = h/p + delta (hp = (h, p)) or theta given directly; accurate 1 - |cos(pi m theta)|"""
    def __init__(self, name, theta=None, hp=None, delta=0):
        self.name, self.hp = name, hp
        self.delta = mp.mpf(delta)
        self.theta = mp.mpf(theta) if hp is None else mp.mpf(hp[0]) / hp[1] + self.delta
        self.rational = (hp is not None and delta == 0)
        self._e, self._ef, self._s = {}, {}, {}
    def eps_mp(self, m):
        if m not in self._e:
            if self.hp is not None and m % self.hp[1] == 0 and abs(m * self.delta) < mp.mpf(1) / 2:
                self._e[m] = 2 * mp.sin(mp.pi * m * self.delta / 2) ** 2     # = 1 - cos(pi m delta), no cancellation
            else:
                self._e[m] = 1 - abs(mp.cos(mp.pi * m * self.theta))
        return self._e[m]
    def dz_mp(self, m):
        if self.hp is not None and m % self.hp[1] == 0 and abs(m * self.delta) < mp.mpf(1) / 2:
            return abs(m * self.delta)
        x = m * self.theta
        return abs(x - mp.nint(x))
    def eps(self, m):
        if m not in self._ef: self._ef[m] = float(self.eps_mp(m))
        return self._ef[m]
    def tau(self, m):
        e = self.eps_mp(m)
        return math.inf if e == 0 else min(float(1 / e), 1e300)
    def qsign(self, m):
        if m not in self._s: self._s[m] = 1.0 if mp.cos(mp.pi * m * self.theta) >= 0 else -1.0
        return self._s[m]
    def taus(self, M): return np.array([math.inf] + [self.tau(m) for m in range(1, M + 1)])


def qpow(ang, m, r):
    """q_m^r in floating point, with |q_m|^r = exp(r log(1 - eps_m))"""
    if r == 0: return 1.0
    e = ang.eps(m)
    if e >= 1: return 0.0
    return (ang.qsign(m) ** (r % 2)) * math.exp(r * math.log1p(-e))


def coeffs(ang, n, counts):
    """the vector a_n(mu) e_1 = (P, z1, z2, nP, n z1, n z2 - y2, y1) of (3.10), for the multiset mu given by
    counts {m: c}; the critical coordinate is summed pair type by pair type, as in (3.10), to avoid cancellation"""
    ms = sorted(m for m, c in counts.items() if c > 0)
    def Qwo(red):
        v = 1.0
        for m in ms:
            v *= qpow(ang, m, counts[m] - red.get(m, 0))
        return v
    Q = Qwo({})
    y1 = sum(counts[m] * 2.0 ** -m * Qwo({m: 1}) for m in ms)
    z1 = sum(counts[m] * 8.0 ** -m * Qwo({m: 1}) for m in ms)
    y2 = z2 = crit = 0.0
    for i, m in enumerate(ms):
        cm = counts[m]
        if cm >= 2:
            w = cm * (cm - 1) / 2 * Qwo({m: 2})
            y2 += w * 4.0 ** -m; z2 += w * 64.0 ** -m
            crit += w * 4.0 ** -m * (n * 16.0 ** -m - 1)
        for m2 in ms[i + 1:]:
            w = cm * counts[m2] * Qwo({m: 1, m2: 1}); s_ = m + m2
            y2 += w * 2.0 ** -s_; z2 += w * 8.0 ** -s_
            crit += w * 2.0 ** -s_ * (n * 4.0 ** -s_ - 1)
    return np.array([Q, z1, z2, n * Q, n * z1, crit, y1])


def opnorm(vec):
    scl = float(np.max(np.abs(vec)))
    if scl == 0: return 0.0
    return scl * float(np.linalg.norm(sum((v / scl) * B for v, B in zip(vec, BASn)), 2))


def Mtrunc(n):
    """gap lengths m > Mtrunc(n) change Phi_theta(n) by a relative amount below 2^-24 (they are ignored)"""
    return int(min(n - 1, int(3 * math.log2(max(n, 2))) + 25))


def phi_data(taus, n, M=None):
    """the three terms of Phi_theta(n) (4.4), using gap lengths m <= M, and the matrix of the pair terms"""
    M = Mtrunc(n) if M is None else M
    if M < 1: return dict(n=float(n), mid=0.0, H=np.zeros((0, 0)), nu=np.zeros(0), M=0, Phi=float(n), L=float(n))
    m = np.arange(1, M + 1, dtype=float)
    nu = np.minimum(n / m, taus[1:M + 1])
    mid = n * float(np.max(nu * 8.0 ** -m))
    s_ = m[:, None] + m[None, :]
    psi = 2.0 ** -s_ * np.abs(n * 4.0 ** -s_ - 1)
    H = np.triu(nu[:, None] * nu[None, :] * psi)
    return dict(n=float(n), mid=mid, H=H, nu=nu, M=M, L=float(n) + mid, Phi=float(n) + mid + float(H.max()))


def Phi(taus, n): return phi_data(taus, n)['Phi']


def xK(ang, p):
    """x_p, R_p and Delta_p of (5.1)"""
    x = min(ang.tau(p), 16.0 ** p / p) / 8.0 ** p
    K = max([ang.tau(k) / 8.0 ** k for k in range(1, p)], default=0.0)
    return x, K, x / max(1.0, K)


# =====================================================================================
print("\n== Part 3: all words of length n <= %d (floating point) ==" % NMAX)
def bd(*Ms):
    n = sum(M.shape[0] for M in Ms); out = np.zeros((n, n)); o = 0
    for M in Ms:
        k = M.shape[0]; out[o:o + k, o:o + k] = M; o += k
    return out
def pair(theta):
    c, s = math.cos(math.pi * theta), math.sin(math.pi * theta); I, O = np.eye(7), np.zeros((7, 7))
    S = bd(np.block([[c * I, -s * I], [s * I, c * I]]), np.eye(2) / 2, np.eye(4) / 8)
    T = bd(Un, Un, np.eye(2), UZn)
    J = np.vstack([I, O, EYn.T @ Yn, EZn.T @ Zn]); L = np.hstack([I, O, EYn, EZn])
    return S, T, J, L, T @ S, T @ J @ L @ S
def partitions_upto(total, maxpart):
    yield ()
    for first in range(min(total, maxpart), 0, -1):
        for rest in partitions_upto(total - first, first): yield (first,) + rest
def Kfl(theta, m): return math.cos(math.pi * m * theta) * np.eye(7) + 2.0 ** -m * Yn + 8.0 ** -m * Zn

ANGLES3 = [Ang("theta_star", hp=(65, 256), delta=mp.mpf(4) ** -256), Ang("sqrt(2)", theta=mp.sqrt(2)),
           Ang("golden mean", theta=(1 + mp.sqrt(5)) / 2), Ang("pi", theta=mp.pi), Ang("e", theta=mp.e),
           Ang("1/3", hp=(1, 3)), Ang("0", hp=(0, 1)), Ang("1/2", hp=(1, 2)), Ang("2/5", hp=(2, 5)),
           Ang("1/10 + 2^-80", hp=(1, 10), delta=mp.mpf(2) ** -80), Ang("1/7 + 10^-5", hp=(1, 7), delta=mp.mpf(10) ** -5),
           Ang("3/8 + 10^-9", hp=(3, 8), delta=mp.mpf(10) ** -9), Ang("1/4 + 2^-20", hp=(1, 4), delta=mp.mpf(2) ** -20),
           Ang("0.05", hp=(1, 20)), Ang("0.01 + 2^-30", hp=(1, 100), delta=mp.mpf(2) ** -30), Ang("1 - 2^-12", hp=(1, 1), delta=-mp.mpf(2) ** -12)]
check(len(ANGLES3) == 16)
ratio_lo, ratio_hi, op_hi = math.inf, 0.0, 0.0
for ang in ANGLES3:
    theta = float(ang.theta)
    S_, T_, J_, L_, F0, F1 = pair(theta)
    level = np.eye(20)[None]; g = [None]
    for n in range(1, NMAX + 1):
        level = np.concatenate([F0 @ level, F1 @ level], axis=0)
        g.append(float(np.linalg.norm(level, ord=2, axis=(1, 2)).max()))
    del level
    taus = ang.taus(80)
    for n in range(1, NMAX + 1):
        gn = g[n]
        check(n - 1e-9 <= gn <= 6 * n ** 3 + 1e-9, "Proposition 4.4", ang.name, n)
        nU = np.linalg.norm(np.linalg.matrix_power(Un, n), 2)
        check(n - 1e-9 <= nU <= n + 1 + 1e-9 and abs(np.linalg.norm(np.linalg.matrix_power(F0, n), 2) - nU) < 1e-9)   # Cor. 3.4(ii)
        d = phi_data(taus, n, M=n - 1); P = d['Phi']; nu = d['nu']
        check(gn <= 20 * P * (1 + 1e-9), "Proposition 4.4", ang.name, n)
        ratio_lo, ratio_hi = min(ratio_lo, gn / P), max(ratio_hi, gn / P)
        # Lemma 4.5(a), all admissible parameters, and Lemma 4.5(b)
        for m in range(1, n):
            for t in range(1, (n - 1) // m + 1):
                if t - 1 > taus[m] / 2: break
                check(gn >= t / 2 * n * 8.0 ** -m * (1 - 1e-9), "Lemma 4.5(a)", ang.name, n, m, t)
                if t >= 2: check(gn >= t * t / 8 * 2.0 ** (-2 * m) * abs(n * 4.0 ** (-2 * m) - 1) * (1 - 1e-9) - 1e-12)
            tb = (n - 1) // m if taus[m] == math.inf else min((n - 1) // m, 1 + int(taus[m] // 2))
            check(tb >= 1 and tb * m <= n - 1 and tb - 1 <= taus[m] / 2 and tb >= nu[m - 1] / 4 * (1 - 1e-12), "Lemma 4.5(b)")
        # Corollary 3.4(iii), Lemma 4.3 and the proof of Proposition 4.4, for every gap sequence
        Unn = np.linalg.matrix_power(Un, n); G1 = Gop = 0.0
        XW = (lambda m: 2.0 ** -m, lambda m: 8.0 ** -m, lambda m: 1.0 / m)
        WW = (lambda m, k: 8.0 ** -(m + k), lambda m, k: 2.0 ** -(m + k) * abs(n * 4.0 ** -(m + k) - 1), lambda m, k: 1.0 / (m * k))
        RX = [max([nu[m - 1] * xw(m) for m in range(1, n)], default=0) for xw in XW]
        RW = [max([nu[a - 1] * nu[b - 1] * ww(a, b) for a in range(1, n) for b in range(a, n)], default=0) for ww in WW]
        A_n = max([nu[m - 1] * 2.0 ** -m for m in range(1, n)], default=0.0)
        B_n = max([nu[m - 1] * 8.0 ** -m for m in range(1, n)], default=0.0)
        for mu in partitions_upto(n - 1, n - 1):
            core = Unn.copy()
            for m in mu: core = core @ Kfl(theta, m)
            vec = core[:, 0]; nc = float(np.linalg.norm(core, 2)); l1 = float(np.abs(vec).sum())
            G1 = max(G1, float(np.linalg.norm(vec))); Gop = max(Gop, nc)
            counts = {}
            for m in mu: counts[m] = counts.get(m, 0) + 1
            check(np.allclose(coeffs(ang, n, counts), vec, rtol=1e-9, atol=1e-9 * max(1.0, l1)), "coeffs vs (3.10)")
            check(nc <= l1 * (1 + 1e-12) + 1e-12 and l1 <= 6.12 * P, "Proposition 4.4", ang.name, n, mu)
            op_hi = max(op_hi, 3 * nc / P)
            # Lemma 4.3 with several weights; the sums are evaluated with the closed forms of (2.8)
            ms = sorted(counts)
            def Qwo(red): return float(np.prod([qpow(ang, m, counts[m] - red.get(m, 0)) for m in ms]))
            for xw, rx in zip(XW, RX):
                lhs = sum(counts[m] * abs(Qwo({m: 1})) * xw(m) for m in ms)
                check(lhs <= EULER * rx * (1 + 1e-9) + 1e-12, "(4.9)")
            for ww, rw in zip(WW, RW):
                lhs = 0.0
                for i, m in enumerate(ms):
                    if counts[m] >= 2: lhs += counts[m] * (counts[m] - 1) / 2 * abs(Qwo({m: 2})) * ww(m, m)
                    for m2 in ms[i + 1:]: lhs += counts[m] * counts[m2] * abs(Qwo({m: 1, m2: 1})) * ww(m, m2)
                check(lhs <= 2 * EULER * rw * (1 + 1e-9) + 1e-12, "(4.10)")
            # the coordinate bounds in the proof of Proposition 4.4
            check(abs(vec[6]) <= EULER * A_n + 1e-9 and abs(vec[1]) <= EULER * B_n + 1e-12 and abs(vec[2]) <= 2 * EULER * B_n ** 2 + 1e-12)
            check(abs(vec[5]) <= 2 * EULER * (d['H'].max() if d['H'].size else 0) + 1e-9)
            # the polynomial bound in the proof of Proposition 4.4
            Aa = sum(2.0 ** -m for m in mu); Bb = sum(8.0 ** -m for m in mu)
            check(l1 <= (n + 1) * (1 + Bb + Bb * Bb / 2) + Aa + Aa * Aa / 2 + 1e-9 <= (n + 1) * (n * n + 30 * n + 33) / 64 + 1e-9)
        check(G1 - 1e-9 <= gn <= max(n + 1, 3 * Gop) + 1e-9 <= 3 * math.sqrt(7) * G1 + 2e-9, "Corollary 3.4(iii)")
    # Corollary 3.4(i) word by word:  ||a_n(mu) e_1|| <= ||F_{i_n}...F_{i_1}|| <= 3 ||a_n(mu)||
    for n in range(1, min(NMAX, 10) + 1):
        Unn = np.linalg.matrix_power(Un, n)
        for code in range(1, 2 ** n):
            letters = [(code >> k) & 1 for k in range(n)]                  # letters[k-1] = i_k
            Pw = np.eye(20)
            for i in letters: Pw = (F1 if i else F0) @ Pw
            pos = [k + 1 for k, i in enumerate(letters) if i]
            core = Unn.copy()
            for j in range(1, len(pos)): core = core @ Kfl(theta, pos[j] - pos[j - 1])
            nw = np.linalg.norm(Pw, 2)
            check(np.linalg.norm(core[:, 0]) - 1e-9 <= nw <= 3 * np.linalg.norm(core, 2) + 1e-9, "Corollary 3.4(i)")
    print("    theta = %-14s g(%d) = %9.4f   g/Phi in [%.3f, %.3f]" %
          (ang.name, NMAX, g[NMAX], min(g[n] / Phi(taus, n) for n in range(1, NMAX + 1)),
           max(g[n] / Phi(taus, n) for n in range(1, NMAX + 1))))
print("    over all sixteen angles and n <= %d:  %.4f <= g/Phi <= %.4f,   3 ||a_n(mu)|| / Phi <= %.4f" % (NMAX, ratio_lo, ratio_hi, op_hi))
done("Proposition 4.4, Corollary 3.4, Lemmas 4.3 and 4.5 (n <= %d)" % NMAX)

# =====================================================================================
print("\n== Part 4: Lemmas 4.2, 4.3, the proof of Proposition 4.4 and Lemma 4.5 for large n ==")
# ---- Lemma 4.2
for _ in range(4000):
    x = mp.mpf(rnd.uniform(-3, 3)) * mp.mpf(10) ** -rnd.choice([0, 0, 1, 3, 8, 30]); dd = abs(x - mp.nint(x))
    v = 1 - abs(mp.cos(mp.pi * x))
    if dd < mp.mpf(10) ** -20: v = 2 * mp.sin(mp.pi * dd / 2) ** 2       # the same number, without cancellation
    check(2 * dd ** 2 <= v * (1 + mp.mpf(10) ** -60) and v <= mp.pi ** 2 / 2 * dd ** 2 * (1 + mp.mpf(10) ** -60))
    e = mp.mpf(rnd.random()) ** rnd.choice([1, 3, 10]); c = rnd.choice([0, 1, 2, 3, 5, 10, 100, 10 ** 4, 10 ** 8])
    if e > 0:
        check(1 - c * e <= (1 - e) ** c * (1 + mp.mpf(10) ** -60) and (1 - e) ** c <= mp.exp(-c * e) * (1 + mp.mpf(10) ** -60))
done("Lemma 4.2")

ANGLES4 = [Ang("sqrt(2)", theta=mp.sqrt(2)), Ang("golden mean", theta=(1 + mp.sqrt(5)) / 2),
           Ang("1/10 + 2^-80", hp=(1, 10), delta=mp.mpf(2) ** -80), Ang("3/7 + 2^-40", hp=(3, 7), delta=mp.mpf(2) ** -40),
           Ang("1/3", hp=(1, 3)), Ang("1/5 + 2^-14", hp=(1, 5), delta=mp.mpf(2) ** -14),
           Ang("theta_star", hp=(65, 256), delta=mp.mpf(4) ** -256), Ang("1/4 + 2^-16", hp=(1, 4), delta=mp.mpf(2) ** -16),
           Ang("5/12 + 2^-60", hp=(5, 12), delta=mp.mpf(2) ** -60), Ang("1/6 + 2^-9", hp=(1, 6), delta=mp.mpf(2) ** -9)]
NS4 = [10 ** 3, 16 ** 5, 16 ** 7 + 5, 16 ** 10 // 2, 16 ** 10, 2 * 16 ** 10, 3 * 10 ** 14, 16 ** 12]


def random_counts(ang, n, gapset):
    budget = n - 1; cnts = {}
    for _ in range(rnd.randrange(0, 7)):
        m = rnd.choice(gapset)
        if budget // m == 0: continue
        t = ang.tau(m)
        cand = [1, 2, 3, 10, 100, budget // m, budget // (2 * m) + 1, rnd.randrange(1, budget // m + 1)]
        if t < 1e18: cand += [int(t) + 1, int(t / 2) + 1, int(2 * t) + 1]
        c = min(rnd.choice(cand), budget // m); cnts[m] = cnts.get(m, 0) + c; budget -= m * c
    return cnts


def climb(ang, n, cnts, gapset, iters, P):
    """local search for large ||a_n(mu)||, starting from cnts"""
    best = opnorm(coeffs(ang, n, cnts)); bestc = cnts
    for _ in range(iters):
        c2 = dict(bestc); m = rnd.choice(gapset)
        free = n - 1 - sum(k * v for k, v in c2.items()) + m * c2.get(m, 0)
        if free // m == 0: continue
        t = ang.tau(m); cand = [0, 1, 2, free // m, free // (2 * m), rnd.randrange(0, free // m + 1)]
        if t < 1e18: cand += [int(t), int(t / 2) + 1, int(2 * t)]
        c2[m] = max(0, min(rnd.choice(cand), free // m))
        v = opnorm(coeffs(ang, n, c2))
        if v > best: best, bestc = v, c2
    return best, bestc


worst_l1, worst_op, n_mult = 0.0, 0.0, 0
for ang in ANGLES4:
    taus = ang.taus(400)
    for n in NS4:
        d = phi_data(taus, n); P = d['Phi']; M = d['M']; nu = d['nu']
        gapset = list(range(1, 25)) + [30, 40, 50, 64, 100]
        if ang.hp is not None: gapset += [ang.hp[1] * k for k in (1, 2, 3) if ang.hp[1] * k <= M]
        gapset = sorted(set(m for m in gapset if m <= M))
        for trial in range(14):
            cnts = random_counts(ang, n, gapset)
            if trial % 2: _, cnts = climb(ang, n, cnts, gapset, 12, P)
            vec = coeffs(ang, n, cnts); l1 = float(np.abs(vec).sum()); op = opnorm(vec); n_mult += 1
            check(op <= l1 * (1 + 1e-9) and l1 <= 6.12 * P * (1 + 1e-6), "Proposition 4.4", ang.name, n, cnts)
            worst_l1, worst_op = max(worst_l1, 3 * l1 / P), max(worst_op, 3 * op / P)
            # Lemma 4.3 for this multiset (weights 2^-m, 8^-m, 8^-(m+m'), psi_n(m+m'))
            ms = sorted(m for m in cnts if cnts[m] > 0)
            def Qwo(red): return float(np.prod([qpow(ang, m, cnts[m] - red.get(m, 0)) for m in ms]))
            for base in (2.0, 8.0):
                lhs = sum(cnts[m] * abs(Qwo({m: 1})) * base ** -m for m in ms)
                check(lhs <= EULER * float(np.max(nu * base ** -np.arange(1, M + 1))) * (1 + 1e-9), "(4.9) large n")
            for kind in (0, 1):
                lhs = 0.0
                for i, m in enumerate(ms):
                    for m2 in ms[i:]:
                        cnt = cnts[m] * (cnts[m] - 1) / 2 if m2 == m else cnts[m] * cnts[m2]
                        if cnt == 0: continue
                        w = 8.0 ** -(m + m2) if kind == 0 else 2.0 ** -(m + m2) * abs(n * 4.0 ** -(m + m2) - 1)
                        lhs += cnt * abs(Qwo({m: 2} if m2 == m else {m: 1, m2: 1})) * w
                mm = np.arange(1, M + 1, dtype=float); s_ = mm[:, None] + mm[None, :]
                W = 8.0 ** -s_ if kind == 0 else 2.0 ** -s_ * np.abs(n * 4.0 ** -s_ - 1)
                check(lhs <= 2 * EULER * float(np.max(np.triu(nu[:, None] * nu[None, :] * W))) * (1 + 1e-9), "(4.10) large n")
        # Lemma 4.5: the products with one gap length m and t = t_m(n) gaps
        def t_j(m, j):
            v = (n - 1) // (j * m)
            return v if taus[m] == math.inf else min(v, 1 + int(taus[m] // 2))
        for m in range(1, M + 1):
            t = t_j(m, 1); vec = coeffs(ang, n, {m: t})
            check(t >= nu[m - 1] / 4 * (1 - 1e-12), "Lemma 4.5(b)")
            check(abs(vec[4]) >= nu[m - 1] * n * 8.0 ** -m / 8 * (1 - 1e-9), "Lemma 4.5")
            if t >= 2: check(abs(vec[5]) >= nu[m - 1] ** 2 * 2.0 ** (-2 * m) * abs(n * 4.0 ** (-2 * m) - 1) / 128 * (1 - 1e-9))
print("    %d multisets: 3 l1(a_n(mu)) / Phi <= %.4f (proof: <= 18.36),  3 ||a_n(mu)|| / Phi <= %.4f" % (n_mult, worst_l1, worst_op))
done("Lemma 4.3, the proof of Proposition 4.4 and Lemma 4.5 for large n")

# =====================================================================================
print("\n== Part 5: Section 5 (Lemmas 5.1, 5.2 and the proof of Proposition 5.3) ==")
# constants used in Section 5
check(all(2 * math.sqrt(2) * p * 8.0 ** (-p / 2) <= 1 + 1e-15 for p in range(1, 200)))            # Lemma 5.1(ii)
check(all(2 * p * p <= 8 ** (p + 1) and p * p * 2 ** p <= 16 ** p and 4 * p ** 4 * 2.0 ** (-2 * p - 1) <= 16 ** p
          and p * 16 ** p * 2.0 ** (-2 * p - 1) <= 16 ** p and 16 ** p / (4 * p * p) <= 16 ** p
          for p in range(1, 200)))                                                                   # Lemma 5.2(ii)
check(1024 * 60 == 61440 and 128 * 60 == 7680 and all(8 ** p / 8 >= 2 for p in range(2, 60)))      # Proposition 5.3

# the angles used in this part: h/p + delta for many p, h, delta (including h not coprime to p), and a few others
ANG5 = []
for p in (1, 2, 3, 4, 5, 6, 7, 8, 10, 12):
    hs = sorted(set([0 if p == 1 else 1, p - 1 if p > 1 else 0, 2 % p, (p // 2) if p > 2 else 0]))
    for h in hs:
        for k in (0.5 * p, 1.0 * p, 1.5 * p, 1.5 * p + 2, 2.0 * p, 3.0 * p, 5.0 * p, None):
            if k is not None and k < 1.5: continue
            delta = mp.mpf(0) if k is None else mp.mpf(2) ** -mp.mpf(k) * rnd.choice([1, -1]) * mp.mpf(rnd.uniform(0.5, 1))
            ANG5.append(Ang("%d/%d%+.3g" % (h, p, float(delta)), hp=(h, p), delta=delta))
ANG5 += [Ang("sqrt(2)", theta=mp.sqrt(2)), Ang("golden mean", theta=(1 + mp.sqrt(5)) / 2), Ang("pi", theta=mp.pi),
         Ang("theta_star", hp=(65, 256), delta=mp.mpf(4) ** -256)]
PMAX5 = 9
cnt = dict(res=0, strong=0, dips=0)
min_r1, min_r2 = math.inf, math.inf
for ang in ANG5:
    taus = ang.taus(400)
    for p in range(1, PMAX5 + 1):
        N = 16 ** p
        x, K, De = xK(ang, p)
        # Lemma 5.1
        if ang.dz_mp(p) <= mp.mpf(2) ** -0.5 * mp.mpf(8) ** (-mp.mpf(p) / 2) and ang.hp is not None:
            hh = int(mp.nint(p * ang.theta)); dgc = math.gcd(hh, p)
            if dgc >= 2:
                check(ang.dz_mp(p // dgc) <= ang.dz_mp(p) / dgc * (1 + mp.mpf(10) ** -50), "Lemma 5.1(i)")
                check(ang.tau(p // dgc) >= 16 / math.pi ** 2 * ang.tau(p) * (1 - 1e-12), "Lemma 5.1(i)")
            else:
                for k in range(1, 2 * p):
                    if k != p: check(ang.dz_mp(k) >= mp.mpf(1) / (2 * p) and ang.tau(k) <= 2 * p * p * (1 + 1e-12), "Lemma 5.1(ii)")
            cnt['res'] += 1
        if De < 1:
            continue
        # Lemma 5.2 under its hypothesis Delta_p >= 1
        hh = int(mp.nint(p * ang.theta))
        check(p == 1 or math.gcd(hh, p) == 1, "Lemma 5.2(i)", ang.name, p)
        check(all(taus[k] <= 2 * p * p * (1 + 1e-12) for k in range(1, 2 * p) if k != p), "Lemma 5.2(i)", ang.name, p)
        dN = phi_data(taus, N); PN = dN['Phi']
        check(dN['L'] <= 2 * N * x * (1 + 1e-9) and dN['H'].max() <= N * x * max(1, K) * (1 + 1e-9)
              and PN <= 3 * N * x * max(1, K) * (1 + 1e-9), "Lemma 5.2(ii)", ang.name, p)
        cnt['strong'] += 1
        if p < 2:
            continue
        # the proof of Proposition 5.3: products with t = t_p(n) gaps of length p at n = N/2 and n = l N
        for (n, lb, tl, l) in [(N // 2, N * x * x / 1024, 8.0 ** p * x / 8, 0)] + \
                [(l * N, (l - 1) * N * x * x / 128, 8.0 ** p * x / 4, l) for l in (2, 3, 5)]:
            t = (n - 1) // p if taus[p] == math.inf else min((n - 1) // p, 1 + int(taus[p] // 2))
            check(t >= 2 and t >= tl * (1 - 1e-12) and t * p <= n - 1 and t - 1 <= taus[p] / 2, "t in Proposition 5.3")
            crit = abs(float(coeffs(ang, n, {p: t})[5]))
            check(crit >= lb * (1 - 1e-9), "Proposition 5.3: lower bound", ang.name, p, n)
            # with Proposition 4.4 and Lemma 5.2(ii): the ratios of (5.2)
            if l == 0:
                r = crit / (20 * PN); check(r >= De / 61440 * (1 - 1e-9), "(5.2), N/2"); min_r1 = min(min_r1, r / De)
            else:
                r = crit / (20 * PN); check(r >= (l - 1) * De / 7680 * (1 - 1e-9), "(5.2), l N"); min_r2 = min(min_r2, r / ((l - 1) * De))
        cnt['dips'] += 1
print("    %d angles; checks: %s" % (len(ANG5), cnt))
print("    proof of Proposition 5.3:  min Gamma(N/2) / (20 Phi(N) Delta_p) = %.3e (proof: >= 1/61440 = %.3e),"
      % (min_r1, 1 / 61440))
print("                               min Gamma(lN) / (20 Phi(N) (l-1) Delta_p) = %.3e (proof: >= 1/7680 = %.3e)"
      % (min_r2, 1 / 7680))
check(cnt['strong'] >= 50 and cnt['dips'] >= 30)
done("Lemmas 5.1, 5.2 and the inequalities in the proof of Proposition 5.3")

# =====================================================================================
print("\n== Part 6: Lemma 5.5 and the numbers in the proof of Theorem 1.3 ==")
mp.mp.dps = 450
# ---- Lemma 5.5 for theta_star and for a sequence with p_{j+1} = 8 p_j^2
seqs = {"theta_star": [4, 4 ** 4, 4 ** 256],                 # the next term 4^(4^256) contributes < 10^(-10^150)
        "8p^2": [4, 128, 131072, 8 * 131072 ** 2, 8 * (8 * 131072 ** 2) ** 2]}
for name, ps in seqs.items():
    th = sum(Fr(1, p_) for p_ in ps)                    # exact partial sum; the omitted tail is < 2 / p_{last+1}
    thm = mp.mpf(th.numerator) / th.denominator
    for j in range(len(ps) - 1):
        p_ = ps[j]; pn = ps[j + 1]
        check(pn >= 8 * p_ * p_ and (p_ & (p_ - 1)) == 0, "Lemma 5.5 hypotheses", name)
        hj = sum(Fr(p_, ps[i]) for i in range(j + 1)); check(hj.denominator == 1 and hj.numerator % 2 == 1)
        diff = th - hj / p_                              # theta - h_j/p_j, without the omitted positive tail
        tail_bound = Fr(2, ps[-1]) * Fr(1, 8 * ps[-1])   # the omitted tail is < 2/p_{last+1} <= 2/(8 p_last^2)
        check(Fr(1, pn) <= diff and (diff > Fr(1, pn) or j == len(ps) - 2), "(5.3)", name, j)
        check(diff + tail_bound <= Fr(2, pn) <= Fr(1, 4 * p_ * p_), "(5.3)", name, j)
        check(mp.nint(p_ * thm) == hj.numerator, "Lemma 5.5(i): h_j is the integer nearest to p_j theta")
        if 2 * p_ <= 20000:
            ks = range(1, 2 * p_)
        else:
            ks = list(range(1, 5001)) + list(range(p_ - 2000, p_ + 2000)) + [rnd.randrange(1, 2 * p_) for _ in range(3000)]
        for k in ks:
            if k == p_: continue
            check(abs(k * thm - mp.nint(k * thm)) >= mp.mpf(1) / (2 * p_), "Lemma 5.5(ii)", name, k)
done("Lemma 5.5 (i), (ii) for theta_star and p_{j+1} = 8 p_j^2")

# ---- the proof of Theorem 1.3: Delta_p(theta_star) for p = p_2 = 256, and the constants
ast = Ang("theta_star", hp=(65, 256), delta=mp.mpf(4) ** -256)
p = 256
tau_p = 1 / ast.eps_mp(p)
x_p = min(tau_p, mp.mpf(16) ** p / p) / mp.mpf(8) ** p
R_p = max(1 / ast.eps_mp(k) / mp.mpf(8) ** k for k in range(1, p))
De = x_p / max(1, R_p)
check(math.gcd(int(mp.nint(p * ast.theta)), p) == 1)
check(R_p <= mp.mpf(p) ** 2 / 4 and all(1 / ast.eps_mp(k) <= 2 * p * p for k in range(1, p)))
check(ast.dz_mp(p) <= 2 * p * mp.mpf(4) ** -p <= mp.mpf(2) ** -0.5 * mp.mpf(8) ** (-mp.mpf(p) / 2))
check(tau_p >= mp.mpf(16) ** p / (2 * mp.pi ** 2 * p ** 2) and mp.mpf(16) ** p / (2 * mp.pi ** 2 * p ** 2) < mp.mpf(16) ** p / p)
check(x_p >= mp.mpf(2) ** p / (2 * mp.pi ** 2 * p ** 2))
check(De >= mp.mpf(2) ** (p + 1) / (mp.pi ** 2 * p ** 4) >= 1)
check(61440 * math.pi ** 2 / 2 <= 4e5 and 7680 * math.pi ** 2 / 2 <= 4e5)
fac = mp.mpf(2) ** 256 / (4 * 10 ** 5 * mp.mpf(256) ** 4); check(fac > mp.mpf(10) ** 61)
print("    theta_star, p = 256:  Delta_p = %s >= 2^(p+1)/(pi^2 p^4) = %s;  2^p/(4e5 p^4) = %s" %
      (mp.nstr(De, 6), mp.nstr(mp.mpf(2) ** (p + 1) / (mp.pi ** 2 * p ** 4), 6), mp.nstr(fac, 6)))
done("the bound for Delta_256(theta_star) and the constants in the proof of Theorem 1.3")
mp.mp.dps = 120

# =====================================================================================
print("\n== Part 7: the invariant subspaces of Remark 9.1 ==")
# ---- Remark 9.1: the invariant flag W > mW > m^2 W > m^3 W > 0 and product boundedness on the quotients
def act(a): return bd(a, a, EYn.T @ a @ EYn, EZn.T @ a @ EZn)       # componentwise action of a in A on W
def colspace(mats):
    Mx = np.hstack(mats); u, s_, vt = np.linalg.svd(Mx); r = int((s_ > 1e-9).sum()); return u[:, :r]
mid_basis = [act(B) for B in BASn[1:]]                                # the ideal m = span{B_2, ..., B_7}
W1 = colspace(mid_basis)
W2 = colspace([act(a @ b) for a in BASn[1:] for b in BASn[1:]])
W3 = colspace([act(a @ b @ c) for a in BASn[1:] for b in BASn[1:] for c in BASn[1:]])
check([20, W1.shape[1], W2.shape[1], W3.shape[1]] == [20, 16, 7, 2], [W1.shape[1], W2.shape[1], W3.shape[1]])
for theta in (math.sqrt(2), 1 / 3, 0.1):
    S_, T_, J_, L_, F0, F1 = pair(theta)
    for Wk in (W1, W2, W3):
        Pk = Wk @ Wk.T
        for F in (F0, F1): check(np.allclose(Pk @ F @ Wk, F @ Wk, atol=1e-10))
    flags = [np.eye(20), W1, W2, W3, np.zeros((20, 0))]
    for k in range(4):
        hi, lo = flags[k], flags[k + 1]
        Plo = lo @ lo.T if lo.shape[1] else np.zeros((20, 20))
        Q_ = colspace([(np.eye(20) - Plo) @ hi])                     # orthonormal basis of the quotient
        worst = 0.0
        for _ in range(60):
            n = rnd.randint(1, 200); Pw = np.eye(20)
            for _ in range(n): Pw = (F1 if rnd.random() < 0.5 else F0) @ Pw
            worst = max(worst, np.linalg.norm(Q_.T @ (np.eye(20) - Plo) @ Pw @ Q_, 2))
        check(worst <= 3 + 1e-9, "Remark 9.1 product bounded quotient", k, worst)
done("Remark 9.1")

print("\n%d checks in %.0f s.  ALL CHECKS PASSED" % (NCHECK, time.time() - T0))
