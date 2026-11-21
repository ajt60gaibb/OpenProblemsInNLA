import sys, math, random, time
from fractions import Fraction as Fr
import numpy as np
import mpmath as mp
import sympy


# ======================================================================================
# The maps of Sections 2, 3 and 6.1 (exact rational arithmetic, with floating point versions)
# ======================================================================================
# ---------------------------------------------------------------- exact helpers
def zeros(r, c): return [[Fr(0)] * c for _ in range(r)]
def eye(n):
    M = zeros(n, n)
    for i in range(n): M[i][i] = Fr(1)
    return M
def Eij(i, j, n=7):
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
    n = sum(len(M) for M in Ms); m = sum(len(M[0]) for M in Ms); out = zeros(n, m); o = p = 0
    for M in Ms:
        for i in range(len(M)):
            for j in range(len(M[0])): out[o + i][p + j] = M[i][j]
        o += len(M); p += len(M[0])
    return out
def cols(idx, n=7):
    M = zeros(n, len(idx))
    for k, i in enumerate(idx): M[i - 1][k] = Fr(1)
    return M
def blocks(rows):
    """assemble a block matrix from a list of lists of matrices"""
    return vstack(*[hstack(*r) for r in rows])

I7, O7 = eye(7), zeros(7, 7)
X = add(Eij(4, 1), Eij(5, 2), Eij(6, 3))
Y = add(Eij(7, 1), sc(-1, Eij(6, 7)))
Z = add(Eij(2, 1), Eij(3, 2), Eij(5, 4), Eij(6, 5))
U = add(I7, X)
EY, EZ = cols([7, 6]), cols([2, 3, 5, 6])          # isometries R^2 -> V_Y, R^4 -> V_Z
UZ = mul(tr(EZ), mul(U, EZ))
# the isometries sigma_Y, sigma_Z of the proof of Lemma 6.1(iii): Y sigY = EY, Z sigZ = EZ   (Y e1 = e7, Y e7 = -e6;  Z e1 = e2, Z e2 = e3, Z e4 = e5, Z e5 = e6)
sigY = zeros(7, 2); sigY[0][0] = Fr(1); sigY[6][1] = Fr(-1)
sigZ = zeros(7, 4); sigZ[0][0] = Fr(1); sigZ[1][1] = Fr(1); sigZ[3][2] = Fr(1); sigZ[4][3] = Fr(1)


def cpow(c, s, m):
    """(cos(m phi), sin(m phi)) from (cos phi, sin phi), exactly"""
    zr, zi = Fr(1), Fr(0)
    for _ in range(m): zr, zi = zr * c - zi * s, zr * s + zi * c
    return zr, zi


def build(c, s, eps):
    """all maps of the construction for (cos(pi theta), sin(pi theta)) = (c, s)"""
    cI, sI = sc(c, I7), sc(s, I7)
    rot = blocks([[cI, sc(-1, sI)], [sI, cI]])
    S = blockdiag(rot, sc(Fr(1, 2), eye(2)), sc(Fr(1, 8), eye(4)))
    T = blockdiag(U, U, eye(2), UZ)
    J = vstack(I7, O7, mul(tr(EY), Y), mul(tr(EZ), Z))
    L = hstack(I7, O7, EY, EZ)
    N = blockdiag(zeros(7, 7), I7, eye(2), eye(4))
    R = add(mul(J, L), sc(eps, N))
    F0 = mul(T, S)
    F1 = mul(T, mul(J, mul(L, S)))
    F1e = mul(T, mul(R, S))
    return dict(S=S, T=T, J=J, L=L, N=N, R=R, F0=F0, F1=F1, F1e=F1e)


def Xi_map():
    """Xi : V^4 -> W,  (a, b, gamma, eta) -> (a, b, Y(a+gamma), Z(a+eta))   (20 x 28), Section 6.1"""
    Yb, Zb = mul(tr(EY), Y), mul(tr(EZ), Z)
    return blocks([[I7, O7, O7, O7],
                   [O7, I7, O7, O7],
                   [Yb, zeros(2, 7), Yb, zeros(2, 7)],
                   [Zb, zeros(4, 7), zeros(4, 7), Zb]])


def Omega_map(Sk, L, eps):
    """Omega_k : W -> V^4 with R S^k = Xi Omega_k   (28 x 20; Lemma 6.1(iii)); Sk = S^k"""
    P2 = hstack(O7, I7, zeros(7, 2), zeros(7, 4))
    P3 = hstack(zeros(2, 7), zeros(2, 7), eye(2), zeros(2, 4))
    P4 = hstack(zeros(4, 7), zeros(4, 7), zeros(4, 2), eye(4))
    return vstack(mul(L, Sk), sc(eps, mul(P2, Sk)), sc(eps, mul(sigY, mul(P3, Sk))), sc(eps, mul(sigZ, mul(P4, Sk))))


def Tmat(m, c, s, eps):
    """the transfer matrix T_m of (6.3) on V^4 (28 x 28), entries in the algebra A"""
    q, sm = cpow(c, s, m)
    y, z = Fr(1, 2 ** m), Fr(1, 8 ** m)
    return blocks([[add(sc(q, I7), sc(y, Y), sc(z, Z)), sc(-sm, I7), sc(y, Y), sc(z, Z)],
                   [sc(eps * sm, I7), sc(eps * q, I7), O7, O7],
                   [sc(eps * y, I7), O7, sc(eps * y, I7), O7],
                   [sc(eps * z, I7), O7, O7, sc(eps * z, I7)]])


def rhoW(a):
    """action of a in A on W (componentwise; on V_Y, V_Z in the coordinates EY, EZ)"""
    return blockdiag(a, a, mul(tr(EY), mul(a, EY)), mul(tr(EZ), mul(a, EZ)))


# ---------------------------------------------------------------- floating point versions
def fl(M): return np.array([[float(x) for x in row] for row in M])

Xn, Yn, Zn, Un = fl(X), fl(Y), fl(Z), fl(U)
EYn, EZn, UZn = fl(EY), fl(EZ), fl(UZ)


def bd(*Ms):
    n = sum(M.shape[0] for M in Ms); m = sum(M.shape[1] for M in Ms)
    out = np.zeros((n, m)); o = p = 0
    for M in Ms:
        out[o:o + M.shape[0], p:p + M.shape[1]] = M; o += M.shape[0]; p += M.shape[1]
    return out


def pair_float(theta, eps):
    c, s = math.cos(math.pi * theta), math.sin(math.pi * theta)
    I, O = np.eye(7), np.zeros((7, 7))
    S = bd(np.block([[c * I, -s * I], [s * I, c * I]]), np.eye(2) / 2, np.eye(4) / 8)
    T = bd(Un, Un, np.eye(2), UZn)
    J = np.vstack([I, O, EYn.T @ Yn, EZn.T @ Zn]); L = np.hstack([I, O, EYn, EZn])
    N = bd(np.zeros((7, 7)), I, np.eye(2), np.eye(4))
    F0 = T @ S
    F1 = T @ J @ L @ S
    F1e = T @ (J @ L + eps * N) @ S
    return F0, F1, F1e


def gbrute(F0, F1, nmax):
    """g(n) for n = 1..nmax by enumerating all products (depth-first)"""
    g = [0.0] * (nmax + 1)
    stack = [(np.eye(F0.shape[0]), 0)]
    while stack:
        P, d = stack.pop()
        if d == nmax: continue
        for F in (F0, F1):
            Q = F @ P
            nr = np.linalg.norm(Q, 2)
            if nr > g[d + 1]: g[d + 1] = nr
            stack.append((Q, d + 1))
    return g


def tau_list(theta, M):
    """tau_m for m = 1..M (floats; inf allowed)"""
    out = [None]
    for m in range(1, M + 1):
        q = abs(math.cos(math.pi * m * theta))
        out.append(math.inf if q >= 1.0 else 1.0 / (1.0 - q))
    return out


def Phi_theta(theta, n, taus=None):
    """Phi_theta(n) of Definition 4.1, computed directly"""
    if taus is None: taus = tau_list(theta, max(n, 2))
    nu = [0.0] + [min(n / m, taus[m]) for m in range(1, n)]
    ph1 = n * max([nu[m] / 8.0 ** m for m in range(1, n)], default=0.0)
    ph2 = 0.0
    for m in range(1, n):
        for mm in range(m, n):
            ps = abs(n / 8.0 ** (m + mm) - 1 / 2.0 ** (m + mm))
            v = nu[m] * nu[mm] * ps
            if v > ph2: ph2 = v
    return n + ph1 + ph2


# ======================================================================================
# Transfer matrices in floating point (Sections 6.1 and 6.2)
# ======================================================================================
I7f = np.eye(7)

def Tm_float(theta, m, eps):
    """T_m as a real 28 x 28 matrix (floating point)"""
    q, s = math.cos(math.pi * m * theta), math.sin(math.pi * m * theta)
    y, z = 2.0 ** -m, 8.0 ** -m
    O = np.zeros((7, 7))
    return np.block([[q * I7f + y * Yn + z * Zn, -s * I7f, y * Yn, z * Zn],
                     [eps * s * I7f, eps * q * I7f, O, O],
                     [eps * y * I7f, O, eps * y * I7f, O],
                     [eps * z * I7f, O, O, eps * z * I7f]])

def top4(theta, m, eps):
    """the real 4 x 4 matrix of the coefficients of I in T_m (the top level, Section 6.2)"""
    q, s = math.cos(math.pi * m * theta), math.sin(math.pi * m * theta)
    y, z = 2.0 ** -m, 8.0 ** -m
    return np.array([[q, -s, 0, 0], [eps * s, eps * q, 0, 0], [eps * y, 0, eps * y, 0], [eps * z, 0, 0, eps * z]])

def product(theta, n, gaps, eps):
    """a_n^eps(mu) = U^n T_{m_h} ... T_{m_1} of Section 6.1 (gaps = (m_1, ..., m_h), m_1 applied first)"""
    P = np.eye(28)
    for m in gaps: P = Tm_float(theta, m, eps) @ P
    U4 = np.kron(np.eye(4), I7f + n * Xn)
    return U4 @ P


# ======================================================================================
# The checks
# ======================================================================================
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 12
rnd = random.Random(20261114)
T0 = time.time()
NCHECK = 0
EPS = 1 / 256


def check(cond, *msg):
    global NCHECK
    NCHECK += 1
    if not cond:
        raise AssertionError(' '.join(str(m) for m in msg))


def done(text):
    print("  %-88s OK  (%.0f s)" % (text, time.time() - T0))


# ======================================================================================
print("== Part 1: the invertible pair, exact ==")
for (c, s) in ((Fr(3, 5), Fr(4, 5)), (Fr(5, 13), Fr(12, 13)), (Fr(-7, 25), Fr(24, 25)), (Fr(1), Fr(0)), (Fr(0), Fr(1))):
    for eps in (Fr(1, 256), Fr(1, 64), Fr(1, 4)):
        D = build(c, s, eps)
        S, T, J, L, N, R, F0, F1, F1e = (D[k] for k in ('S', 'T', 'J', 'L', 'N', 'R', 'F0', 'F1', 'F1e'))
        check(F1e == add(F1, sc(eps, mul(N, F0))))                       # (6.2): F1eps = F1 + eps N F0
        for a in (X, Y, Z):
            ra = rhoW(a)
            for F in (S, T, R, N, F0, F1e):
                check(mul(F, ra) == mul(ra, F))                          # A-linearity
        check(sympy.Matrix(F1e).det() == eps ** 13 * Fr(1, 2 ** 14))    # Lemma 6.1(i)
        check(sympy.Matrix(R).det() == eps ** 13)
        Xi = Xi_map(); U4 = blockdiag(U, U, U, U)
        check(mul(T, Xi) == mul(Xi, U4))
        Sk = eye(20)
        for k in range(0, 6):
            check(mul(Xi, Omega_map(Sk, L, eps)) == mul(R, Sk)); Sk = mul(S, Sk)
        Sm = S
        for m in range(1, 7):
            check(mul(R, mul(Sm, Xi)) == mul(Xi, Tmat(m, c, s, eps))); Sm = mul(S, Sm)
        for _ in range(5):                                               # Proposition 6.2
            n = rnd.randint(1, 10)
            letters = [rnd.randint(0, 1) for _ in range(n)]
            if 1 not in letters: letters[rnd.randrange(n)] = 1
            P = eye(20)
            for i in letters: P = mul(F1e if i else F0, P)
            pos = [k + 1 for k, i in enumerate(letters) if i]
            gaps = [pos[i] - pos[i - 1] for i in range(1, len(pos))]
            core = mpow(U4, n)
            for m in reversed(gaps): core = mul(core, Tmat(m, c, s, eps))
            check(P == mul(mpow(S, n - pos[-1]), mul(Xi, mul(core, Omega_map(mpow(S, pos[0]), L, eps)))))
        # norms of Xi and Omega_k (floating point; Lemma 6.1(iii))
        check(np.linalg.norm(np.array(Xi, dtype=float), 2) <= math.sqrt(5) + 1e-12)
        check(np.linalg.norm(np.array(Omega_map(eye(20), L, eps), dtype=float), 2) <= 2)
done("identities of Lemma 6.1 and Proposition 6.2, det F1eps = eps^13 2^-14")

# ======================================================================================
print("\n== Part 2: all words of length n <= %d (Proposition 6.9, Remark 6.12(a)) ==" % NMAX)
thetas = [0.0, 1.0, 0.5, 1 / 3, 0.25, 0.1, 0.2, 2 ** 0.5 - 1, (5 ** 0.5 - 1) / 2, 1 / 10 + 2 ** -20, 0.123456, 0.7071]
lo, hi, lo0, hi0 = 1e9, 0, 1e9, 0
for th in thetas:
    for eps in (EPS, 1 / 16):
        F0, F1, F1e = pair_float(th, eps)
        g = gbrute(F0, F1e, NMAX); g0 = gbrute(F0, F1, NMAX)
        check(min(abs(np.linalg.det(F1e)), 1) > 0)
        taus = tau_list(th, NMAX + 2)
        for n in range(1, NMAX + 1):
            r = g[n] / Phi_theta(th, n, taus); lo, hi = min(lo, r), max(hi, r)
            r0 = g[n] / g0[n]; lo0, hi0 = min(lo0, r0), max(hi0, r0)
            check(r <= 5000)                                             # Proposition 6.9
print("  g_eps(n)/Phi(n) in [%.3f, %.3f];  g_eps(n)/g_0(n) in [%.3f, %.3f]  (12 angles, eps = 2^-8, 2^-4)" % (lo, hi, lo0, hi0))
done("Proposition 6.9 and Remark 6.12(a) for n <= %d (brute force)" % NMAX)

# ======================================================================================
print("\n== Part 3: the top level (Lemmas 6.4-6.6) ==")
def Mm(th, m, eps=EPS):
    q, s = math.cos(math.pi * m * th), math.sin(math.pi * m * th)
    return np.array([[q, -s], [eps * s, eps * q]])
def starnorm(A, eps=EPS):
    return np.linalg.norm(np.diag([1, eps ** -0.5]) @ A @ np.diag([1, eps ** 0.5]), 2)
kap = (1 - EPS) / (2 * (2 + EPS))
for _ in range(20000):                                                   # Lemma 6.4
    th = rnd.random(); m = rnd.randint(1, 60); q = math.cos(math.pi * m * th)
    rho = starnorm(Mm(th, m))
    check(rho >= math.sqrt(EPS) - 1e-12 and (1 - rho) >= kap * (1 - abs(q)) - 1e-12)
w5 = 0
for _ in range(5000):                                                    # Lemma 6.5
    th = rnd.random(); seq = [rnd.randint(1, 14) for _ in range(rnd.randint(1, 30))]
    P = np.eye(4)
    for m in seq: P = top4(th, m, EPS) @ P
    rh = [starnorm(Mm(th, m)) for m in seq]
    # Lemma 6.5(i): the block structure and the formulas for the entries in rows 3 and 4
    G = np.eye(2); Gs = [G]                                              # Gs[j] = G_{[1, j]}
    for m in seq: G = Mm(th, m) @ G; Gs.append(G)
    check(np.allclose(P[:2, :2], G, rtol=1e-12, atol=1e-14))
    check(P[0, 2] == 0 and P[0, 3] == 0 and P[1, 2] == 0 and P[1, 3] == 0 and P[2, 3] == 0 and P[3, 2] == 0)
    for (row, w) in ((2, [2.0 ** -m for m in seq]), (3, [8.0 ** -m for m in seq])):
        pr = np.prod([EPS * x for x in w])
        check(abs(P[row, row] - pr) <= 1e-12 * pr + 1e-290)
        for c_ in (0, 1):
            terms = [np.prod([EPS * x for x in w[j + 1:]]) * EPS * w[j] * Gs[j][0, c_] for j in range(len(seq))]
            check(abs(P[row, c_] - sum(terms)) <= 1e-12 * sum(abs(x) for x in terms) + 1e-290)
    # Lemma 6.5(ii)
    check(np.max(np.abs(P)) <= np.prod(rh[1:]) + 1e-12)
    check(np.max(np.abs(P[:, 0])) <= np.prod(rh) + 1e-12)
    # Lemma 6.5(iii), columns 1 and 2 (for column 2 the sum starts at the second gap)
    for (row, w) in ((2, [2.0 ** -m for m in seq]), (3, [8.0 ** -m for m in seq])):
        b = len(seq) - 1
        ch1 = sum(2.0 ** -(b - j) * EPS * w[j] * np.prod([rh[l] for l in range(len(seq)) if l != j]) for j in range(len(seq)))
        ch2 = sum(2.0 ** -(b - j) * EPS * w[j] * np.prod([rh[l] for l in range(len(seq)) if l not in (0, j)]) for j in range(1, len(seq)))
        check(abs(P[row, 0]) <= ch1 + 1e-15 and abs(P[row, 1]) <= ch2 + 1e-15)
wa = wb = 0
for _ in range(5000):                                                    # Lemma 6.6
    th = rnd.random(); good = [m for m in range(1, 40) if abs(math.cos(math.pi * m * th)) >= 0.5]
    seq = []; sig = 0
    for _ in range(rnd.randint(1, 80)):
        m = rnd.choice(good); s2 = math.sin(math.pi * m * th) ** 2
        if sig + s2 > 4: break
        seq.append(m); sig += s2
    if not seq: continue
    P = np.eye(4); Q = 1.0
    for m in seq: P = top4(th, m, EPS) @ P; Q *= math.cos(math.pi * m * th)
    d = abs(P[0, 0] / Q - 1); check(d <= math.exp(4 * EPS * sig / (1 - EPS)) - 1 + 1e-13)
    wa = max(wa, d / (math.exp(4 * EPS * sig / (1 - EPS)) - 1 + 1e-300))
    check(abs(P[2, 0]) <= 2.3 * EPS * 2.0 ** -seq[-1] * abs(P[0, 0]) and abs(P[3, 0]) <= 2.3 * EPS * 8.0 ** -seq[-1] * abs(P[0, 0]))
    wb = max(wb, abs(P[2, 0]) / (2.3 * EPS * 2.0 ** -seq[-1] * abs(P[0, 0])))
print("  Lemma 6.6: max |M11/prod q - 1|/bound = %.3f, max memory ratio = %.3f" % (wa, wb))
done("Lemmas 6.4, 6.5, 6.6")

# ======================================================================================
print("\n== Part 4: normal form (Lemma 6.7) and the critical coordinate (proof of Proposition 6.9) ==")
def nu_list(n, taus, kap_=1.0, M=150):
    return [0] + [min(n / m, taus[m] / kap_) for m in range(1, min(n, M))]
def AB(n, taus, kap_):
    """the numbers A'_n, A^(2)_n, B'_n, B^(2)_n of Section 6 (with nu'_m(n) = min(n/m, tau_m / kappa_eps))"""
    nu = nu_list(n, taus, kap_)
    A1 = max(nu[m] / 2.0 ** m for m in range(1, len(nu)))
    A2 = max(nu[m] / 4.0 ** m for m in range(1, len(nu)))
    B1 = max(nu[m] / 8.0 ** m for m in range(1, len(nu)))
    B2 = max(nu[m] / 64.0 ** m for m in range(1, len(nu)))
    return A1, A2, B1, B2
def expansion(th, n, gaps, r, c):
    """coordinates (P, y1, z1, y2, z2) of entry (r,c) from the formulas of Lemma 6.7, and Sigma_main"""
    h = len(gaps); T = [top4(th, m, EPS) for m in gaps]
    y = [2.0 ** -m for m in gaps]; z = [8.0 ** -m for m in gaps]
    def prodseg(a, b):          # gaps a..b (0-based, inclusive)
        P = np.eye(4)
        for l in range(a, b + 1): P = T[l] @ P
        return P
    Y_ = lambda v: v[0] + v[2]; Z_ = lambda v: v[0] + v[3]
    Pfull = prodseg(0, h - 1)
    y1 = z1 = y2 = z2 = main = 0.0
    for i in range(h):
        Pg, Pl = prodseg(i + 1, h - 1), prodseg(0, i - 1)
        y1 += y[i] * Pg[r, 0] * Y_(Pl[:, c]); z1 += z[i] * Pg[r, 0] * Z_(Pl[:, c])
        for k in range(i + 1, h):
            Pk, Pm = prodseg(k + 1, h - 1), prodseg(i + 1, k - 1)
            y2 += y[k] * y[i] * Pk[r, 0] * Y_(Pm[:, 0]) * Y_(Pl[:, c])
            z2 += z[k] * z[i] * Pk[r, 0] * Z_(Pm[:, 0]) * Z_(Pl[:, c])
            main += Pk[r, 0] * (n * z[k] * z[i] - y[k] * y[i]) * Pm[0, 0] * Pl[0, c]
    return Pfull[r, c], y1, z1, y2, z2, main
worst_mem = worst_34 = 0
E2, E3 = math.e ** 2, math.e ** 3
tests = []
for _ in range(60):
    th = rnd.random(); h = rnd.randint(1, 18)
    tests.append((th, [rnd.randint(1, 7) for _ in range(h)]))
for _ in range(30):                                   # longer gaps and near-resonant angles
    m0 = rnd.randint(2, 12); th = rnd.randint(0, 2 * m0) / m0 + rnd.choice([1e-3, 1e-5, 1e-8]) / m0
    tests.append((th, [rnd.choice([m0, m0, m0, rnd.randint(1, 12)]) for _ in range(rnd.randint(2, 16))]))
for (th, gaps) in tests:
    n = sum(gaps) + rnd.choice([1, 7, 300, 3000, 10 ** 5])
    E = product(th, n, gaps, EPS)
    taus = tau_list(th, 160)
    A1, A2, B1, B2 = AB(n, taus, kap)
    for r in range(4):
        for c in range(4):
            P, y1, z1, y2, z2, main = expansion(th, n, gaps, r, c)
            blk = E[7 * r:7 * r + 7, 7 * c:7 * c + 7][:, 0]          # (P, z1, z2, nP, nz1, nz2-y2, y1) in the basis (2.4)
            tol = 1e-9 * (1 + np.max(np.abs(blk)))
            check(abs(blk[0] - P) < tol and abs(blk[1] - z1) < tol and abs(blk[2] - z2) < tol)
            check(abs(blk[3] - n * P) < tol and abs(blk[4] - n * z1) < tol and abs(blk[6] - y1) < tol)
            check(abs(blk[5] - (n * z2 - y2)) < tol)
            if c <= 1:                                   # columns 1, 2: memory terms
                mem = abs(blk[5] - main); bound = 32 * E3 * EPS * (A1 * A2 + n * B1 * B2)
                check(mem <= bound + tol); worst_mem = max(worst_mem, mem / bound)
            else:                                        # columns 3, 4: direct bound
                bound = (E2 * A1 + 8 * E2 * EPS * A1 * A2) if c == 2 else (E2 / 4 * n * B1 + 8 * E2 * EPS * n * B1 * B2)
                check(abs(blk[5]) <= bound + tol); worst_34 = max(worst_34, abs(blk[5]) / bound)
print("  columns 1,2: max |memory terms| / (32 e^3 eps (A'_n A2_n + n B'_n B2_n)) = %.2e" % worst_mem)
print("  columns 3,4: max |critical coordinate| / (direct bound) = %.2e" % worst_34)
done("Lemma 6.7 and the bounds for the critical coordinate in Proposition 6.9")

# ======================================================================================
print("\n== Part 5: the upper bound (Proposition 6.9) ==")
def Phi_parts(th, n, taus, kap_=1.0, M=60):
    M = min(M, n - 1)
    nu = [0] + [min(n / m, taus[m] / kap_) for m in range(1, M + 1)]
    ph1 = n * max(nu[m] / 8.0 ** m for m in range(1, M + 1)) if M >= 1 else 0.0
    ph2 = 0.0
    for m in range(1, M + 1):
        for mm in range(m, M + 1):
            ph2 = max(ph2, nu[m] * nu[mm] * abs(n / 8.0 ** (m + mm) - 1 / 2.0 ** (m + mm)))
    return ph1, ph2
hi = hi_entry = 0
angles = [rnd.random() for _ in range(12)] + [0.1 + 2 ** -30, 0.25 + 2 ** -25, 1 / 3 + 1e-6, 0.0, 0.5]
for th in angles:
    taus = tau_list(th, 70)
    for n in (50, 300, 2000, 20000):
        ph1, ph2 = Phi_parts(th, n, taus); Ph = n + ph1 + ph2
        ph1p, ph2p = Phi_parts(th, n, taus, kap)
        words = []
        for _ in range(8):
            gaps, tot = [], 0
            while True:
                m = rnd.choice([1, 2, 3, 4, 5, 6, 8, 10])
                if tot + m > n - 1 or len(gaps) > 300: break
                gaps.append(m); tot += m
            words.append(gaps)
        for m in range(1, 11):
            t = min((n - 1) // m, 1 + int(min(taus[m], 1e9) / 2), 300)
            if t >= 1: words.append([m] * t)
        for gaps in words:
            E = product(th, n, gaps, EPS)
            check(2 * math.sqrt(5) * np.linalg.norm(E, 2) <= 5000 * Ph)
            hi = max(hi, np.linalg.norm(E, 2) / Ph)
            for r in range(4):
                for c in range(4):
                    s_ = np.sum(np.abs(E[7 * r:7 * r + 7, 7 * c:7 * c + 7][:, 0]))
                    bnd = 15 * n + 27.2 * ph1p + 15.5 * ph2p
                    check(s_ <= bnd); hi_entry = max(hi_entry, s_ / bnd)
print("  max ||E||/Phi = %.4f;  max (sum of coordinates of an entry)/(15 n + 27.2 Phi'1 + 15.5 Phi'2) = %.4f" % (hi, hi_entry))
done("Proposition 6.9 on random and structured words")

# ======================================================================================
print("\n== Part 6: Lemma 6.11 on explicit words, and the numbers in the proof of Theorem 1.4 ==")
def coords_blocks(th, n, blocks):
    P = np.eye(28)
    for (m, t) in blocks: P = np.linalg.matrix_power(Tm_float(th, m, EPS), t) @ P
    return ((I7n + n * Xn) @ P[0:7, 0:7])[:, 0]
I7n = np.eye(7)
def tj(n, m, j, tau):
    a = (n - 1) // (j * m)
    return a if math.isinf(tau) else min(a, 1 + int(tau // 2))
worst = 1e300; cnt = 0
angles = [rnd.random() for _ in range(25)] + [0.1 + 2 ** -40, 0.25 + 2 ** -30, 1 / 3 + 2 ** -35, 0.5, 0.0, 0.2, 1.0]
for th in angles:
    taus = tau_list(th, 70)
    for n in [3, 10, 40, 150, 700, 3000, 20000, 200000, 3 * 10 ** 6]:
        for m in range(1, min(n, 16)):
            t = tj(n, m, 1, taus[m])
            if t >= 2:
                x = n / 16.0 ** m
                if abs(x - 1) >= 12.4 * EPS * 2.0 ** -m * (x / 4.0 ** m + 1):          # Lemma 6.11
                    cc = coords_blocks(th, n, [(m, t)])
                    bound = t * t * abs(n / 64.0 ** m - 1 / 4.0 ** m) / 17
                    check(abs(cc[5]) >= bound); cnt += 1
                    if bound > 0: worst = min(worst, abs(cc[5]) / bound)
print("  %d explicit words: min |n z2 - y2| / (t^2 psi_n(2m) / 17) = %.3f  (Lemma 6.11: >= 1)" % (cnt, worst))
# the numbers in the proof of Theorem 1.4
check(64 * 34 == 2176 and 16 * 17 == 272 and 5000 * 3 == 15000)
check(2176 * 15000 == 3.264e7 and 272 * 15000 == 4.08e6 and 4.08e6 <= 3.264e7 and 3.264e7 * math.pi ** 2 / 2 <= 2e8)
check(0.95 - 5.6 / 12.4 >= 0.49 and 0.49 / 8 >= 0.06 and 0.06 >= 1 / 17)                          # proof of Lemma 6.11
check(math.exp(4 * EPS / (1 - EPS)) - 1 <= 0.0159 and 1.0159 ** 3 - 1 <= 0.05 and 1.05 * 2.31 <= 2.8)  # Lemma 6.10
for p in (256, 4 ** 4):
    c_ = 12.4 * EPS * 2.0 ** -p
    check(c_ < 0.1 and c_ * (0.5 * 4.0 ** -p + 1) < 0.1 and all(c_ * (l * 4.0 ** -p + 1) <= l - 1 for l in (2, 3, 10, 10 ** 6)))
done("Lemma 6.11 on explicit words, and the constants in the proof of Theorem 1.4")

# ======================================================================================
print("\n== Part 7: the numbers of Remark 6.12(a): n near 16^10, theta = 1/10 + 2^-80 (multiprecision) ==")
mp.mp.dps = 80
def mpm(M): return mp.matrix([[mp.mpf(x.numerator) / x.denominator for x in row] for row in M])
Xm, Ym, Zm, I7m = mpm(X), mpm(Y), mpm(Z), mp.eye(7)
def Tm_mp(th, m, eps):
    q, s = mp.cos(mp.pi * m * th), mp.sin(mp.pi * m * th); y, z = mp.mpf(2) ** -m, mp.mpf(8) ** -m
    R = mp.matrix(28, 28)
    B = [[q * I7m + y * Ym + z * Zm, -s * I7m, y * Ym, z * Zm], [eps * s * I7m, eps * q * I7m, None, None],
         [eps * y * I7m, None, eps * y * I7m, None], [eps * z * I7m, None, None, eps * z * I7m]]
    for bi in range(4):
        for bj in range(4):
            if B[bi][bj] is None: continue
            for i in range(7):
                for j in range(7): R[7 * bi + i, 7 * bj + j] = B[bi][bj][i, j]
    return R
def mpow_mp(A, t):
    R = mp.eye(A.rows); Bm = A
    while t:
        if t & 1: R = Bm * R
        Bm = Bm * Bm; t >>= 1
    return R
th = mp.mpf(1) / 10 + mp.mpf(2) ** -80; p = 10; N = 16 ** p
vals = {}
for eps in (mp.mpf(0), mp.mpf(1) / 256):
    T = Tm_mp(th, p, eps)
    for n in (N // 2, N, 2 * N):
        P = mpow_mp(T, (n - 1) // p)
        col = [P[i, 0] + (n * P[i - 3, 0] if 3 <= i <= 5 else 0) for i in range(7)]   # (U^n P)_{11} e_1
        vals[(float(eps), n)] = (col[5], mp.sqrt(sum(abs(v) ** 2 for v in col)))
for eps in (0.0, 1 / 256):
    print("  eps = %-9s coordinate n z2 - y2 at N/2, N, 2N: %s, %s, %s" % (eps, mp.nstr(vals[(eps, N // 2)][0], 5),
          mp.nstr(vals[(eps, N)][0], 5), mp.nstr(vals[(eps, 2 * N)][0], 5)))
check(vals[(0.0, N)][0] == 0)
check(abs(vals[(1 / 256, N)][0]) < 1e-3 * abs(vals[(1 / 256, N // 2)][0]))
check(abs(vals[(1 / 256, 2 * N)][0]) > 30 * abs(vals[(1 / 256, N // 2)][0]) / 1.1)
done("uniform words around the dip: the cancellation survives for eps = 1/256")

# ======================================================================================
print("\n== Part 8: Lemma 8.2 and Theorem 1.7 (illustrations) ==")
def gb(Ms, nmax):
    g = [1.0] * (nmax + 1); layer = [np.eye(Ms[0].shape[0])]
    for n in range(1, nmax + 1):
        layer = [A @ P for P in layer for A in Ms]
        g[n] = max(np.linalg.norm(P, 2) for P in layer)
    return g
# Lemma 8.2: a 2x2 upper triangular family with bi-unimodular letters generating a finite semigroup
# (no unipotent element) has bounded products; with a unipotent element, linear growth.
for trial in range(30):
    k = 3
    letters = []
    for _ in range(k):
        a = rnd.choice([1, -1, 0.5, -0.5]); b = rnd.choice([1, -1, 0.5]); x = rnd.choice([0, 1, -1, 0.5])
        letters.append(np.array([[a, x], [0, b]]))
    # semigroup of bi-unimodular letters: does it contain [[1, x], [0, 1]] with x != 0 ?
    bi = [L_ for L_ in letters if abs(L_[0, 0]) == 1 and abs(L_[1, 1]) == 1]
    elems = {}
    frontier = [np.eye(2)]
    for _ in range(6):
        new = []
        for P in frontier:
            for L_ in bi:
                Q = L_ @ P; key = tuple(np.round(Q.flatten(), 9))
                if key not in elems: elems[key] = Q; new.append(Q)
        frontier = new
    unip = any(abs(Q[0, 0] - 1) < 1e-9 and abs(Q[1, 1] - 1) < 1e-9 and abs(Q[0, 1]) > 1e-9 for Q in elems.values())
    g = gb(letters, 11)
    if unip: check(g[11] >= 3)                       # linear growth visible
    else: check(g[11] <= 12)                         # bounded (crude constant)
done("Lemma 8.2 (illustration on random 2 x 2 upper triangular families)")
# Theorem 1.7 illustration: random 3x3 upper triangular families with JSR 1; WI along n <= 11
worst = 1e9
for trial in range(25):
    Ms = []
    for _ in range(2):
        d = [rnd.choice([1, -1, 0.5, 1]) for _ in range(3)]
        Ms.append(np.array([[d[0], rnd.uniform(-1, 1), rnd.uniform(-1, 1)], [0, d[1], rnd.uniform(-1, 1)], [0, 0, d[2]]]))
    g = gb(Ms, 11)
    worst = min(worst, min(g[m] / max(g[1:m + 1]) for m in range(1, 12)))
print("  random 3x3 upper triangular families: min_m g(m)/max_{j<=m} g(j) = %.3f (illustration only)" % worst)
done("Theorem 1.7 (illustration)")

# ======================================================================================
print("\n== Part 9: Proposition 8.4 (binary encoding into a pair) ==")
def encode(Ms):
    k = len(Ms); Lc = max(1, math.ceil(math.log2(k))); d = Ms[0].shape[0]
    states = [(p, bits) for p in range(Lc) for bits in range(2 ** p)]
    idx = {s: i for i, s in enumerate(states)}
    S = len(states); B = []
    for bit in (0, 1):
        Bm = np.zeros((S * d, S * d))
        for (p, bits) in states:
            nb = bits * 2 + bit
            if p + 1 < Lc: tgt, A = (p + 1, nb), np.eye(d)
            else: tgt, A = (0, 0), (Ms[nb] if nb < k else np.zeros((d, d)))
            i, j = idx[tgt], idx[(p, bits)]
            Bm[i * d:(i + 1) * d, j * d:(j + 1) * d] = A
        B.append(Bm)
    return B, Lc, S
for trial in range(6):
    Ms = [np.array([[rnd.choice([1, -1, 0.5]), rnd.uniform(-1, 1)], [0, rnd.choice([1, -1])]]) for _ in range(3)]
    B, Lc, S = encode(Ms)
    gB = gb(B, 12); gM = gb(Ms, 7)
    for n in range(1, 13):
        j = n // Lc
        lowM = gM[j] if j >= 1 else 1.0
        upM = max(gM[j], gM[min(j + 1, 7)]) if j >= 1 else max(1.0, gM[1])
        check(gB[n] >= lowM - 1e-9 and gB[n] <= math.sqrt(S) * upM + 1e-9)
done("g_B(n) between g_M(floor(n/L)) and sqrt(#states) * g_M(floor(n/L)+1)")

print("\n%d checks in %.0f s.  ALL CHECKS PASSED" % (NCHECK, time.time() - T0))
