# Independent check of Prop. 2.1 (odd-symbol pencil), its Jacobian formula, the base
# Jacobian J^0, and the partial-convolution identity used in the endpoint lemma.
import mpmath as mp, random
mp.mp.dps = 40
def binom_half(k, a=mp.mpf(1)/2):
    return mp.binomial(a, k)

def toeplitz(coef, L):
    # T_L(g) = (g_{j-k}); coef: dict index->value
    return mp.matrix([[coef.get(j-k, 0) for k in range(L)] for j in range(L)])

def symbol_g(P, K=200):
    # g = sqrt(1+1/s) + P ; P dict power->coef
    g = {-k: binom_half(k) for k in range(K)}
    for p, c in P.items():
        g[p] = g.get(p, 0) + c
    return g

def symbol_a(g):
    # a(z) = z g(z^2) -> a_{1+2l} = g_l
    return {1 + 2*l: c for l, c in g.items()}

def check(P, m, trials=3):
    L = m + 1; n = 2*m + 1
    g = symbol_g(P); a = symbol_a(g)
    G = toeplitz(g, L)
    U = mp.zeros(L)
    for j in range(L-1): U[j, j+1] = 1
    H = G*G - U
    Tn = toeplitz(a, n)
    e0 = mp.zeros(L,1); e0[0] = 1
    em = mp.zeros(L,1); em[m] = 1
    worst = 0
    for _ in range(trials):
        w = mp.mpc(random.uniform(-1.5,1.5), random.uniform(-1.5,1.5))
        t = w*w - 1
        lhs = mp.det(w*mp.eye(n) - Tn)
        Mt = (e0.T * mp.inverse(H - t*U) * em)[0]
        rhs = w * mp.det(H - t*U) * Mt
        worst = max(worst, abs(lhs - rhs)/max(1, abs(lhs)))
    return worst, G, H, U

random.seed(1)
# base symbol: H should be I, char poly w (w^2-1)^m
for m in [1, 2, 5, 8]:
    err, G, H, U = check({}, m)
    print(f"base m={m}: det identity rel err {mp.nstr(err,5)}, ||H-I||_max = {mp.nstr(max(abs(H[i,j]-(1 if i==j else 0)) for i in range(m+1) for j in range(m+1)),5)}")
# perturbed symbols with positive and negative powers
P = {1: mp.mpf('0.13'), 2: mp.mpf('-0.07'), -3: mp.mpf('0.21'), -5: mp.mpf('-0.11')}
for m in [4, 7, 10]:
    err, G, H, U = check(P, m)
    print(f"perturbed m={m}: det identity rel err {mp.nstr(err,5)}")

# Jacobian formula (odd-pencil-jacobian): d[t^k]M / d g_{-q-1} = -2 sum_l [s^{m-q-1}] R_l X_{k-l}
def jets(H, U, e0, em, kmax):
    W = mp.inverse(H)
    rows = []
    r = e0.T * W
    for k in range(kmax+1):
        rows.append(r)
        r = r * U * W
    return rows  # r_k = e0^* W (UW)^k
def M_jets(G, U, kmax):
    L = G.rows; m = L-1
    e0 = mp.zeros(L,1); e0[0]=1; em = mp.zeros(L,1); em[m]=1
    H = G*G - U
    rows = jets(H, U, e0, em, kmax)
    return [rows[k][m] for k in range(kmax+1)], rows
m = 9; L = m+1
g = symbol_g(P); G = toeplitz(g, L)
U = mp.zeros(L)
for j in range(L-1): U[j,j+1]=1
kmax = 4
Mj, rows = M_jets(G, U, kmax)
maxerr = 0
for q in range(0, m):
    # finite difference in g_{-q-1}
    eps = mp.mpf('1e-15')
    g2 = dict(g); g2[-q-1] = g2.get(-q-1,0) + eps
    Mj2,_ = M_jets(toeplitz(g2, L), U, kmax)
    for k in range(kmax+1):
        fd = (Mj2[k]-Mj[k])/eps
        # formula
        s = 0
        for l in range(k+1):
            R_l = rows[l]            # row vector, R_l(s) = sum_j (r_l)_j s^j
            X = rows[k-l]*G          # X_{k-l}(s)
            idx = m-q-1
            if 0 <= idx <= m:
                s += R_l[idx]*X[idx] if False else sum(R_l[i]*X[idx-i] for i in range(idx+1))
        formula = -2*s
        maxerr = max(maxerr, abs(fd-formula)/max(1,abs(formula)))
print("Jacobian formula max rel err (finite diff, eps=1e-15, dps=40):", mp.nstr(maxerr,5))

# Base Jacobian J^0_{kq} = -2(k+1) binom(1/2, m-q-1-k) 1_{k<=m-q-1}
g0 = symbol_g({}); G0 = toeplitz(g0, L)
Mj0, rows0 = M_jets(G0, U, kmax)
maxerr=0
for q in range(0,m):
    for k in range(kmax+1):
        s=0
        for l in range(k+1):
            idx=m-q-1
            s += sum(rows0[l][i]*(rows0[k-l]*G0)[idx-i] for i in range(idx+1))
        formula=-2*s
        J0 = -2*(k+1)*binom_half(m-q-1-k) if k <= m-q-1 else 0
        maxerr=max(maxerr, abs(formula-J0))
print("J^0 formula max abs err:", mp.nstr(maxerr,5))
print("base jets M(t) coefficients k=0..4 (expect 0 except k=m):", [mp.nstr(x,5) for x in Mj0])

# partial convolution identity
maxerr=0
for k in range(0,12):
    for j in range(1,12):
        lhs = sum(mp.binomial(mp.mpf(1)/2, d+j)*mp.binomial(-mp.mpf(1)/2, k-d) for d in range(k+1))
        rhs = (k+mp.mpf(1)/2)/(k+j)*mp.binomial(-mp.mpf(1)/2,k)*mp.binomial(-mp.mpf(1)/2,j-1)
        maxerr=max(maxerr, abs(lhs-rhs))
print("partial-convolution identity max abs err:", mp.nstr(maxerr,5))

# ||H-I|| <= 2 sqrt2 eta + eta^2 where eta = sup|g-g0|
for trial in range(3):
    Pr = {random.choice([-6,-4,-2,-1,1,2,3]): mp.mpf(random.uniform(-0.2,0.2)) for _ in range(3)}
    m=12; L=m+1
    g=symbol_g(Pr); G=toeplitz(g,L); U=mp.zeros(L)
    for j in range(L-1): U[j,j+1]=1
    H=G*G-U
    eta = max(abs(sum(c*mp.exp(1j*p*th) for p,c in Pr.items())) for th in [2*mp.pi*i/400 for i in range(400)])
    normHI = mp.norm(H-mp.eye(L), 2) if hasattr(mp,'norm') else None
    # spectral norm via svd
    sv = mp.svd_r(H-mp.eye(L), compute_uv=False)
    print(f"||H-I||_2 = {mp.nstr(max(sv),6)}  bound 2sqrt2 eta+eta^2 = {mp.nstr(2*mp.sqrt(2)*eta+eta**2,6)}")
