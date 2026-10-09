# High-precision end-to-end check at m=32, h=2: solve the two jet equations, then verify that
# (w^2-1)^2 divides det(wI - T_65(a)) and that eigenvalues +-1 appear, each at least twice.
import mpmath as mp
mp.mp.dps = 60
def binom_half(k): return mp.binomial(mp.mpf(1)/2, k)
def gco(P,K):
    g={-k:binom_half(k) for k in range(K)}
    for p,c in P.items(): g[p]=g.get(p,0)+c
    return g
def toep(co,L): return mp.matrix([[co.get(j-k,0) for k in range(L)] for j in range(L)])
m=32; L=m+1; n=2*m+1; h=2; q=12
tau=mp.mpf('1e-3'); P={1:tau,2:tau}
g=gco(P,4*m+10)
U=mp.zeros(L)
for j in range(L-1): U[j,j+1]=1
def jets(v):
    g2=dict(g)
    for d in range(q): g2[-(m-d)]=g.get(-(m-d),0)+v[d]
    G=toep(g2,L); H=G*G-U; W=mp.inverse(H)
    r=W[0,:]; out=[]
    for k in range(h):
        out.append(r[m]); r=(r*U)*W
    return out
v=[mp.mpf(0)]*q
for it in range(8):
    F=jets(v)
    res=max(abs(f) for f in F)
    print(f"it {it}: residual {mp.nstr(res,5)}")
    if res<mp.mpf('1e-55'): break
    # finite-difference Jacobian (h x q), minimal-norm step
    eps=mp.mpf('1e-30'); J=mp.zeros(h,q)
    for d in range(q):
        v2=list(v); v2[d]+=eps
        F2=jets(v2)
        for k in range(h): J[k,d]=(F2[k]-F[k])/eps
    # min-norm: dv = J^T (J J^T)^{-1} (-F)
    JJt=J*J.T; rhs=mp.matrix([-f for f in F])
    lam=mp.lu_solve(JJt, rhs); dv=J.T*lam
    v=[v[d]+dv[d] for d in range(q)]
print("solution v:", [mp.nstr(x,6) for x in v])
# full Toeplitz matrix and characteristic polynomial
g2=dict(g)
for d in range(q): g2[-(m-d)]=g.get(-(m-d),0)+v[d]
a={1+2*l:c for l,c in g2.items()}
T=toep(a,n)
# characteristic polynomial via Faddeev-LeVerrier would be slow; use eigenvalues + check det at sample points.
E=mp.eig(T, left=False, right=False)
near1=sorted([e for e in E if abs(e-1)<mp.mpf('1e-6')], key=lambda z: abs(z-1))
nearm1=sorted([e for e in E if abs(e+1)<mp.mpf('1e-6')], key=lambda z: abs(z+1))
print("eigenvalues within 1e-6 of +1:", [mp.nstr(e,12) for e in near1])
print("eigenvalues within 1e-6 of -1:", [mp.nstr(e,12) for e in nearm1])
# divisibility check: p(w)=det(wI-T); evaluate p(1+d)/d^2 for small d -> finite limit iff (w-1)^2 | p
for d in [mp.mpf('1e-5'), mp.mpf('1e-10'), mp.mpf('1e-15')]:
    val=mp.det((1+d)*mp.eye(n)-T)
    print(f"det(wI-T) at w=1+{mp.nstr(d,2)}: {mp.nstr(val,6)}; /d^2 = {mp.nstr(val/d**2,8)}; /d^3 = {mp.nstr(val/d**3,6)}")
# compare: same at the unperturbed background (no v): should NOT be divisible by (w-1)^2 ... check order
T0=toep({1+2*l:c for l,c in g.items()},n)
for d in [mp.mpf('1e-5'), mp.mpf('1e-10')]:
    val=mp.det((1+d)*mp.eye(n)-T0)
    print(f"[no correction] det at w=1+{mp.nstr(d,2)}: {mp.nstr(val,6)}; /d = {mp.nstr(val/d,8)}; /d^2 = {mp.nstr(val/d**2,6)}")
