import numpy as np
from scipy.special import binom
from mechanism import g_coeffs, toep
from conformal import h_on_circle
tau=1e-3; P={1:tau,2:tau}
# pencil stability on the closed domain: t on Gamma=h(T) and some interior points
hv=h_on_circle(P, 64)
tpts=list(hv)+[0.0, -0.99, 0.99, 0.5+0.5j, -0.5-0.5j]
r=1.05
for m in [64,128,256,512,1024]:
    L=m+1; g=g_coeffs(P,4*m+10); U=np.eye(L,k=1); G=toep(g,L); H=G@G-U
    Dr=r**np.arange(L)
    nrm=0; wnrm=0
    for t in tpts:
        W=np.linalg.inv(H-t*U)
        nrm=max(nrm,np.linalg.norm(W,2))
        wnrm=max(wnrm,np.linalg.norm((Dr[:,None]*W)/Dr[None,:],2))
    print(f"m={m}: max_t ||W_m(t)|| = {nrm:.3e} (/(m+1)^4 = {nrm/(m+1)**4:.2e}), max_t ||D_r W D_r^-1|| (r={r}) = {wnrm:.3e}")
# Gohberg-Semencul identity as displayed in the write-up
rng=np.random.default_rng(3)
N=12
c={k: rng.normal()+1j*rng.normal() for k in range(-N+1,N)}
T=np.array([[c[j-k] for k in range(N)] for j in range(N)])
V=np.linalg.inv(T); x=V[:,0]; y=V[:,N-1]; x0=x[0]
def Lmat(v): return np.array([[v[i-j] if i>=j else 0 for j in range(N)] for i in range(N)])
def Umat(v): return np.array([[v[j-i] if j>=i else 0 for j in range(N)] for i in range(N)])
rhs=(Lmat(x)@Umat(y[::-1]) - Lmat(np.r_[0,y[:-1]])@Umat(np.r_[0,x[::-1][:-1]]))/x0
print("Gohberg-Semencul (as displayed) max err:", np.abs(V-rhs).max())
# tail identity for sqrt(1-x)=1-sum c_l x^l : sum_{l>=t} c_l = C(2t-2,t-1)/4^{t-1}
cl=[-binom(0.5,l)*(-1)**l for l in range(1,4000)]   # coefficient of x^l in sqrt(1-x) is binom(1/2,l)(-1)^l ; c_l = minus that
cl=np.array(cl)
print("c_l positive:", np.all(cl>0), " sum c_l ~", cl.sum())
for t in [1,2,3,5,10,20]:
    tail=cl[t-1:].sum()   # sum_{l>=t}
    print(f"t={t}: sum_(l>=t) c_l = {tail:.6f}, C(2t-2,t-1)/4^(t-1) = {binom(2*t-2,t-1)/4**(t-1):.6f} (truncation ~ {2*cl[-1]*np.sqrt(4000):.1e})")
