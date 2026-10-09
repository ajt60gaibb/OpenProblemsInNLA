# Nested-background test: stage 1 at m1=64 (solve, restore with K_m), add a positive packet
# at s^64(1+s), then measure forcing scaling and conformal-coordinate Jacobian conditioning
# at m = 512,1024,2048, and solve stage 2 at m=512.
import numpy as np
from scipy.special import binom
from mechanism import g_coeffs, toep, jets_and_rows, jacobian, J0_matrix, s_exp
from conformal import riemann_map, composition_matrix

def solve_stage(P, m, theta, fcoef=None):
    L=m+1; h=max(1,int(theta*m)); q=3*m//8
    g=g_coeffs(P, 4*m+10); U=np.eye(L,k=1)
    J0inv=np.linalg.inv(J0_matrix(q))
    wh=(np.arange(h)+1.0)**s_exp; wq=(np.arange(q)+1.0)**s_exp
    C = composition_matrix(fcoef,h).real if fcoef is not None else np.eye(h)
    v=np.zeros(q); x=np.zeros(q)
    for it in range(15):
        g2=dict(g)
        for d in range(q): g2[-(m-d)]=g.get(-(m-d),0.0)+v[d]
        G2=toep(g2,L); M2,rows2,_=jets_and_rows(G2,U,h)
        res=np.max(np.abs(M2))
        if res<1e-16: break
        A2=C@(jacobian(G2,rows2,h,q)@J0inv)
        Aw=wh[:,None]*A2/wq[None,:]
        dx=np.linalg.lstsq(Aw,-wh*(C@M2),rcond=None)[0]/wq
        x+=dx; v=J0inv@x
    return v, x, res, h, q

def restore(v, m):
    # D_v = L_v - L_v(-1) K_m ; L_v(s)=s^-m sum v_d s^d ; K_m(s)=(-s)^{-m-1}((1-s^{-1})/2)^m
    D={}
    for d,c in enumerate(v): D[-(m-d)]=D.get(-(m-d),0.0)+c
    Lm1=sum(c*(-1.0)**(-(m-d)) for d,c in enumerate(v))
    # K_m coefficients: (-1)^{-m-1} s^{-m-1} * 2^{-m} sum_j C(m,j) (-1)^j s^{-j}
    for j in range(m+1):
        K = (-1.0)**(m+1) * binom(m,j)*(-1.0)**j / 2.0**m
        D[-(m+1)-j]=D.get(-(m+1)-j,0.0) - Lm1*K
    # check D(-1)=0
    val=sum(c*(-1.0)**p for p,c in D.items())
    return D, val, Lm1

theta=1/16
tau1=1e-3
P1={1:tau1, 2:tau1}
f1=riemann_map(P1)
v1,x1,res1,h1,q1=solve_stage(P1,64,theta,f1)
D1,endpoint,Lm1=restore(v1,64)
print(f"stage1 m=64 h={h1} q={q1}: residual {res1:.1e}, ||x||_Hs {np.sqrt(np.sum(((np.arange(q1)+1.0)**s_exp*x1)**2)):.3e}, ||v||_1 {np.sum(np.abs(v1)):.3e}, L(-1)={Lm1:.3e}, D(-1) check {endpoint:.1e}")
P2=dict(P1)
for p,c in D1.items(): P2[p]=P2.get(p,0.0)+c
tau2=1e-5
P2[64]=P2.get(64,0.0)+tau2; P2[65]=P2.get(65,0.0)+tau2
print("stage-2 background: negative degrees", min(P2), "..", "positive degrees up to", max(P2), " #terms", len(P2))
f2=riemann_map(P2, N=16384)
print(f"f2: f_1={f2[1].real:.8f}, max|neg freq|={np.max(np.abs(f2[-100:])):.1e}")
for m in [512,1024,2048]:
    L=m+1; h=m//16; q=3*m//8
    g=g_coeffs(P2,4*m+10); U=np.eye(L,k=1); G=toep(g,L)
    M,rows,W=jets_and_rows(G,U,h)
    A=jacobian(G,rows,h,q)@np.linalg.inv(J0_matrix(q))
    C=composition_matrix(f2,h).real
    wh=(np.arange(h)+1.0)**s_exp; wq=(np.arange(q)+1.0)**s_exp
    for nm,AA,bb in (("t",A,M),("u",C@A,C@M)):
        Aw=wh[:,None]*AA/wq[None,:]; sv=np.linalg.svd(Aw,compute_uv=False)
        print(f"[nested] m={m} h={h} coord={nm}: sigma_min {sv.min():.4f} sigma_max {sv.max():.4f} | max|b| m^1.5 {np.max(np.abs(bb))*m**1.5:.3e} ||b||_Hs m^1.25 {np.sqrt(np.sum(wh**2*bb**2))*m**1.25:.3e}")
v2,x2,res2,h2,q2=solve_stage(P2,512,theta,f2)
print(f"stage2 m=512 h={h2} q={q2}: residual {res2:.1e}, ||x||_Hs {np.sqrt(np.sum(((np.arange(q2)+1.0)**s_exp*x2)**2)):.3e} (x m^1.25 = {np.sqrt(np.sum(((np.arange(q2)+1.0)**s_exp*x2)**2))*512**1.25:.3e}), ||v||_1 {np.sum(np.abs(v2)):.3e}")
