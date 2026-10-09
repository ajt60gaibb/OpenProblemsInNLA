import numpy as np
from mechanism import g_coeffs, toep, jets_and_rows, jacobian, J0_matrix, s_exp
from conformal import riemann_map, composition_matrix, h_on_circle
# High-degree negative background with P-(-1)=0 and non-negligible W^0 norm, plus a tiny positive packet.
for amp, deg in [(5e-4, 60), (2e-3, 60), (5e-4, 200)]:
    P={-deg: amp, -(deg+1): amp, 1: 1e-3, 2: 1e-3}
    f=riemann_map(P, N=16384)
    hv=h_on_circle(P,4096); dev=np.max(np.abs(hv-np.exp(2j*np.pi*np.arange(4096)/4096)))
    print(f"=== P- = {amp}(s^-{deg}+s^-{deg+1}) + 1e-3 s(1+s): sup|h-s| = {dev:.3e}, f_1 = {f[1].real:.6f}, max|neg| {np.max(np.abs(f[-200:])):.1e}")
    for m in [512,1024,2048]:
        if m < 2*deg: continue
        L=m+1; h=m//16; q=3*m//8
        g=g_coeffs(P,4*m+10); U=np.eye(L,k=1); G=toep(g,L)
        M,rows,W=jets_and_rows(G,U,h)
        A=jacobian(G,rows,h,q)@np.linalg.inv(J0_matrix(q))
        C=composition_matrix(f,h).real
        wh=(np.arange(h)+1.0)**s_exp; wq=(np.arange(q)+1.0)**s_exp
        Aw=wh[:,None]*(C@A)/wq[None,:]; sv=np.linalg.svd(Aw,compute_uv=False)
        bb=C@M
        print(f"   m={m} h={h}: u-coord sigma_min {sv.min():.4f} sigma_max {sv.max():.4f} | max|b| m^1.5 {np.max(np.abs(bb))*m**1.5:.3e} ||b||_Hs m^1.25 {np.sqrt(np.sum(wh**2*bb**2))*m**1.25:.3e}")
