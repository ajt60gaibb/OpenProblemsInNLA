import numpy as np
from mechanism import g_coeffs, toep, jets_and_rows, jacobian, J0_matrix, s_exp
tau = 1e-3
backgrounds = {"P+ only": {1: tau, 2: tau},
               "P- only": {-2: 0.5*tau, -3: -0.5*tau},
               "both":    {1: tau, 2: tau, -2: 0.5*tau, -3: -0.5*tau}}
for name, P in backgrounds.items():
    print("=== background", name, P)
    for m in [128, 256, 512, 1024]:
        L=m+1; h=m//16; q=3*m//8
        g=g_coeffs(P, 4*m+10); U=np.eye(L,k=1); G=toep(g,L)
        M, rows, W = jets_and_rows(G,U,h)
        ks=[0,1,2,4,8,16,h-1]
        prof=" ".join(f"k={k}:{M[k]*m**1.5:+.3e}" for k in ks if k<h)
        print(f" m={m:5d} jets x m^1.5: {prof}")
    # Jacobian structure at m=512
    m=512; L=m+1; h=m//16; q=3*m//8
    g=g_coeffs(P, 4*m+10); U=np.eye(L,k=1); G=toep(g,L)
    M, rows, W = jets_and_rows(G,U,h)
    J=jacobian(G,rows,h,q); J0=J0_matrix(q); A=J@np.linalg.inv(J0)
    wh=(np.arange(h)+1.0)**s_exp; wq=(np.arange(q)+1.0)**s_exp
    Aw=wh[:,None]*A/wq[None,:]
    E=Aw-np.eye(h,q)
    print(f" m=512: ||A_w - I||_2 = {np.linalg.norm(E,2):.4f}; max |E| entry {np.abs(E).max():.4f} at", np.unravel_index(np.abs(E).argmax(),E.shape))
    # where is the mass: norm of E restricted to columns < h vs >= h
    print(f"   ||E[:, :h]|| = {np.linalg.norm(E[:,:h],2):.4f}, ||E[:, h:]|| = {np.linalg.norm(E[:,h:],2):.4f}")
    # scaling of E with m for 'both'
