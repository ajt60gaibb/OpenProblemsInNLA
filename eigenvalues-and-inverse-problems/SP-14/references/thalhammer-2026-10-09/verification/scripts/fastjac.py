import numpy as np
from numpy.fft import rfft2, irfft2
from mechanism import g_coeffs, toep, J0_matrix, s_exp
from conformal import riemann_map, composition_matrix

def jets_rows_fast(G, U, h):
    H = G @ G - U
    W = np.linalg.inv(H)
    m = G.shape[0]-1
    rows = np.empty((h, m+1))
    r = W[0,:].copy()
    for k in range(h):
        rows[k] = r
        r = np.concatenate([[0.0], r[:-1]]) @ W
    return rows[:, m].copy(), rows

def jacobian_fft(G, rows, h, q):
    X = rows @ G                     # h x L
    R = rows[:, :q]; Xq = X[:, :q]
    nk, nd = 2*h, 2*q
    FR = rfft2(R, s=(nk, nd)); FX = rfft2(Xq, s=(nk, nd))
    prod = irfft2(FR*FX, s=(nk, nd))
    return -2*prod[:h, :q]

def sigma_u(P, m, fcoef, theta=1/16):
    L=m+1; h=int(theta*m); q=3*m//8
    g=g_coeffs(P,4*m+10); U=np.eye(L,k=1); G=toep(g,L)
    M,rows=jets_rows_fast(G,U,h)
    A=jacobian_fft(G,rows,h,q)@np.linalg.inv(J0_matrix(q))
    C=composition_matrix(fcoef,h).real
    wh=(np.arange(h)+1.0)**s_exp; wq=(np.arange(q)+1.0)**s_exp
    Aw=wh[:,None]*(C@A)/wq[None,:]
    sv=np.linalg.svd(Aw,compute_uv=False)
    bb=C@M
    return sv.min(), sv.max(), np.max(np.abs(bb))*m**1.5, np.sqrt(np.sum(wh**2*bb**2))*m**1.25, h, q

if __name__=="__main__":
    import sys
    # sanity: fft jacobian equals direct one at m=256
    from mechanism import jacobian, jets_and_rows
    P={-60:5e-4,-61:5e-4,1:1e-3,2:1e-3}; m=256; L=m+1; h=16; q=96
    g=g_coeffs(P,4*m+10); U=np.eye(L,k=1); G=toep(g,L)
    M,rows,_=jets_and_rows(G,U,h); J1=jacobian(G,rows,h,q)
    M2,rows2=jets_rows_fast(G,U,h); J2=jacobian_fft(G,rows2,h,q)
    print("fft jacobian check:", np.abs(J1-J2).max()/np.abs(J1).max())
    for amp in [5e-4, 2e-3]:
        P={-60:amp,-61:amp,1:1e-3,2:1e-3}
        f=riemann_map(P,N=16384)
        for m in [2048, 4096]:
            smin,smax,fm,fh,h,q=sigma_u(P,m,f)
            print(f"deg60 amp={amp}: m={m} h={h}: sigma_min {smin:.4f} sigma_max {smax:.4f} | max|b| m^1.5 {fm:.3e} ||b||_Hs m^1.25 {fh:.3e}", flush=True)
