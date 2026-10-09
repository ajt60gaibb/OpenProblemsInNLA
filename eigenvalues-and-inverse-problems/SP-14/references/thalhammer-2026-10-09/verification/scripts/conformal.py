import numpy as np
from mechanism import g_coeffs, toep, jets_and_rows, jacobian, J0_matrix, s_exp

def h_on_circle(P, N):
    phi = 2*np.pi*np.arange(N)/N
    s = np.exp(1j*phi)
    g0 = np.sqrt(1+1/s)                       # principal branch, continuous on the circle
    Pv = sum(c*s**p for p,c in P.items())
    g = g0 + Pv
    return s*g*g - 1

def riemann_map(P, N=8192, iters=60):
    """Normalized Riemann map f of the interior of Gamma=h(T): Taylor coefficients f_1..f_{N/2}."""
    hv = h_on_circle(P, N)
    ang = np.unwrap(np.angle(hv)); ang -= ang[0] - np.angle(hv[0])
    # polar graph: ell(theta)=log|point at angle theta|
    theta_grid = 2*np.pi*np.arange(N)/N
    # make ang start near 0 and increasing
    ang_mod = ang - 2*np.pi*np.floor(ang[0]/(2*np.pi))
    order = np.argsort(ang_mod % (2*np.pi))
    th_s = (ang_mod % (2*np.pi))[order]; ell_s = np.log(np.abs(hv))[order]
    th_ext = np.concatenate([th_s-2*np.pi, th_s, th_s+2*np.pi]); ell_ext = np.tile(ell_s,3)
    ell = lambda t: np.interp(np.mod(t, 2*np.pi), th_ext, ell_ext)
    def hilbert(x):
        X = np.fft.fft(x); n = np.fft.fftfreq(N, 1/N)
        X = -1j*np.sign(n)*X; X[0]=0
        return np.real(np.fft.ifft(X))
    u = np.zeros(N)
    for _ in range(iters):
        u_new = hilbert(ell(theta_grid+u))
        if np.max(np.abs(u_new-u)) < 1e-15: u = u_new; break
        u = u_new
    fb = np.exp(ell(theta_grid+u))*np.exp(1j*(theta_grid+u))
    coef = np.fft.fft(fb)/N
    return coef   # coef[k] = [u^k] f, k>=0 ; negative-frequency entries should be ~0

def composition_matrix(fcoef, h):
    # C[k,l] = [u^k] f(u)^l, k,l<h
    C = np.zeros((h,h), dtype=complex)
    pw = np.zeros(h, dtype=complex); pw[0]=1
    f = fcoef[:h].copy()
    for l in range(h):
        C[:,l] = pw
        pw = np.convolve(pw, f)[:h]
    return C

def analyze(P, ms, label):
    fcoef = riemann_map(P)
    neg = np.max(np.abs(fcoef[-50:])); print(f"[{label}] f_1={fcoef[1].real:.8f}+{fcoef[1].imag:.1e}i, f_0={abs(fcoef[0]):.1e}, max|neg freq|={neg:.1e}, f_2..f_4={np.round(fcoef[2:5].real,6)}")
    for m in ms:
        L=m+1; h=m//16; q=3*m//8
        g=g_coeffs(P, 4*m+10); U=np.eye(L,k=1); G=toep(g,L)
        M, rows, W = jets_and_rows(G,U,h)
        J=jacobian(G,rows,h,q); J0inv=np.linalg.inv(J0_matrix(q)); A=J@J0inv
        C=composition_matrix(fcoef,h).real
        Au=C@A; bu=C@M
        wh=(np.arange(h)+1.0)**s_exp; wq=(np.arange(q)+1.0)**s_exp
        for nm,AA,bb in (("t",A,M),("u",Au,bu)):
            Aw=wh[:,None]*AA/wq[None,:]
            sv=np.linalg.svd(Aw,compute_uv=False)
            print(f"[{label}] m={m:5d} h={h:3d} coord={nm}: sigma_min {sv.min():.4f} sigma_max {sv.max():.4f} ||A_w-I|| {np.linalg.norm(Aw-np.eye(h,q),2):.4f} | forcing: max|b|*m^1.5 {np.max(np.abs(bb))*m**1.5:.3e}, ||b||_Hs*m^1.25 {np.sqrt(np.sum(wh**2*bb**2))*m**1.25:.3e}, |b_0|*m^2.5 {abs(bb[0])*m**2.5:.3e}, |b_{{h-1}}|*m^2.5/h {abs(bb[h-1])*m**2.5/h:.3e}")

tau=1e-3
analyze({1:tau, 2:tau}, [128,256,512,1024,2048], "P+ only")
analyze({-2:0.5*tau, -3:0.5*tau}, [128,256,512,1024,2048], "P- only (P-(-1)=0)")
