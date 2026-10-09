# Probe of the central mechanism: for a fixed small background P (positive packet + a
# negative piece), how do (i) the forcing jets, (ii) the right-inverse norm of the
# preconditioned finite Jacobian, and (iii) the exact Newton solution scale with m?
import numpy as np, sys
from scipy.special import binom
from scipy.linalg import solve_triangular
s_exp = -0.25

def g_coeffs(P, K):
    g = {-k: binom(0.5, k) for k in range(K)}
    for p, c in P.items(): g[p] = g.get(p, 0.0) + c
    return g

def toep(coefs, L):
    idx = np.arange(L)
    T = np.zeros((L, L))
    for d, c in coefs.items():
        if -L < d < L:
            T[np.arange(max(0,d), min(L, L+d)), np.arange(max(0,-d), min(L, L-d))] = c
    return T

def jets_and_rows(G, U, h):
    H = G @ G - U
    W = np.linalg.inv(H)
    m = G.shape[0]-1
    rows = []
    r = W[0, :].copy()
    for k in range(h):
        rows.append(r)
        r = np.concatenate([[0.0], r[:-1]]) @ W     # r U W
    M = np.array([rows[k][m] for k in range(h)])
    return M, rows, W

def jacobian(G, rows, h, q):
    # J[k,d] = dM_k / d g_{-(m-d)} = -2 sum_l [s^d](R_l X_{k-l})
    X = [r @ G for r in rows]
    J = np.zeros((h, q))
    for k in range(h):
        acc = np.zeros(q)
        for l in range(k+1):
            acc += np.convolve(rows[l][:q], X[k-l][:q])[:q]
        J[k] = -2*acc
    return J

def J0_matrix(q):
    J0 = np.zeros((q, q))
    for k in range(q):
        d = np.arange(k, q)
        J0[k, d] = -2*(k+1)*binom(0.5, d-k)
    return J0

def run(P, m, theta, sigma=3/8, newton=True, verbose=False):
    L = m+1; q = int(sigma*m); h = max(1, int(theta*m))
    g = g_coeffs(P, 4*m+10)
    U = np.eye(L, k=1)
    G = toep(g, L)
    M, rows, W = jets_and_rows(G, U, h)
    J = jacobian(G, rows, h, q)
    J0 = J0_matrix(q)
    J0inv = np.linalg.inv(J0)
    A = J @ J0inv                       # h x q preconditioned finite Jacobian
    wh = (np.arange(h)+1.0)**s_exp; wq = (np.arange(q)+1.0)**s_exp
    Aw = wh[:,None]*A/wq[None,:]
    sv = np.linalg.svd(Aw, compute_uv=False)
    out = dict(m=m, h=h, q=q, forcing_max=float(np.max(np.abs(M))),
               forcing_Hs=float(np.sqrt(np.sum(wh**2*M**2))),
               sigma_min=float(sv.min()), sigma_max=float(sv.max()),
               condW=float(np.linalg.cond(W)))
    if newton:
        v = np.zeros(q); x = np.zeros(q)
        for it in range(12):
            g2 = dict(g)
            for d in range(q): g2[-(m-d)] = g.get(-(m-d),0.0) + v[d]
            G2 = toep(g2, L)
            M2, rows2, _ = jets_and_rows(G2, U, h)
            res = np.max(np.abs(M2))
            if verbose: print(f"   newton it {it}: residual {res:.3e}")
            if res < 1e-15: break
            J2 = jacobian(G2, rows2, h, q)
            A2 = J2 @ J0inv
            A2w = wh[:,None]*A2/wq[None,:]
            dx_w = np.linalg.lstsq(A2w, -wh*M2, rcond=None)[0]   # minimal Euclidean norm = minimal H^s norm
            dx = dx_w/wq
            x = x + dx
            v = J0inv @ x
        out.update(newton_residual=float(res), x_Hs=float(np.sqrt(np.sum(wq**2*x**2))),
                   v_l1=float(np.sum(np.abs(v))), R1=float(np.sum(np.abs(x)/(np.arange(q)+1))),
                   Rhalf=float(np.sum(np.abs(x)/np.sqrt(np.arange(q)+1))))
    return out

if __name__ == "__main__":
    tau = 1e-3
    P = {1: tau, 2: tau, -2: 0.5*tau, -3: -0.5*tau}   # P_+ = tau s(1+s); P_- = 0.5 tau (s^-2 - s^-3), both vanish at -1
    theta = float(sys.argv[1]) if len(sys.argv)>1 else 1/16
    print(f"background P={P}, theta={theta}, s={s_exp}")
    prev=None
    for m in [32, 64, 128, 256, 512]:
        o = run(P, m, theta)
        line = (f"m={m:4d} h={o['h']:3d} q={o['q']:3d} | forcing max {o['forcing_max']:.3e} "
                f"(x m^1.5 = {o['forcing_max']*m**1.5:.3e}) | sigma_min {o['sigma_min']:.4f} sigma_max {o['sigma_max']:.3f} "
                f"| cond(W) {o['condW']:.2f} | Newton res {o['newton_residual']:.1e} ||x||_Hs {o['x_Hs']:.3e} "
                f"(x m^1.25 = {o['x_Hs']*m**1.25:.3e}) ||v||_1 {o['v_l1']:.3e} (x m = {o['v_l1']*m:.3e})")
        print(line, flush=True)
