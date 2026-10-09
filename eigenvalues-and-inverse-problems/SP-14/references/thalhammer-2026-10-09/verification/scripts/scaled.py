import numpy as np
from fastjac import sigma_u
from conformal import riemann_map, h_on_circle
from scipy.special import binom
# Fixed W^{1+alpha} size of g0*P- while the degree grows: amp = c/deg^{1.125}; m = 32*deg so h = 2*deg.
alpha=0.125
for deg in [30, 60, 120]:
    amp=0.02/deg**(1+alpha)
    P={-deg:amp,-(deg+1):amp,1:1e-3,2:1e-3}
    # W^{1+alpha} norm of g0 P- (truncate the series)
    K=20000; g0=binom(0.5,np.arange(K))*0  # placeholder
    coef=np.zeros(K+deg+2)
    for n in range(K):
        b=binom(0.5,n)
        coef[n+deg]+=amp*b; coef[n+deg+1]+=amp*b      # powers s^{-(n+deg)}, s^{-(n+deg+1)}
    idx=np.arange(len(coef)); w1a=np.sum((1+idx)**(1+alpha)*np.abs(coef))
    hv=h_on_circle(P,8192); dev=np.max(np.abs(hv-np.exp(2j*np.pi*np.arange(8192)/8192)))
    f=riemann_map(P,N=16384)
    m=32*deg
    smin,smax,fm,fh,h,q=sigma_u(P,m,f)
    print(f"deg={deg} amp={amp:.2e}: ||g0 P-||_W^(1+a) ~ {w1a:.3f}, sup|h-s| {dev:.2e} | m={m} h={h}: sigma_min {smin:.4f} sigma_max {smax:.4f} | max|b| m^1.5 {fm:.3e} ||b||_Hs m^1.25 {fh:.3e}", flush=True)
