"""Supporting algebraic/numerical diagnostics for five proposed NLA arguments.

The exact certificates and mathematical proofs carry the conclusions.
The randomized checks here are diagnostics, not proofs.
Run with Python 3, NumPy, SciPy, and SymPy.
"""
from itertools import product
import numpy as np
import sympy as sp
from scipy.linalg import eigh
from scipy.optimize import brentq


def check_is02():
    S = sp.Matrix([[0, 1], [1, 0]])
    J = sp.ones(2) / 2
    A = sp.diag(S, J)
    assert A * sp.ones(4, 1) == sp.ones(4, 1)
    assert A == A.T
    assert A.trace() == 1
    assert A.eigenvals() == {sp.Integer(1): 2, sp.Integer(-1): 1, sp.Integer(0): 1}
    assert A == (sp.diag(S, sp.eye(2)) + sp.diag(S, S)) / 2
    print('IS-02: exact spectrum, stochasticity, trace, and nonvertex identity verified.')


def check_sp04():
    s = np.array([1.751, 1.755, 1.759])
    tmax = sp.Rational(13, 25)
    # Bounds used to exclude all positive stationary diagonals for 0 <= c <= tmax.
    assert sp.Rational(7, 4)**2 - 4*tmax > sp.Rational(9, 10)**2
    assert tmax * sp.Rational(44, 25) * sp.Rational(51, 50) < 1
    # At t=tmax a negative root has magnitude >1/4 and the positive roots exceed 2.
    assert sp.Rational(1, 4)**2 + sp.Rational(44,25)/4 < tmax
    assert 4 - 2*sp.Rational(7,4) - tmax < 0
    neg_stationary = []
    for neg in product([False, True], repeat=3):
        if not any(neg):
            continue
        neg = np.array(neg)
        def vals(t):
            plus = (s + np.sqrt(s*s + 4*t))/2
            return np.where(neg, -t/plus, plus)
        def f(t):
            return np.prod(np.abs(vals(t))) - 1
        hi = 1.
        while f(hi) < 0:
            hi *= 2
        t = brentq(f, 0., hi, xtol=1e-14)
        x = vals(t)
        neg_stationary.append((t, tuple(neg), x, np.sum((s-x)**2)))
    neg_stationary.sort(key=lambda v:v[0])
    t, neg, x, dist2 = neg_stationary[0]
    assert neg == (True, False, False)
    assert t < float(tmax)
    assert np.max(np.abs(x*(s-x)+t)) < 1e-12
    assert abs(abs(np.prod(x))-1) < 1e-12
    flipped = np.abs(x)
    assert np.sum((s-flipped)**2) < dist2
    # The all-plus positive-multiplier branch also contains a better stationary point.
    cmax = min(s*s)/4
    def pos(c): return (s + np.sqrt(s*s-4*c))/2
    cp = brentq(lambda c: np.prod(pos(c))-1, 0., cmax)
    print('SP-04: rational bounds verified.')
    print(f'  least absolute multiplier: c={-t:.12f}; X diagonal={x}')
    print(f'  squared distance={dist2:.12f}; sign-flipped distance={np.sum((s-flipped)**2):.12f}')
    print(f'  all-plus stationary c={cp:.12f}; squared distance={np.sum((s-pos(cp))**2):.12f}')


def orthogonal_sector_bases(n):
    sy, sk = [], []
    for i in range(n):
        E = np.zeros((n,n)); E[i,i] = 1
        sy.append(E.ravel(order='F'))
        for j in range(i+1,n):
            E = np.zeros((n,n)); E[i,j]=E[j,i]=1/np.sqrt(2)
            sy.append(E.ravel(order='F'))
            E = np.zeros((n,n)); E[i,j]=1/np.sqrt(2); E[j,i]=-1/np.sqrt(2)
            sk.append(E.ravel(order='F'))
    return np.column_stack(sy), np.column_stack(sk)


def check_sp05(rng):
    worst_ratio = 0.
    for n in range(2,9):
        sy, sk = orthogonal_sector_bases(n)
        for _ in range(12):
            Z=rng.normal(size=(n,n)); A=Z.T@Z+0.1*np.eye(n)
            Z=rng.normal(size=(n,n)); B=Z.T@Z+0.1*np.eye(n)
            L=np.kron(A,B)+np.kron(B,A)
            ls=eigh(sy.T@L@sy,eigvals_only=True)[0]
            la=eigh(sk.T@L@sk,eigvals_only=True)[0]
            assert ls <= la + 1e-8
            worst_ratio=max(worst_ratio,ls/la)
            W=rng.normal(size=(n,n)); W=W-W.T
            H=1j*W
            ev,U=eigh(H)
            absH=(U*np.abs(ev))@U.conj().T
            assert np.max(np.abs(absH.imag))<1e-8
            PhiH=np.linalg.solve(L,H.ravel(order='F')).reshape((n,n),order='F')
            PhiAbs=np.linalg.solve(L,absH.ravel(order='F')).reshape((n,n),order='F')
            qH=np.vdot(H,PhiH).real
            qAbs=np.vdot(absH,PhiAbs).real
            assert qAbs >= qH-1e-8
    print(f'SP-05: 84 SPD-pair diagnostics passed; largest symmetric/skew minimum ratio={worst_ratio:.6f}.')


def check_ke04(rng):
    checked=0
    for p in range(1,5):
        for s in range(3,8):
            for _ in range(4):
                n=p*s; T=np.zeros((n,n))
                for k in range(s):
                    Z=rng.normal(size=(p,p))
                    T[k*p:(k+1)*p,k*p:(k+1)*p]=(Z+Z.T)/2
                    if k:
                        Z=rng.normal(size=(p,p))+3*np.eye(p)
                        T[k*p:(k+1)*p,(k-1)*p:k*p]=Z
                        T[(k-1)*p:k*p,k*p:(k+1)*p]=Z.T
                spectra={k:eigh(T[:k*p,:k*p],eigvals_only=True) for k in range(1,s+1)}
                for k in range(2,s):
                    for j in range(k+1,s+1):
                        for i in range((k-1)*p):
                            a,b=spectra[k][i],spectra[k][i+p]
                            assert np.any((spectra[j]>a)&(spectra[j]<b))
                            checked+=1
    print(f'KE-04: {checked} strict-interval diagnostics passed.')


def check_ke03_geometry(rng):
    # This verifies the shift-selection geometry, not an efficient floating-point
    # implementation of the exact high-degree Krylov algorithm.
    checked=0
    for eps in [0.49,0.3,0.1,0.03]:
        eta=eps**2/1024
        L=int(np.ceil(16/eps))
        t=np.linspace(-1,1,L+1)
        u=(1-t*t+2j*t)/(1+t*t)
        u=np.concatenate([u,-u])
        for _ in range(100):
            lam=rng.normal(size=20)+1j*rng.normal(size=20)
            rho=max(abs(lam))
            r=rho*(1+eta)**rng.uniform(-2,2)
            R=np.max(np.abs(lam[:,None]+r*u[None,:]),axis=0)
            # Any radius estimates within the proven multiplicative bounds.
            estimates=R*(1+eta)**rng.uniform(-1,1,size=len(u))
            j=np.argmax(estimates)
            mu=lam[np.argmax(abs(lam+r*u[j]))]
            z=r*u[j]
            assert abs(z-mu) < eps*rho/3 + 1e-12
            assert abs(mu) >= (1-eps)*rho
            checked+=1
    print(f'KE-03: {checked} geometric certificates tested with perturbed radius estimates.')


if __name__ == '__main__':
    rng=np.random.default_rng(20260911)
    check_is02()
    check_sp04()
    check_sp05(rng)
    check_ke04(rng)
    check_ke03_geometry(rng)
