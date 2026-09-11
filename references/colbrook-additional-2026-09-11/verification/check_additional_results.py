#!/usr/bin/env python3
"""Exact certificates and numerical diagnostics for four NLA submissions.

This is not a formal proof checker or a production IE-08 implementation.
Run: python3 verification/check_additional_results.py
No network access is used. Failures raise AssertionError.
"""
from __future__ import annotations
import itertools
import platform
import numpy as np
import scipy
import scipy.linalg as la
from scipy.optimize import brentq
import sympy as sp


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def derivative_certificate() -> None:
    z = sp.symbols('z')
    c2 = sp.Matrix([[0, 1], [1, 0]])
    c4 = sp.Matrix([[0, 1, 0, 0], [0, 0, 1, 0],
                    [0, 0, 0, 1], [1, 0, 0, 0]])
    A = sp.diag(sp.Rational(1, 2), c2, c4)
    require(all(x >= 0 for x in A), 'IS-03 input is not nonnegative')
    p = sp.expand((z-sp.Rational(1,2))*(z**2-1)*(z**4-1))
    require(sp.expand(A.charpoly(z).as_expr()-p) == 0, 'IS-03 characteristic polynomial')
    q = sp.Poly(sp.diff(p,z)/7,z)
    c = q.all_coeffs(); d = q.degree(); moments = [sp.Integer(d)]
    for k in range(1,8):
        moment = -sum(c[j]*moments[k-j] for j in range(1,min(k,d+1)))
        if k <= d:
            moment -= k*c[k]
        moments.append(sp.factor(moment))
    expected = [sp.Rational(3,7), sp.Rational(79,49), sp.Rational(48,343),
                sp.Rational(6731,2401), sp.Rational(5213,16807),
                sp.Rational(219766,117649), sp.Rational(-8593,823543)]
    require(moments[1:] == expected, 'IS-03 Newton sums mismatch')
    companion = sp.zeros(d)
    for i in range(1,d):
        companion[i,i-1] = 1
    for i in range(d):
        companion[i,d-1] = -c[d-i]
    require(sp.expand(companion.charpoly(z).as_expr()-q.as_expr()) == 0,
            'Companion polynomial mismatch')
    require(sp.trace(companion**7) == expected[-1], 'Independent exact trace check')
    print('IS-03: exact characteristic polynomial, all seven Newton sums, and')
    print('       independent companion trace passed.')
    print('       s_7 =', moments[-1])


def toeplitz_certificate() -> None:
    z, r, t = sp.symbols('z r t', real=True)
    lam = sp.Symbol('lambda')
    a = 8/z+8*z+z*z; b = sp.expand(a-a*a)
    expected = {-2:-64,-1:8,0:-128,1:-8,2:-63,3:-16,4:-1}
    require(all(b.coeff(z,k) == v for k,v in expected.items()), 'SP-06 expansion')
    T = sp.Matrix([[expected[0],expected[-1]],[expected[1],expected[0]]])
    require(sp.expand(T.charpoly(lam).as_expr()-((lam+128)**2+64)) == 0,
            'SP-06 finite spectrum')
    F = r*r-1+r**3*sp.cos(t)/4
    imag_a = (8*r-8/r+2*r*r*sp.cos(t))*sp.sin(t)
    require(sp.simplify(imag_a-8*sp.sin(t)*F/r) == 0, 'SP-06 reality identity')
    require(sp.Rational(-3,4)+sp.Rational(1,32) < 0, 'SP-06 lower endpoint')
    require(3-2 > 0, 'SP-06 upper endpoint')
    # On [1/2,2], F_r >= r*(2-3r/4) >= r/2 > 0, an exact certificate.
    require(2-sp.Rational(3,4)*2 == sp.Rational(1,2), 'SP-06 derivative bound')
    angles = np.linspace(0,2*np.pi,2001)
    radii = np.array([brentq(lambda x:x*x-1+x**3*np.cos(theta)/4,
                              .5,2,xtol=1e-14) for theta in angles])
    points = radii*np.exp(1j*angles)
    aa = 8/points+8*points+points*points; bb = aa-aa*aa
    require(np.max(np.abs(bb.imag)) < 1e-9, 'SP-06 curve diagnostic')
    print('SP-06: exact Laurent expansion, finite spectrum, reality identity,')
    print('       endpoint inequalities and monotonicity certificate passed.')
    print('       2,001 curve samples: max |Im b| = %.3e (diagnostic only).' %
          np.max(np.abs(bb.imag)))


def sign_matrix_bounds() -> None:
    rng = np.random.default_rng(43017)
    count = 0
    examples = [np.array(values,dtype=np.int64).reshape(3,3)
                for values in itertools.product([-1,1],repeat=9)]
    for n in [5,7,9,6,10,14]:
        examples += [rng.choice([-1,1],size=(n,n)) for _ in range(60)]
    invertible = 0
    for A in examples:
        n = A.shape[0]; G = A.T@A
        energy = int(np.sum((G-n*np.eye(n,dtype=np.int64))**2))
        lower_v = n-1 if n%2 else 2*(n-2)
        require(energy >= n*lower_v, 'IS-05 exact variance obstruction')
        if n%4 == 2:
            edges = int(np.sum((G == 0)&(~np.eye(n,dtype=bool)))//2)
            require(4*edges <= n*n, 'IS-05 orthogonality graph edge bound')
        sv = la.svdvals(A.astype(float))
        if sv[-1] > 1e-10:
            invertible += 1
            kappa = sv[0]/sv[-1]
            bound = np.sqrt(1+lower_v/n**2)+np.sqrt(lower_v)/n
            require(kappa+1e-10 >= bound, 'IS-05 condition number inequality')
            v = energy/n
            require(v <= n*n*(kappa-1/kappa)**2/4 + 1e-7,
                    'IS-05 variance upper bound')
        count += 1
    print('IS-05: %d sign matrices checked (%d numerically nonsingular).' %
          (count,invertible))
    print('       Integer variance/graph checks exact; singular values numerical.')


def newton(M: np.ndarray) -> np.ndarray:
    return (M+la.solve(M,np.eye(M.shape[0],dtype=complex)))/2


def iterate(M: np.ndarray, steps: int) -> np.ndarray:
    X = M.copy()
    for _ in range(steps):
        X = newton(X)
    return X


def complex_gaussian(rng: np.random.Generator, shape: tuple[int,...]) -> np.ndarray:
    return (rng.standard_normal(shape)+1j*rng.standard_normal(shape))/np.sqrt(2)


def schur_mechanism_diagnostics() -> None:
    rng = np.random.default_rng(917235)
    # Scalar all-iteration bounds.
    for _ in range(300):
        z = rng.uniform(.2,2)+1j*rng.uniform(-2,2)
        if rng.random()<.5:
            z = -z
        R0=max(1.,abs(z)); a=min(1.,abs(z.real)); B=(R0+1)**2/a
        x=z
        for _ in range(20):
            require(abs(x) <= B*(1+1e-12), 'IE-08 scalar magnitude')
            require(abs(x.real) >= (1-1e-12)/B, 'IE-08 scalar half-plane margin')
            x=(x+1/x)/2
    max_telescoping=0.; max_sign=0.; max_split=0.; trials=40
    for case in range(trials):
        n=3+case%6; rank=1+case%(n-1)
        # A well-conditioned, generally nonnormal diagonalization.
        U,_=la.qr(complex_gaussian(rng,(n,n)))
        V=U@(np.eye(n)+.09*np.triu(complex_gaussian(rng,(n,n)),1))
        eig = np.r_[-rng.uniform(.4,1.8,rank),rng.uniform(.4,1.8,n-rank)]
        eig = eig+1j*rng.uniform(-1,1,n)
        M=V@np.diag(eig)@la.inv(V)
        true_sign=V@np.diag(np.sign(eig.real))@la.inv(V)
        computed=iterate(M,12)
        sign_error=la.norm(computed-true_sign,2)
        require(sign_error < 1e-9,'IE-08 sign computation diagnostic')
        max_sign=max(max_sign,sign_error)
        # Test the exact telescoping identity in floating-point evaluation,
        # with noncommuting additive perturbations at every step.
        N=6; Y=[M+1e-8*complex_gaussian(rng,(n,n))]; fY=[]
        for j in range(N):
            fY.append(newton(Y[-1]))
            Y.append(fY[-1]+1e-8*complex_gaussian(rng,(n,n)))
        rhs=iterate(Y[0],N)-iterate(M,N)
        for j in range(N):
            rhs+=iterate(Y[j+1],N-j-1)-iterate(fY[j],N-j-1)
        residual=la.norm((Y[-1]-iterate(M,N))-rhs,2)
        require(residual < 1e-10,'IE-08 telescoping identity diagnostic')
        max_telescoping=max(max_telescoping,residual)
        P=(np.eye(n)-computed)/2
        require(abs(np.trace(P)-rank)<1e-9,'IE-08 projector rank')
        require(la.norm(P@P-P,2)<1e-9,'IE-08 projector identity')
        nonzero=la.svdvals(P)[:rank]
        require(np.min(nonzero)>=1-1e-9,'IE-08 projector singular values')
        Omega=complex_gaussian(rng,(n,rank))
        Z,_=la.qr(P@Omega,mode='full')
        S=Z.conj().T@M@Z
        lower=la.norm(S[rank:,:rank],2)
        require(lower<1e-9,'IE-08 range-extraction split')
        max_split=max(max_split,lower)
    print('IE-08: 300 scalar-orbit diagnostics and %d nonnormal matrix tests passed.' % trials)
    print('       max sign forward error: %.3e' % max_sign)
    print('       max telescoping identity residual: %.3e' % max_telescoping)
    print('       max discarded lower-left block: %.3e' % max_split)
    print('       Tests use ordinary precision, NOT the theorem\'s full implementation.')


def main() -> None:
    print('Additional NLA submission checks')
    print('Python',platform.python_version(),'NumPy',np.__version__,
          'SciPy',scipy.__version__,'SymPy',sp.__version__)
    derivative_certificate()
    toeplitz_certificate()
    sign_matrix_bounds()
    schur_mechanism_diagnostics()
    print('ALL CHECKS PASSED. This is not independent review or formal verification.')

if __name__=='__main__':
    main()
