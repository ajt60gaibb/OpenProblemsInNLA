"""Reproducible exact certificates and high-precision counterexample checks.

The fixed spectral example has a rational remainder certificate. The nuclear
family is proved by a divergent derivative lower bound, not by unreliable
large-dimensional finite differences. Hallman's two auxiliary conjectures are
checked separately from the main trace-tail conjectures, which are not settled.
"""
from __future__ import annotations
from pathlib import Path
import json
import numpy as np
import sympy as sp
import mpmath as mp
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=80

def cap_matrix(A: mp.matrix) -> mp.matrix:
    ev,U=mp.eigsy(A)
    return U*mp.diag([min(x,mp.mpf(1)) for x in ev])*U.T

def nuclear(A: mp.matrix) -> mp.mpf:
    ev=mp.eigsy(A,eigvals_only=True)
    return sum(abs(x) for x in ev)

def spectral_certificate() -> dict:
    B=sp.diag(sp.Rational(1,2),sp.Rational(127,128),sp.Rational(17,16))
    w=sp.Matrix([-3,2,4]); E=sp.eye(3)-w*w.T/29
    assert E*E==E and E.trace()==2
    b=list(B.diagonal()); f=[min(x,1) for x in b]
    L=sp.zeros(3)
    for i in range(3):
        for j in range(3):
            L[i,j]=(1 if b[i]<1 else 0) if i==j else (f[i]-f[j])/(b[i]-b[j])
    D=sp.matrix_multiply_elementwise(L,E)
    expected=sp.Matrix([[20,6,sp.Rational(32,3)],[6,25,-sp.Rational(8,9)],[sp.Rational(32,3),-sp.Rational(8,9),0]])/29
    assert D==expected
    v=sp.Matrix([2,3,1]); witness=(v.T*D*v)[0]/14
    assert witness==1+sp.Rational(25,1218)
    t=sp.Rational(1,65536);r=sp.Rational(9,256);d=sp.Rational(1,16)
    remainder_constant=2*(d+r)/r**2
    assert remainder_constant==sp.Rational(12800,81)
    assert t<r/2 and b[1]+t<1 and b[0]>t
    lower=witness-remainder_constant*t
    assert lower==1+sp.Rational(38125,2104704) and lower>1
    bm=mp.diag([mp.mpf(str(x.p))/int(x.q) for x in b])
    em=mp.matrix([[mp.mpf(str(E[i,j].p))/int(E[i,j].q) for j in range(3)] for i in range(3)])
    tm=mp.mpf(1)/65536
    delta=cap_matrix(bm+tm*em)-cap_matrix(bm)
    ev=mp.eigsy(delta,eigvals_only=True)
    ratio=max(abs(x) for x in ev)/tm
    vm=mp.matrix([2,3,1])/mp.sqrt(14)
    rayleigh=(vm.T*delta*vm)[0]/tm
    assert ratio>=rayleigh>mp.mpf(str(lower.p))/int(lower.q)>1
    return {'status':'PASS','t':'1/65536','input_relative_error':1,
            'exact_derivative_rayleigh':str(witness),
            'exact_remainder_constant':str(remainder_constant),
            'rigorous_transformed_error_ratio_lower_bound':str(lower),
            'numerical_transformed_spectral_error_ratio':mp.nstr(ratio,40),
            'numerical_witness_rayleigh_ratio':mp.nstr(rayleigh,40),
            'scope':'Arbitrary ordered PSD approximations; not asserted to be an actual Nystrom approximation.'}

def nuclear_family() -> dict:
    rho=0.25; records=[]; finite=[]
    for m in [1,2,3,4,8,16,32,64,128]:
        indices=np.arange(m)
        K=1/(1+rho**(indices[None,:]-indices[:,None]))
        T=np.triu(np.ones((m,m)))
        D=np.block([[np.ones((m,m)),K],[K.T,np.zeros((m,m))]])/(2*m)
        normD=float(np.sum(abs(np.linalg.eigvalsh(D))))
        normK=float(np.sum(np.linalg.svd(K,compute_uv=False)))
        singular=1/(2*np.sin((2*np.arange(1,m+1)-1)*np.pi/(4*m+2)))
        assert np.allclose(np.linalg.svd(T,compute_uv=False),singular,rtol=2e-12,atol=2e-12)
        error=float(np.linalg.norm(K-(T-np.eye(m)/2),'fro')**2)
        assert error<=2*m*rho**2/(1-rho**2)+1e-12
        assert normD>=normK/m-1e-12
        lower=float(np.log(m+1)/np.pi-.5-np.sqrt(2/15))
        assert normD>=lower-1e-12
        records.append({'m':m,'derivative_nuclear_norm':normD,'analytic_lower_bound':lower})
    for m in [1,2,4,8]:
        h=[mp.mpf(1)/4**i for i in range(1,m+1)]
        B=mp.diag([1-x for x in h]+[1+x for x in h])
        E=mp.ones(2*m)/(2*m)
        t=h[-1]/65536
        K=mp.matrix([[h[i]/(h[i]+h[j]) for j in range(m)] for i in range(m)])
        D=mp.zeros(2*m)
        for i in range(m):
            for j in range(m):
                D[i,j]=mp.mpf(1)/(2*m)
                D[i,j+m]=K[i,j]/(2*m)
                D[j+m,i]=K[i,j]/(2*m)
        fd=(cap_matrix(B+t*E)-cap_matrix(B))/t
        discrepancy=nuclear(fd-D)
        assert discrepancy<mp.mpf('0.0001')
        finite.append({'m':m,'t':mp.nstr(t,25),'derivative_nuclear_norm':mp.nstr(nuclear(D),30),
                       'finite_difference_nuclear_norm':mp.nstr(nuclear(fd),30),
                       'nuclear_difference_from_derivative':mp.nstr(discrepancy,12)})
    return {'status':'PASS','singular_value_formula_checks':len(records),'records':records,
            'high_precision_finite_difference_checks':finite,
            'proof_basis':'The analytic lower bound diverges; finite computations are illustrations only.'}

def gamma_certificates() -> dict:
    x,y=sp.symbols('x y',positive=True)
    p=sp.exp(-x)*(x*x-2*x+2)-2*sp.exp(-2*x)
    convolution=sp.integrate((x-y)**2/2*sp.exp(-(x-y))*2*sp.exp(-2*y),(y,0,x))
    assert sp.simplify(p-convolution)==0
    first=-sp.exp(-x)*(x-2)**2+4*sp.exp(-2*x)
    second=sp.exp(-x)*(x-2)*(x-4)-8*sp.exp(-2*x)
    assert sp.simplify(sp.diff(p,x)-first)==0
    assert sp.simplify(sp.diff(p,x,2)-second)==0
    assert sp.integrate(p,(x,0,sp.oo))==1
    assert sp.integrate(x*p,(x,0,sp.oo))==sp.Rational(7,2)
    # Exact sign arguments: e<3 implies e^(5/2)<9 sqrt(3)<16,
    # since 243<256. At x=4 the second derivative is -8 e^-8<0;
    # at x=5 it is e^-10(3e^5-8)>0 since e^5>1+5=6.
    assert 243<256 and 3*(1+5)>8
    mode=2+2*mp.lambertw(mp.e**-1)
    upper_inflection=mp.findroot(lambda z: mp.e**(-z)*(z-2)*(z-4)-8*mp.e**(-2*z),(4,5))
    assert mode>mp.mpf(5)/2
    assert upper_inflection>4
    return {'status':'PASS','density':'exp(-x)*(x^2-2*x+2)-2*exp(-2*x)',
            'density_integral':1,'mean_Y':'7/2','mean_Q':'3/2','variance_Q':'5/4',
            'mode_Y':mp.nstr(mode,40),'mode_normalized_Y':mp.nstr(mode/(mp.mpf(3)/2),40),
            'conjecture_1_claimed_upper_mode':'5/3',
            'upper_inflection_Y':mp.nstr(upper_inflection,40),
            'upper_inflection_Y_minus_EQ':mp.nstr(upper_inflection-mp.mpf(3)/2,40),
            'conjecture_2_claimed_upper_inflection':'5/2',
            'scope':'Refutes auxiliary Conjectures 1 and 2 of arXiv:2411.15454v1; does not settle Conjectures 3 or 4.'}

def main() -> None:
    result={'status':'PASS','mpmath_decimal_precision':mp.mp.dps,
            'spectral':spectral_certificate(),'nuclear':nuclear_family(),'gamma_auxiliary':gamma_certificates()}
    (ROOT/'results'/'counterexample_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
