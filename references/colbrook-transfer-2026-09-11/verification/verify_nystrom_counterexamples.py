"""Exact Nyström certificates and 80-digit diagnostics.

The six-dimensional spectral example has a rational proof certificate.
The nuclear impossibility is certified by the analytical divergent lower bound
in the manuscript, not by the finite numerical examples recorded here.
"""
from __future__ import annotations
from pathlib import Path
import json
import sympy as sp
import mpmath as mp
from verify_counterexamples import cap_matrix,nuclear
ROOT=Path(__file__).resolve().parents[1]
mp.mp.dps=80

def to_mp(A: sp.Matrix) -> mp.matrix:
    return mp.matrix([[mp.mpf(str(A[i,j].p))/int(A[i,j].q)
                       for j in range(A.cols)] for i in range(A.rows)])

def spectral_example() -> dict:
    B=sp.diag(sp.Rational(1,2),sp.Rational(127,128),sp.Rational(17,16))
    U=sp.Matrix([[1,8],[8,1],[-4,4]])/9
    assert U.T*U==sp.eye(2)
    E=U*U.T
    F=sp.zeros(6)
    F[:3,:3]=64*E/65; F[:3,3:5]=8*U/65
    F[3:5,:3]=8*U.T/65;F[3:5,3:5]=sp.eye(2)/65;F[5,5]=1
    Omega=sp.eye(3).col_join(-8*U.T).col_join(sp.zeros(1,3))
    Bh=sp.diag(*list(B.diagonal()),0,0,0)
    t=sp.Rational(1,65536);A=Bh+t*F
    assert F*F==F and F.rank()==3
    assert F*Omega==sp.zeros(6,3)
    assert Omega.T*A*Omega==B
    assert A*Omega*(Omega.T*A*Omega).inv()*Omega.T*A==Bh
    assert A.det()>0
    D=sp.Matrix([[585,144,224],[144,585,-28],[224,-28,0]])/729
    v=sp.Matrix([4,3,1]);witness=(v.T*D*v)[0]/26
    assert witness==sp.Rational(19705,18954)
    lower=sp.Rational(64,65)*witness-sp.Rational(12800,81)*t
    assert lower==1+sp.Rational(334583,15769728)>1
    am,bhm,om=to_mp(A),to_mp(Bh),to_mp(Omega)
    delta=cap_matrix(am)-cap_matrix(bhm)
    ev=mp.eigsy(am,eigvals_only=True)
    tm=mp.mpf(1)/65536
    assert abs(ev[2]-tm)<mp.mpf('1e-65') and ev[0]>0
    ratio=max(abs(x) for x in mp.eigsy(delta,eigvals_only=True))/tm
    assert ratio>mp.mpf(str(lower.p))/int(lower.q)
    ny=am*om*(om.T*am*om)**-1*om.T*am
    assert mp.norm(ny-bhm)<mp.mpf('1e-65')
    # A fixed smooth, strictly concave replacement of the capped function.
    smooth_delta=sp.Rational(1,2**24)
    smooth_bound=(lower-smooth_delta/t)/(1+smooth_delta/(2*t))
    assert smooth_bound>1
    def smooth(x):
        d=mp.mpf(1)/2**24
        return (x+mp.sqrt(1+d*d)-mp.sqrt((x-1)**2+d*d))/2
    def smooth_matrix(X):
        eig,Q=mp.eigsy(X)
        return Q*mp.diag([smooth(x) for x in eig])*Q.T
    smooth_error=smooth_matrix(am)-smooth_matrix(bhm)
    smooth_ratio=max(abs(x) for x in mp.eigsy(smooth_error,eigvals_only=True))/smooth(tm)
    assert smooth_ratio>mp.mpf(str(smooth_bound.p))/int(smooth_bound.q)
    return {'status':'PASS','dimension':6,'rank':3,'target_positive_definite':True,
            'exact_nystrom_identity':True,'projection_identity':True,
            'rational_target_determinant':str(A.det()),'t':str(t),
            'rigorous_spectral_ratio_lower_bound':str(lower),
            'numerical_spectral_ratio':mp.nstr(ratio,40),
            'smallest_target_eigenvalue':mp.nstr(ev[0],30),
            'smooth_parameter':str(smooth_delta),
            'rigorous_smooth_spectral_ratio_lower_bound':str(smooth_bound),
            'numerical_smooth_spectral_ratio':mp.nstr(smooth_ratio,40),
            'target_matrix_rational':[[str(A[i,j]) for j in range(6)] for i in range(6)],
            'sketch_matrix_rational':[[str(Omega[i,j]) for j in range(3)] for i in range(6)]}

def nuclear_examples() -> dict:
    records=[]
    for m in [1,2,4,8,16]:
        d=2*m
        h=[mp.mpf(1)/4**i for i in range(1,m+1)]
        B=mp.diag([1-x for x in h]+[1+x for x in h])
        u=mp.ones(d,1)/mp.sqrt(d)
        K=mp.matrix([[h[i]/(h[i]+h[j]) for j in range(m)] for i in range(m)])
        D=mp.zeros(d)
        for i in range(m):
            for j in range(m):
                D[i,j]=mp.mpf(1)/d
                D[i,j+m]=K[i,j]/d;D[j+m,i]=K[i,j]/d
        for eta in [mp.mpf(1)/4,mp.mpf(1)/100]:
            Bh=mp.zeros(d+1);Bh[:d,:d]=B
            v=mp.matrix([mp.sqrt(eta)*u[i] for i in range(d)]+[mp.sqrt(1-eta)])
            Omega=mp.zeros(d+1,d)
            for i in range(d):
                Omega[i,i]=1;Omega[d,i]=-mp.sqrt(eta/(1-eta))*u[i]
            t=h[-1]/2**20
            A=Bh+t*v*v.T
            assert mp.norm(v.T*Omega)<mp.mpf('1e-70')
            assert mp.norm(Omega.T*A*Omega-B)<mp.mpf('1e-68')
            ny=A*Omega*(Omega.T*A*Omega)**-1*Omega.T*A
            assert mp.norm(ny-Bh)<mp.mpf('1e-65')
            eig=mp.eigsy(A,eigvals_only=True);tail=eig[0]
            assert 0<tail<t and eig[1]>=mp.mpf(3)/4
            assert abs(tail-(1-eta)*t)<=2*t*t*eta*(1-eta)
            err=nuclear(cap_matrix(A)-cap_matrix(Bh))
            epsA=t/tail-1;epsF=err/tail-1;ratio=epsF/epsA
            # The limiting lower bound has a strict or non-strict slack because
            # pinching discards potentially helpful off-diagonal blocks.
            assert ratio>=nuclear(D)-mp.mpf('0.0001')
            records.append({'m':m,'eta':mp.nstr(eta,15),'t':mp.nstr(t,20),
                            'input_nuclear_relative_excess':mp.nstr(epsA,30),
                            'output_nuclear_relative_excess':mp.nstr(epsF,30),
                            'excess_ratio':mp.nstr(ratio,30),
                            'derivative_lower_bound_for_limit':mp.nstr(nuclear(D),30)})
    return {'status':'PASS','finite_nystrom_cases':len(records),'records':records,
            'scope':'Finite numerical checks illustrate, but do not establish, the unbounded family theorem.'}

def main():
    result={'status':'PASS','mpmath_decimal_precision':mp.mp.dps,
            'spectral_nystrom':spectral_example(),'nuclear_nystrom':nuclear_examples()}
    (ROOT/'results'/'nystrom_counterexample_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
