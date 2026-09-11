#!/usr/bin/env python3
"""Exact algebra checks for the PF-05 proof. Not a substitute for its proof."""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp


def main() -> None:
    a, b, c, d, e, f = sp.symbols('a b c d e f', real=True)
    alpha, beta, gamma, t, u = sp.symbols('alpha beta gamma t u', real=True)
    X = sp.Matrix([[a,b],[b,c]])
    Y = sp.Matrix([[d,e],[e,f]])
    E11 = sp.diag(1,0)
    s = gamma**2
    sigma = s-1
    LX = sp.Matrix([[a+alpha*b+beta*c,gamma*b],[gamma*b,c]])
    LinvstarY = sp.Matrix([[d,(e-alpha*d/2)/gamma],[(e-alpha*d/2)/gamma,f-beta*d]])
    TX = (-sigma*a+alpha*b+beta*c)*E11
    negTstarY = d*sp.Matrix([[sigma,-alpha/2],[-alpha/2,-beta]])
    checks: dict[str, bool] = {}
    checks['trace_invariance_of_canonical_map'] = sp.simplify(sp.trace(LX*LinvstarY)-sp.trace(X*Y)) == 0
    checks['first_order_trace_cancellation'] = sp.simplify(sp.trace(TX*Y)+sp.trace(X*negTstarY)) == 0
    checks['rank_one_primal_determinant'] = sp.simplify((LX.det()-c*TX[0,0]).subs(a,b*b/c)) == 0
    g = s*(u*u-beta)-(u-alpha/2)**2
    Q = sigma*u*u+alpha*u-beta
    checks['dual_nonnegative_identity'] = sp.expand(s*Q-g-(sigma*u+alpha/2)**2) == 0
    B = d*sp.Matrix([[1,u],[u,u*u]])
    F = d*sp.Matrix([[sigma,-alpha/2],[-alpha/2,-beta]])
    checks['dual_line_determinant'] = sp.expand((B+t*F).det()-d*d*(t*Q+t*t*(-sigma*beta-alpha*alpha/4))) == 0
    checks['flat_dual_is_eigenvector'] = sp.simplify(F.subs({alpha:-2*sigma*u,beta:-sigma*u*u})-sigma*B) == sp.zeros(2)

    # A fully exact example with a nontrivial zero and rational alternative factors.
    av,bv,gv = sp.Rational(1,5), sp.Rational(1,10),sp.Rational(11,10)
    As = [sp.diag(1,0),sp.eye(2),sp.Matrix([[2,sp.Rational(1,3)],[sp.Rational(1,3),1]])]
    Bs = [sp.diag(0,1),sp.eye(2),sp.Matrix([[1,sp.Rational(1,4)],[sp.Rational(1,4),2]])]
    def subst(mat: sp.Matrix, x: sp.Matrix, primal: bool) -> sp.Matrix:
        vals = {alpha:av,beta:bv,gamma:gv}
        vals.update(dict(zip((a,b,c) if primal else (d,e,f),(x[0,0],x[0,1],x[1,1]))))
        return mat.subs(vals)
    A2 = [subst(LX,A,True) for A in As]
    B2 = [subst(LinvstarY,B,False) for B in Bs]
    def psd(Z: sp.Matrix) -> bool:
        return bool(Z[0,0]>=0 and Z[1,1]>=0 and Z.det()>=0)
    M = sp.Matrix([[sp.trace(A*B) for B in Bs] for A in As])
    M2 = sp.Matrix([[sp.trace(A*B) for B in B2] for A in A2])
    checks['exact_example_has_rank_three'] = M.rank()==3
    checks['exact_example_has_a_zero'] = M[0,0]==0
    checks['exact_alternative_factors_are_psd'] = all(psd(Z) for Z in A2+B2)
    checks['exact_alternative_preserves_matrix'] = M==M2
    Es = [subst(TX,A,True) for A in As]
    Fs = [subst(negTstarY,B,False) for B in Bs]
    h = sp.Rational(1,100)
    checks['exact_example_linear_factors_psd_at_h'] = all(psd(A+h*E) for A,E in zip(As,Es)) and all(psd(B+h*F) for B,F in zip(Bs,Fs))
    # PSD at 0 and h implies PSD on the whole intervening segment by convexity.
    for name,ok in checks.items():
        print(('PASS' if ok else 'FAIL')+' '+name)
    output = {'checks':checks,'passed':sum(checks.values()),'total':len(checks),'matrix_example':str(M),'sympy_version':sp.__version__}
    out = Path(__file__).resolve().parents[1]/'results'/'pf05_verification.json'
    out.write_text(json.dumps(output,indent=2)+'\n')
    if not all(checks.values()):
        raise AssertionError('A PF-05 verification check failed')

if __name__ == '__main__':
    main()
