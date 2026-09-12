#!/usr/bin/env python3
"""Exact algebra diagnostics from the prior proof pack; not a formal proof."""
import random
import sympy as sp

def check_sp03():
    rng=random.Random(7303)
    tested=0
    for m in (1,2,3):
        I=sp.eye(m);Z=sp.zeros(m)
        J=Z.row_join(I).col_join((-I).row_join(Z))
        for _ in range(4):
            B=sp.Matrix(m,m,lambda i,j:rng.randrange(-2,3));B=B+B.T
            C=sp.Matrix(m,m,lambda i,j:rng.randrange(-2,3));C=C+C.T
            X=I.row_join(B).col_join(Z.row_join(I))*I.row_join(Z).col_join(C.row_join(I))
            W=sp.Matrix(2*m,2*m,lambda i,j:sp.Rational(rng.randrange(-2,3),100))
            K=W-W.T;Q=sp.eye(2*m)+K*K
            assert X.T*J*X==J and Q.det()!=0
            U=X+J*X*K;G=U.T*U;R=U.T*J*U
            assert R+G*K+K*G-K*R*K-Q*J*Q==sp.zeros(2*m)
            assert (U-J*U*K)*Q.inv()==X
            assert (J*X).inv()*(U-X)==K
            tested+=1
    t=sp.symbols('t');f=t**4-8*t**2-13*t-5
    assert sp.discriminant(f,t)==-16075
    assert f.subs(t,1)==-25 and f.subs(t,-1)==1
    print(f'PASS: SP-03 exact rational identities in {tested} examples, m=1,2,3; quartic discriminant and exceptional values.')


if __name__=="__main__": check_sp03()
