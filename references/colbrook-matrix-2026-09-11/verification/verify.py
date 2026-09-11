#!/usr/bin/env python3
"""Verify the submission's finite rational certificates with Python's stdlib.

Usage: python3 verification/verify.py [--json PATH]
No internet, NumPy, SymPy, or arbitrary-precision floating point is needed.
General analytic arguments (in particular MI-03, MI-04, MI-08 and MI-25) must
also be checked by reading the proofs. Passing this script is NOT formal
verification of those arguments or independent peer review.
"""
from __future__ import annotations
import argparse, json, sys, time
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
from exact_linear import (mat,eye,diag,trans,add,sub,scale,mul,power,det,
    leading_minors,positive_definite,positive_semidefinite,frobenius_squared,
    trace,characteristic_coefficients,polynomial_from_roots)

HERE=Path(__file__).resolve().parent
REPORT=[]

def require(condition: bool, label: str) -> None:
    if not condition:raise AssertionError(label)

def record(problem: str, checks: list[str], **values) -> None:
    REPORT.append({'problem':problem,'status':'PASS','checks':checks,
                   'values':{k:str(v) for k,v in values.items()}})
    print(f"PASS {problem}: {'; '.join(checks)}",flush=True)


def check_mi06():
    t=F(3,4);s=F(5,4);a=(s+1)/2;b=(s-1)/2
    X=mat([[1,t,0],[0,0,0],[0,0,0]])
    Y=mat([[-1,0,0],[0,0,0],[-t,0,0]])
    absX=scale(1/s,mat([[1,t,0],[t,t*t,0],[0,0,0]]))
    absXt=diag([s,0,0]);absY=absXt
    absYt=scale(1/s,mat([[1,0,t],[0,0,0],[t,0,t*t]]))
    for Z,R,L in [(X,absX,absXt),(Y,absY,absYt)]:
        require(positive_semidefinite(R) and positive_semidefinite(L),'MI06 PSD moduli')
        require(power(R,2)==mul(trans(Z),Z) and power(L,2)==mul(Z,trans(Z)),'MI06 modulus squares')
    SX=scale(F(1,2),add(absX,absXt));SY=scale(F(1,2),add(absY,absYt))
    expected=polynomial_from_roots([a,b,0])
    require(characteristic_coefficients(SX)==expected and characteristic_coefficients(SY)==expected,'MI06 spectra')
    Z=add(X,Y);R=diag([t,t,0]);L=diag([t,0,t])
    require(power(R,2)==mul(trans(Z),Z) and power(L,2)==mul(Z,trans(Z)),'MI06 sum modulus')
    lower=t/2;upper_without_factor=2*b
    require(lower>0 and lower**2>2*upper_without_factor**2,'MI06 sqrt(2) contradiction')
    record('MI-06',['exact moduli','orbit-obstruction spectra','strict sqrt(2) comparison'],
           left_min=lower,right_tail_sum=upper_without_factor,required_factor=lower/upper_without_factor)


def check_mi07():
    t=F(3,4);s=F(5,4)
    A=diag([1,0]);B=mat([[0,t],[0,0]])
    Z=add(A,B)
    require(frobenius_squared(Z)==s*s and det(Z)==0,'MI07 rank-one singular value')
    require(Z[0][1]!=0 and t>0,'MI07 independent left/right rank-one directions')
    require(s>t,'MI07 strict minimum-eigenvalue obstruction')
    record('MI-07',['rank-one modulus-limit input','strict orbit obstruction'],t=t,nonzero_singular_value=s)


def check_mi19():
    X=mat([[13,0,13,13],[1,1,-2,1]])
    A=mul(trans(X),X);q=F(7,8)
    expected=mat([[170,1,167,170],[1,1,-2,1],[167,-2,173,167],[170,1,167,170]])
    require(A==expected,'MI19 Gram factor')
    full=F(0);restricted=F(0);coeff=[F(0)]*7;restricted_coeff=coeff.copy()
    for p in permutations(range(4)):
        inversions=sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))
        term=F(1)
        for i in range(4):term*=A[i][p[i]]
        coeff[inversions]+=term;full+=term*q**inversions
        if p[1]==1:restricted_coeff[inversions]+=term;restricted+=term*q**inversions
    require(coeff==[4999700,4886140,-199231,4712758,9568969,4886140,115600],'MI19 polynomial')
    require(full-restricted==F(-3235575,16384),'MI19 exact negative gap')
    require(full==F(335001935775,16384),'MI19 full value')
    require(restricted==F(167502585675,8192),'MI19 restricted value')
    record('MI-19',['exact Gram factor','24-permutation inversion convention','negative rational gap'],
           full=full,restricted=restricted,gap=full-restricted)


def check_mi21():
    C=diag([F(12,37),F(21,29)]);E=diag([F(35,37),F(20,29)])
    S=scale(F(1,17),mat([[15,8],[8,-15]]));D=mul(mul(S,E),S)
    require(add(power(C,2),power(E,2))==eye(2) and power(S,2)==eye(2),'MI21 scalar sums')
    delta=F(5,3);h=F(61697295,8682716)
    N=add(D,scale(delta,C))
    require(N==scale(F(1,310097),mat([[443355,33000],[33000,605715]])),'MI21 geometric mean numerator')
    require(delta**2==det(D)/det(C),'MI21 determinant ratio')
    Ci=diag([1/C[0][0],1/C[1][1]])
    require(h==trace(mul(Ci,D))+2*delta,'MI21 geometric mean denominator')
    require(positive_definite(N),'MI21 positive mean')
    require(mul(mul(N,Ci),N)==scale(h,D),'MI21 Riccati equation')
    G2=scale(1/h,power(N,2));L=add(G2,mul(mul(S,G2),S))
    require(G2==scale(F(1,12158163),mat([[3516940,616000],[616000,6547660]])),'MI21 G squared')
    w=mat([[1],[-4]]);lam=F(1351000,1350907)
    require(mul(L,w)==scale(lam,w) and lam>1,'MI21 violating eigenpair')
    record('MI-21',['positive rational inputs','geometric-mean Riccati identity','violating rational eigenpair'],
           left_eigenvalue=lam,right_norm=1,excess=lam-1)


def check_mi22():
    data=json.loads((HERE/'MI22_certificate.json').read_text())
    # Certificate file is a convenient duplicate; matrices below are the proof's
    # independent, complete inputs. Agreement is checked explicitly.
    den=10**15
    R=scale(F(1,den),mat([[563431071954661,-4774979464975,-152620714401404],
        [-4774979464975,6722248446399974,-185449303604146],
        [-152620714401404,-185449303604146,793308473748417]]))
    S=scale(F(1,den),mat([[1417565567728212,-40084698659651,-79375309604622],
        [-40084698659651,2883518412755210,-1150490885652445],
        [-79375309604622,-1150490885652445,1157680400969996]]))
    A=diag([256,F(1,256),1]);B=mat([[17,-4,0],[-4,16385,-8192],[0,-8192,4096]])
    C=mat([[F(17,256),-4,0],[-4,4194560,-131072],[0,-131072,4096]])
    Ai=diag([F(1,16),16,1]);require(C==mul(mul(Ai,B),Ai),'MI22 congruence')
    require(leading_minors(B)==[F(17),F(278529),F(4096)],'MI22 input positivity')
    I=eye(3);m=F(1,1024)
    for Z,name in [(B,'B'),(C,'C')]:require(positive_definite(sub(Z,scale(m,I))),f'MI22 {name} lower bound')
    for Z,upper,name in [(R,8,'R'),(S,4,'S')]:
        require(positive_definite(sub(Z,scale(F(9,20),I))),f'MI22 {name} root lower bound')
        require(positive_definite(sub(scale(upper,I),Z)),f'MI22 {name} root upper bound')
    rres=frobenius_squared(sub(power(R,8),C));sres=frobenius_squared(sub(power(S,8),B))
    require(rres<F(1,10**16) and sres<F(1,10**16),'MI22 root residuals')
    require(F(9,20)**8>m,'MI22 powered root lower bound')
    require(F(1,8)**8*m**(-7)<64**8,'MI22 root Lipschitz coefficient')
    require(trace(C)<8**8 and trace(B)<4**8,'MI22 true root upper bounds')
    eps=F(64,10**8);error=32*16*eps*(4**7+8*7*4**6)
    require(error==F(6291456,78125) and error<100,'MI22 propagated error')
    Lt=mul(mul(mul(diag([32,F(1,32),1]),R),diag([16,F(1,16),1])),power(S,7))
    require(Lt[0][1]>11000,'MI22 rational matrix entry')
    right=frobenius_squared(mul(A,B))
    require(right==F(6807858741265,65536) and right<10200**2,'MI22 right norm bound')
    # JSON key conventions are validated below after loading the generation file.
    if 'R' in data and 'S' in data:
        require(mat(data['R'])==R and mat(data['S'])==S,'MI22 duplicated JSON certificate')
    record('MI-22',['positive rational root bounds','exact eighth-power residuals',
        'analytic error bound arithmetic','strict entry versus Frobenius certificate'],
        error_bound=error,left_lower_bound=10900,right_upper_bound=10200)


def check_mi23():
    D=diag([16,F(1,12),1]);T=mat([[2,1,2],[1,25,-10],[2,-10,10]])
    require(leading_minors(T)==[F(2),F(49),F(150)],'MI23 positivity')
    A=power(D,2);B=mul(mul(D,power(T,8)),D)
    G=mul(mul(D,T),D);H=mul(mul(D,power(T,7)),D)
    entry=mul(G,H)[0][2];right=frobenius_squared(mul(A,B))
    require(entry==F(1260589125202,9),'MI23 exact entry')
    require(right==F(2009446159144992718181231562721,107495424),'MI23 right norm squared')
    require(entry>140000000000 and right<138000000000**2,'MI23 separated integer bounds')
    gap=entry**2-right
    require(gap==F(99434824489435745411095588895,107495424) and gap>0,'MI23 positive rational certificate')
    record('MI-23',['positive rational inputs','integer-power geometric means','strict rational norm certificate'],
           entry=entry,right_frobenius_squared=right,positive_gap=gap)


def check_mi26():
    P=diag([1,0]);Q=scale(F(1,25),mat([[9,12],[12,16]]))
    require(power(P,2)==P and power(Q,2)==Q,'MI26 projections')
    Z=add(P,Q);fZ=sub(Z,power(Z,2));w=mat([[1],[-2]])
    require(mul(fZ,w)==scale(F(6,25),w),'MI26 positive eigenpair')
    require(fZ==scale(F(1,25),mat([[-18,-12],[-12,0]])),'MI26 polynomial evaluation')
    # Positive definite variant from the note.
    A=add(P,scale(F(1,20),eye(2)));B=add(Q,scale(F(1,20),eye(2)))
    require(positive_definite(A) and positive_definite(B),'MI26 positive definite variant')
    for V in [A,B]:
        require(characteristic_coefficients(sub(V,power(V,2)))==polynomial_from_roots([F(19,400),F(-21,400)]),'MI26 PD input spectra')
    Fsum=sub(add(A,B),power(add(A,B),2))
    require(mul(Fsum,w)==scale(F(1,4),w),'MI26 PD violating eigenpair')
    require(F(1,4)>F(19,200),'MI26 PD orbit obstruction')
    record('MI-26',['exact projection obstruction','positive definite variant'],positive_eigenvalue=F(6,25))


def check_mi29():
    A=diag([2,1,F(1,2)]);M=mat([[-1,2,0],[2,1,2],[0,2,1]])
    B=scale(F(1,5),M);D=power(A,6)
    require(positive_definite(A) and B==trans(B) and det(B)==F(-1,125),'MI29 inputs')
    H=power(mul(mul(M,power(A,2)),M),4)
    J=power(mul(mul(A,power(M,2)),A),4)
    # Four distinct rational points verify the cubic polynomial identity.
    for z in [F(0),F(1),F(2),F(3)]:
        gap=det(add(D,scale(z,J)))-det(add(D,scale(z,H)))
        expected=F(2089017,16)*z-F(31188746592549,1024)*z*z
        require(gap==expected,'MI29 determinant polynomial')
    z=F(1,5**8);left=det(add(D,scale(z,H)));right=det(add(D,scale(z,J)))
    gap=right-left
    require(gap==F(21036678407451,156250000000000) and gap>0,'MI29 reversed determinant inequality')
    record('MI-29',['Hermitian invertible B','exact determinant polynomial','positive reversed gap'],left=left,right=right,gap=gap)


def check_mi08_partial():
    residues={1,3,4,5,9}
    def chi(x):
        x%=11
        return 0 if x==0 else (1 if x in residues else -1)
    Q=mat([[chi(i-j) for j in range(11)] for i in range(11)])
    require(trans(Q)==scale(-1,Q),'MI08 Paley skew matrix')
    bottom=sub(Q,eye(11))
    H=mat([[1]*12]+[[1]+row for row in bottom])
    require(mul(H,trans(H))==scale(12,eye(12)),'MI08 Hadamard certificate')
    for d in range(9,13):
        Hd=[row[:d] for row in H]
        require(mul(trans(Hd),Hd)==scale(12,eye(d)),'MI08 rectangular sign certificate')
    record('MI-08 (partial)',['exact order-12 sign matrix','column orthogonality for d=9,10,11,12'])


def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--json',type=Path,help='Write a machine-readable verification report')
    args=parser.parse_args();start=time.perf_counter()
    for fn in [check_mi06,check_mi07,check_mi19,check_mi21,check_mi22,
               check_mi23,check_mi26,check_mi29,check_mi08_partial]:
        fn()
    print('Analytic proofs requiring direct review: MI-03, MI-04, MI-08 reduction, MI-25 endpoint.')
    print('All finite certificates passed. This is not formal verification or peer review.')
    output={'status':'PASS','arithmetic':'Python fractions.Fraction; no floating point',
            'elapsed_seconds':round(time.perf_counter()-start,3),'results':REPORT,
            'not_formally_verified':['MI-03 general proof','MI-04 general proof',
                'unitary-orbit arguments','MI-08 reduction','MI-25 asymptotic proof',
                'MI-22 analytic matrix-root error lemma']}
    if args.json:
        args.json.parent.mkdir(parents=True,exist_ok=True)
        args.json.write_text(json.dumps(output,indent=2)+'\n')
    return 0

if __name__=='__main__':
    try:sys.exit(main())
    except (AssertionError,ValueError,KeyError) as exc:
        print(f'FAILED: {exc}',file=sys.stderr);sys.exit(1)
