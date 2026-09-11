#!/usr/bin/env python3
"""Exact certificate checks for the PF-02 disconnected-orbit counterexample."""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp


def coords(A: sp.Matrix) -> list:
    return [A[0,0],A[1,1],A[2,2],A[0,1],A[0,2],A[1,2]]

def main() -> None:
    I=sp.eye(3)
    As=[]
    for i in range(3):
        A=2*I; A[i,i]+=2; As.append(A)
    for i,j in [(0,1),(0,2),(1,2)]:
        A=2*I; A[i,j]=A[j,i]=1; As.append(A)
    At=[A.copy() for A in As]
    At[3][0,1]=At[3][1,0]=-1
    M=sp.Matrix([[sp.trace(A*B) for B in As] for A in As])
    Mt=sp.Matrix([[sp.trace(A*B) for B in At] for A in At])
    U=sp.Matrix([coords(A) for A in As]); Ut=sp.Matrix([coords(A) for A in At])
    checks={
        'all_factors_positive_definite':all(all(A[:i,:i].det()>0 for i in range(1,4)) for A in As+At),
        'both_gram_factorizations_equal':M==Mt,
        'matrix_entries_are_positive_integers':all(x>0 and x.is_Integer for x in M),
        'ordinary_rank_is_six':M.rank()==6,
        'matrix_determinant_is_8192':M.det()==8192,
        'first_orientation_determinant_is_32':U.det()==32,
        'second_orientation_determinant_is_minus_32':Ut.det()==-32,
    }
    # Exact samples check the congruence representation formula. The manuscript
    # proves it for every invertible S, rather than relying on these samples.
    basis=[]
    for i in range(3):
        E=sp.zeros(3);E[i,i]=1;basis.append(E)
    for i,j in [(0,1),(0,2),(1,2)]:
        E=sp.zeros(3);E[i,j]=E[j,i]=1;basis.append(E)
    samples=[sp.diag(-1,1,1),sp.Matrix([[1,2,0],[0,1,1],[1,0,1]]),sp.Matrix([[2,1,0],[1,3,1],[0,1,2]])]
    for k,S in enumerate(samples):
        R=sp.Matrix.hstack(*(sp.Matrix(coords(S.T*E*S)) for E in basis))
        checks[f'congruence_determinant_sample_{k}']=R.det()==S.det()**4
    block_cases = []
    for size in range(4,8):
        r=size-3
        Fs=[]
        for A in As:
            F=sp.zeros(size); F[:3,:3]=A; Fs.append(F)
        for i in range(r):
            F=sp.zeros(size); F[3:,3:]=2*sp.eye(r)
            F[3+i,3+i]+=2; Fs.append(F)
        for i in range(r):
            for j in range(i+1,r):
                F=sp.zeros(size); F[3:,3:]=2*sp.eye(r)
                F[3+i,3+j]=F[3+j,3+i]=1; Fs.append(F)
        for i in range(3):
            for j in range(3,size):
                F=2*sp.eye(size); F[i,j]=F[j,i]=1; Fs.append(F)
        def allcoords(F):
            return [F[i,i] for i in range(size)]+[F[i,j] for i in range(size) for j in range(i+1,size)]
        dim=size*(size+1)//2; d=r*(r+1)//2
        C=sp.Matrix([allcoords(F) for F in Fs])
        K=sp.Matrix([[sp.trace(A*B) for B in Fs] for A in Fs])
        reflected=[]
        for F in Fs:
            R=F.copy(); R[0,1]=-R[0,1];R[1,0]=-R[1,0];reflected.append(R)
        Kr=sp.Matrix([[sp.trace(A*B) for B in reflected] for A in reflected])
        Q=sum(Fs[6:6+d],sp.zeros(size))
        checks[f'block_size_{size}_full_coordinate_rank']=len(Fs)==dim and C.rank()==dim
        checks[f'block_size_{size}_full_gram_rank']=K.rank()==dim
        checks[f'block_size_{size}_leading_block_rank']=K[:6,:6].rank()==6
        checks[f'block_size_{size}_trailing_block_rank']=K[6:6+d,6:6+d].rank()==d
        checks[f'block_size_{size}_zero_cross_entries']=K[:6,6:6+d]==sp.zeros(6,d)
        checks[f'block_size_{size}_bottom_support_rank']=Q.rank()==r
        checks[f'block_size_{size}_reflection_preserves_gram']=K==Kr
        checks[f'block_size_{size}_all_factors_psd']=all(F.is_positive_semidefinite is True for F in Fs+reflected)
        # These checks concern the explicit perturbation only. They do NOT give
        # the uniform eta_0 in the compactness theorem about all factorizations.
        eta=sp.Rational(1,100)
        perturbed=[F+eta*sp.eye(size) for F in Fs]
        ref_perturbed=[F+eta*sp.eye(size) for F in reflected]
        KP=sp.Matrix([[sp.trace(A*B) for B in perturbed] for A in perturbed])
        KRP=sp.Matrix([[sp.trace(A*B) for B in ref_perturbed] for A in ref_perturbed])
        checks[f'block_size_{size}_perturbation_pd']=all(F.is_positive_definite is True for F in perturbed+ref_perturbed)
        checks[f'block_size_{size}_perturbation_positive_full_rank']=all(x>0 for x in KP) and KP.rank()==dim
        checks[f'block_size_{size}_perturbation_equal_gram']=KP==KRP
        block_cases.append({'factor_size':size,'matrix_order':dim,'coordinate_determinant':str(C.det()),'reflection_coordinate_determinant':str(sp.Matrix([allcoords(F) for F in reflected]).det()),'perturbation_test_eta':'1/100','note':'This eta only tests positivity, full rank and equality of the explicit Gram factorizations; no numerical component-separation threshold is certified.'})
    out={
        'checks':checks,'passed':sum(checks.values()),'total':len(checks),
        'all_size_block_cases':block_cases,
        'M':[[int(x) for x in M.row(i)] for i in range(6)],
        'factors_A_equal_B':[[[int(x) for x in A.row(i)] for i in range(3)] for A in As],
        'alternative_factors_A_equal_B':[[[int(x) for x in A.row(i)] for i in range(3)] for A in At],
        'conclusion':'Real psd rank is 3 by the rank-dimension bound and the explicit factors. The continuous congruence-invariant orientation takes both signs, so the orbit quotient is disconnected.'
    }
    p=Path(__file__).resolve().parents[1]/'results'/'pf02_verification.json'
    p.write_text(json.dumps(out,indent=2)+'\n')
    print(M)
    for name,ok in checks.items():print(('PASS' if ok else 'FAIL')+' '+name)
    assert all(checks.values())

if __name__=='__main__':main()
