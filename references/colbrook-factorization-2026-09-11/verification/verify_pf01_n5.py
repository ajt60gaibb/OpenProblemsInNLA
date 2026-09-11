#!/usr/bin/env python3
"""Exact arithmetic checks for PF-01, n=5 (not the general family)."""
from __future__ import annotations
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path
import json
import sympy as sp


def main() -> None:
    checks: dict[str, bool] = {}
    pairs=list(combinations(range(5),2))
    E=sp.Matrix([[int(i in I) for i in range(5)] for I in pairs])
    D=sp.Matrix([[2-len(set(I)&set(J)) for J in pairs] for I in pairs])
    checks['incidence_rank_five']=E.rank()==5
    checks['ordinary_rank_five']=D.rank()==5
    checks['ordinary_rank_factorization']=D==E*(sp.ones(5)/2-sp.eye(5))*E.T

    helmert=sp.zeros(4,5)
    for r in range(1,5):
        for i in range(r):helmert[r-1,i]=1/sp.sqrt(r*(r+1))
        helmert[r-1,r]=-r/sp.sqrt(r*(r+1))
    checks['helmert_rows_orthonormal']=sp.simplify(helmert*helmert.T)==sp.eye(4)
    checks['helmert_projection']=sp.simplify(helmert.T*helmert)==sp.eye(5)-sp.ones(5)/5
    As=[];Bs=[];Zs=[]
    for I in pairs:
        y=helmert*sp.Matrix([int(i in I) for i in range(5)])/sp.sqrt(2)
        Z=sp.Matrix([[y[0],y[1]],[y[2],y[3]]]);Zs.append(Z)
        C=Z.col_join(sp.eye(2));F=sp.eye(2).col_join(-Z.T)
        As.append(C*C.T);Bs.append(F*F.T)
    checks['all_twenty_factors_rank_two']=all(A.rank()==2 for A in As+Bs)
    factor_entries=[]
    for i in range(10):
        for j in range(10):
            val=sp.simplify(sp.trace(As[i]*Bs[j]))
            checks[f'upper_factor_entry_{i}_{j}']=val==D[i,j]
    checks['entrywise_nonnegative_input']=all(t>=0 for t in D)
    checks['zero_diagonal_strictly_positive_elsewhere']=all(D[i,j]>0 if i!=j else D[i,j]==0 for i in range(10) for j in range(10))

    x=sp.symbols('x1:6');a=sp.symbols('a1:6');lam=sp.symbols('lambda')
    e3=sum(sp.prod(x[i] for i in I) for I in combinations(range(5),3))
    q=2*sum(t*t for t in x)-sum(x)**2
    p=lam*e3+q*sum(ai*xi for ai,xi in zip(a,x))
    H=sp.hessian(p,x)
    pt={x[i]:int(i in(0,1)) for i in range(5)}
    s=a[0]+a[1]
    determinant_identity=-96*s*(2*s-lam)**2*(4*s-lam)**2
    checks['unspecialized_hessian_determinant_identity']=sp.expand(H.subs(pt).det(method='domain-ge')-determinant_identity)==0
    grad=[sp.diff(p,xi).subs(pt) for xi in x]
    checks['unspecialized_gradient_pattern']=all(sp.expand(grad[i]-(0 if i<2 else lam-4*s))==0 for i in range(5))
    # Check the dimension of the gradient-pattern cubic space independently.
    monomials=[sp.prod(x[i] for i in I) for I in combinations_with_replacement(range(5),3)]
    coeffs=sp.symbols('c:'+str(len(monomials)))
    general=sum(c*m for c,m in zip(coeffs,monomials));eq=[]
    for i,j in pairs:
        pp={x[k]:int(k in(i,j)) for k in range(5)}
        gg=[sp.diff(general,xi).subs(pp) for xi in x]
        other=[k for k in range(5) if k not in(i,j)]
        eq.extend([gg[i],gg[j],gg[other[1]]-gg[other[0]],gg[other[2]]-gg[other[0]]])
    constraint,_=sp.linear_eq_to_matrix(eq,coeffs)
    checks['cubic_constraint_rank_29']=constraint.rank()==29
    basis=[e3]+[q*xi for xi in x]
    coefficient_basis=sp.Matrix([[sp.Poly(b,*x).coeff_monomial(m) for b in basis] for m in monomials])
    checks['six_cubic_generators_independent']=coefficient_basis.rank()==6
    checks['six_cubic_generators_span_constraint_kernel']=constraint*coefficient_basis==sp.zeros(40,6)

    z=sp.symbols('z:6');alpha,beta=sp.symbols('alpha beta',nonzero=True)
    S=sp.Matrix([[z[0],z[3],z[4]],[z[3],z[1],z[5]],[z[4],z[5],z[2]]])
    fullH=sp.hessian(S.det(),z)
    rank2=fullH.subs({z[0]:alpha,z[1]:beta,z[2]:0,z[3]:0,z[4]:0,z[5]:0})
    rank1=rank2.subs(beta,0)
    checks['determinant_hessian_rank_two_base_rank_four']=rank2.rank()==4
    checks['determinant_hessian_rank_one_base_rank_three']=rank1.rank()==3

    R=sp.Rational
    cases=[(1,[0]*5),(1,[R(1,8)]*5),(1,[R(1,4)]+[0]*4),(1,[-R(1,8)]+[R(1,8)]*4),(-1,[-R(1,4)]*5),(-1,[-R(1,8)]*5),(-1,[0]+[-R(1,4)]*4),(-1,[-R(3,8)]+[-R(1,8)]*4)]
    certificates=[]
    four_minor_cases={1:((0,1),(0,2,3,4),R(1,4)),2:((0,1),(0,2,3,4),sp.Integer(1)),3:((1,2),(0,1,3,4),R(9,4)),6:((0,1),(0,2,3,4),sp.Integer(-2)),7:((1,2),(0,1,3,4),R(1,4))}
    zero_cases={0:([1,1,1,1,-R(2,3)],R(256,3)),4:([1,1,1,0,5],sp.Integer(320))}
    for k,(lv,av) in enumerate(cases):
        sub={lam:lv,**dict(zip(a,av))};pc=sp.expand(p.subs(sub));HC=H.subs(sub)
        checks[f'case_{k+1}_allowed_pair_sums']=all(av[i]+av[j] in [0,R(lv,4),R(lv,2)] and lv-4*(av[i]+av[j])>=0 for i,j in pairs)
        record={'case':k+1,'lambda':lv,'a':[str(v) for v in av]}
        if k in four_minor_cases:
            ij,I,expected=four_minor_cases[k];point={x[i]:int(i in ij) for i in range(5)}
            gradient=sp.Matrix([sp.diff(pc,xi).subs(point) for xi in x])
            value=HC.subs(point).extract(I,I).det()
            checks[f'case_{k+1}_rank_one_forced']=gradient==sp.zeros(5,1) and av[ij[0]]+av[ij[1]]==R(lv,4)
            checks[f'case_{k+1}_nonzero_four_minor']=value==expected and value!=0
            record.update({'pair_one_based':[i+1 for i in ij],'principal_minor_indices_one_based':[i+1 for i in I],'minor':str(value)})
        elif k in zero_cases:
            w,expected=zero_cases[k];point=dict(zip(x,w));value=HC.subs(point).det()
            checks[f'case_{k+1}_polynomial_zero']=pc.subs(point)==0
            checks[f'case_{k+1}_nonzero_hessian_determinant']=value==expected and value!=0
            record.update({'zero_point':[str(v) for v in w],'hessian_determinant':str(value)})
        else:
            value=pc.subs(dict.fromkeys(x,1))
            checks[f'case_{k+1}_violates_positive_definite_sum']=value==-R(5,8)
            record['p_at_ones']=str(value)
        certificates.append(record)
    # This finite check supplements the all-real classification in the proof;
    # it does not replace that classification.
    positive_values=[-R(1,8),0,R(1,8),R(1,4)]
    negative_values=[-R(3,8),-R(1,4),-R(1,8),0]
    for lv,values in [(1,positive_values),(-1,negative_values)]:
        candidates=set()
        for av in product(values,repeat=5):
            if all(av[i]+av[j] in ([0,R(1,4)] if lv==1 else [-R(1,2),-R(1,4)]) for i,j in pairs):
                candidates.add(tuple(sorted(av)))
        expected={tuple(sorted(av)) for ll,av in cases if ll==lv}
        checks[f'finite_classification_check_lambda_{lv}']=candidates==expected
    out={'checks':checks,'passed':sum(checks.values()),'total':len(checks),'case_certificates':certificates,'D':[[int(v) for v in D.row(i)] for i in range(10)],'pairs_one_based':[[i+1 for i in I] for I in pairs],'factors_A':[[[str(sp.simplify(v)) for v in A.row(i)] for i in range(4)] for A in As],'factors_B':[[[str(sp.simplify(v)) for v in B.row(i)] for i in range(4)] for B in Bs],'scope':'Exact psd rank 4 for n=5 only. The general PF-01 family is not solved.'}
    path=Path(__file__).resolve().parents[1]/'results'/'pf01_n5_verification.json'
    path.write_text(json.dumps(out,indent=2)+'\n')
    for key,value in checks.items():print(('PASS ' if value else 'FAIL ')+key)
    print(f'{sum(checks.values())}/{len(checks)} checks passed')
    assert all(checks.values())

if __name__=='__main__':main()
