#!/usr/bin/env python3
"""Exact checks for the robust NM-03 reduction and simple-spectrum perturbation.

The universal approximation-gap argument is in the manuscript. These checks
validate its rational constants, perturbation selection and SAT witnesses;
no numerical optimizer is used to infer a lower bound.
"""
from __future__ import annotations
from itertools import combinations, product
from pathlib import Path
import json
import sympy as s
from verify_nm03 import encode, reduction, sqnorm

ROOT=Path(__file__).resolve().parents[1]

def main() -> None:
    checks: dict[str, bool] = {}
    records=[]
    for N in range(5,21):
        delta=s.Rational(1,12*N);epsilon=s.Rational(1,24*N*N)
        eta=epsilon/(9216*N**4)
        alpha=(1+delta)**2-1;beta=1-(1-epsilon)**2
        checks[f'gap_constants_N{N}']=bool(eta==s.Rational(1,221184*N**6) and
            0<eta<min(1,alpha,beta) and min(alpha,beta)>=epsilon and
            64*eta/epsilon==s.Rational(1,144*N**4))
        checks[f'rounding_margin_N{N}']=3*N*(delta+N*s.Rational(1,12*N*N))==s.Rational(1,2)
    cases=[(3,[(0,1,2)]),(4,list(combinations(range(4),3))),
           (5,[(0,1,2),(0,3,4)]),(5,list(combinations(range(5),3)))]
    z=s.Symbol('z')
    for n,clauses in cases:
        C=encode(n,clauses); X,tau,P=reduction(C); N=X.rows
        eta=s.Rational(1,221184*N**6); L=N*(N-1)+1
        D=s.diag(*range(1,N+1)); chosen=None
        for j in range(1,L+1):
            t=j*eta/(64*N*N*L); A=X+t*D
            p=A.charpoly(z).as_poly()
            if s.gcd(p,p.diff()).degree()==0:
                chosen=(j,t,A,p);break
        if chosen is None:
            raise AssertionError('Polynomial discriminant selection failed')
        j,t,A,p=chosen
        prefix=f'instance_{n}_{len(clauses)}'
        checks[prefix+'_simple_spectrum']=s.gcd(p,p.diff()).degree()==0
        checks[prefix+'_positive_symmetric_spd']=bool(A==A.T and min(A)>0 and
            all(A[:k,:k].det()>0 for k in range(1,N+1)))
        checks[prefix+'_perturbation_norm_bound']=bool(sqnorm(A-X)<=eta**2/(4096*N))
        checks[prefix+'_objective_bound_constant']=bool(5*eta/64<eta/8)
        sat=[bits for bits in product((0,1),repeat=n) if all(sum(bits[i] for i in c)==1 for c in clauses)]
        witness_errors=[]
        for bits in sat:
            chi=s.Matrix(bits+(1,0));k=sum(chi);one=s.ones(N,1)
            centered=chi-s.Rational(k,N)*one
            Y=(1+s.Rational(1,12*N))/N*s.ones(N)+centered*centered.T/s.Rational(k*(N-k),N)
            error=sqnorm(A-Y)
            assert min(Y)>0 and Y.rank()==2 and error<tau+eta/8
            witness_errors.append(str(error-tau))
        checks[prefix+'_explicit_sat_witnesses']=all(s.Rational(x)<eta/8 for x in witness_errors)
        records.append({'n':n,'clauses':clauses,'satisfying_assignments':len(sat),
                        'selected_candidate':j,'candidate_count_bound':L,'t':str(t),
                        'gap_eta':str(eta),'perturbed_threshold':str(tau+eta/2),
                        'explicit_witness_error_minus_tau':witness_errors})
    assert all(checks.values())
    out={'checks':checks,'passed':sum(checks.values()),'total':len(checks),'instances':records,
         'scope':'Exact constants and finite perturbation checks; universal hardness and error gap follow from the manuscript proof.'}
    (ROOT/'results').mkdir(exist_ok=True)
    (ROOT/'results'/'nm03_gap_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(f'NM-03 gap checks: {out["passed"]}/{out["total"]}')

if __name__=='__main__':
    main()
