#!/usr/bin/env python3
"""Exact tests for the arbitrary-margin and coefficient-symmetry extensions.

These tests supplement the all-dimension proof in NM-04_sinkhorn_identity.tex.
They do not infer a theorem from numerical examples. Only SymPy is required.
"""
from __future__ import annotations
from itertools import combinations
from pathlib import Path
import json
import random
import sympy as sp

ROOT=Path(__file__).resolve().parents[1]
Index=tuple[tuple[int,...],tuple[int,...]]

def indices(m:int,n:int)->list[Index]:
    return [(r,c) for k in range(min(m,n))
            for r in combinations(range(1,m),k)
            for c in combinations(range(1,n),k)]

def margin_matrix(rows:list,cols:list)->sp.Matrix:
    """Indices 0,1,... correspond to manuscript indices 1,2,... ."""
    if sum(rows)!=sum(cols):
        raise ValueError('Margins must have equal totals.')
    m,n=len(rows),len(cols)
    inds=indices(m,n);total=sum(rows);h=sp.zeros(len(inds))
    for i,(r,c) in enumerate(inds):
        for j,(rr,cc) in enumerate(inds):
            if i==j:
                h[i,j]=sum(rows[t] for t in r)+sum(cols[t] for t in c)-total
                continue
            rm,ra,cm,ca=set(r)-set(rr),set(rr)-set(r),set(c)-set(cc),set(cc)-set(c)
            if not rm and len(ra)==1 and not cm and len(ca)==1:
                s,t=next(iter(ra)),next(iter(ca))
                h[i,j]=(-1)**(rr.index(s)+cc.index(t))
            elif len(rm)==1 and not ra and len(cm)==1 and not ca:
                s,t=next(iter(rm)),next(iter(cm))
                h[i,j]=-(-1)**(r.index(s)+c.index(t))*rows[s]*cols[t]
            elif not rm and not ra and len(cm)==1 and len(ca)==1:
                s,t=next(iter(cm)),next(iter(ca))
                h[i,j]=(-1)**(c.index(s)+cc.index(t))*cols[s]
            elif len(rm)==1 and len(ra)==1 and not cm and not ca:
                s,t=next(iter(rm)),next(iter(ra))
                h[i,j]=(-1)**(r.index(s)+rr.index(t))*rows[s]
    return h

def signed_compound(e:sp.Matrix,inds:list[Index],m:int,n:int)->sp.Matrix:
    """Build the additive exterior compound independently by basis replacement."""
    p=m-1
    sets=[tuple([i for i in range(p) if i+1 not in r]+[p+cj-1 for cj in c]) for r,c in inds]
    signs=[(-1)**(sum(r)+(p+1)*len(r)+len(r)*(len(r)-1)//2) for r,c in inds]
    q=sp.zeros(len(inds))
    for i,si in enumerate(sets):
        for j,sj in enumerate(sets):
            if i==j:
                q[i,j]=sum(e[t,t] for t in si)
            else:
                add,rem=set(si)-set(sj),set(sj)-set(si)
                if len(add)==len(rem)==1:
                    r,c=next(iter(add)),next(iter(rem))
                    q[i,j]=e[r,c]*(-1)**(si.index(r)+sj.index(c))
    return sp.diag(*signs)*q*sp.diag(*signs)

def check_matrix(a:sp.Matrix,label:str)->dict:
    m,n=a.shape
    rows=list(a*sp.ones(n,1));cols=list(sp.ones(1,m)*a)
    inds=indices(m,n);h=margin_matrix(rows,cols)
    delta=sp.Matrix([a.extract((0,)+r,(0,)+c).det() for r,c in inds])
    gamma=sp.Matrix([a[0,0]*a.extract(r,c).det() for r,c in inds])
    assert gamma+a[0,0]/(rows[0]*cols[0])*h*delta==sp.zeros(len(inds),1)
    u=sp.Matrix([-1]*(m-1)+cols[1:]);v=sp.Matrix(rows[1:]+[1]*(n-1))
    h2=signed_compound(u*v.T,inds,m,n)-rows[0]*sp.eye(len(inds))
    assert h2==h
    assert (h+rows[0]*sp.eye(len(inds)))*(h+cols[0]*sp.eye(len(inds)))==sp.zeros(len(inds))
    if m+n>2:
        z=sp.Symbol('z');n1=sp.binomial(m+n-3,m-2) if m>=2 else 0;n2=sp.binomial(m+n-3,m-1)
        assert sp.expand(h.charpoly(z).as_expr()-(z+cols[0])**n1*(z+rows[0])**n2)==0
    assert h.det()!=0
    return {'case':label,'dimensions':[m,n],'compound_order':len(inds),'null_vector':True,
            'compound_identity':True,'quadratic_minimal_polynomial_identity':True,
            'characteristic_polynomial':True,'invertible':True}

def check_complement(n:int)->dict:
    inds=indices(n,n);h=margin_matrix([sp.Integer(1)]*n,[sp.Integer(1)]*n)
    universe=set(range(1,n));lookup={rc:i for i,rc in enumerate(inds)}
    perm=[lookup[(tuple(sorted(universe-set(r))),tuple(sorted(universe-set(c))))] for r,c in inds]
    q=sp.diag(*[(-1)**(sum(r)+sum(c)) for r,c in inds])
    transformed=q*h.extract(perm,perm)*q
    assert transformed==-h-2*sp.eye(len(inds))
    assert h*transformed==sp.eye(len(inds))
    assert h.det()==1
    # Exhaustive principal-minor coefficient symmetry at n<=3; sampled at n=4.
    rng=random.Random(818+n);N=len(inds)
    subsets=([tuple(i for i in range(N) if mask>>i&1) for mask in range(1<<N)] if n<=3
             else [tuple(i for i in range(N) if rng.randrange(2)) for _ in range(25)])
    for ss in subsets:
        tt=tuple(sorted(perm[i] for i in range(N) if i not in ss))
        assert h.extract(ss,ss).det()==h.extract(tt,tt).det()
    return {'order':n,'inverse_complement_identity':True,'principal_minors_checked':len(subsets)}

def main()->None:
    rng=random.Random(902);records=[]
    for m,n in [(1,1),(1,4),(4,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3),(4,4),(5,3),(3,5),(5,4),(4,5)]:
        a=sp.Matrix(m,n,[sp.Rational(rng.randrange(1,13),rng.randrange(1,6)) for _ in range(m*n)])
        records.append(check_matrix(a,f'rational_{m}x{n}'))
    records.append(check_matrix(sp.ones(4,4),'rank_one_equal_margins'))
    # A symbolic 2x3 check of the generalized entries and null-vector formula.
    entries=sp.symbols('a:6',positive=True);a=sp.Matrix(2,3,entries)
    rows=list(a*sp.ones(3,1));cols=list(sp.ones(1,2)*a)
    h=margin_matrix(rows,cols);inds=indices(2,3)
    delta=sp.Matrix([a.extract((0,)+r,(0,)+c).det() for r,c in inds])
    gamma=sp.Matrix([a[0,0]*a.extract(r,c).det() for r,c in inds])
    assert all(sp.expand(v)==0 for v in rows[0]*cols[0]*gamma+a[0,0]*h*delta)
    complements=[check_complement(n) for n in range(2,5)]
    out={'arithmetic':'exact rational and symbolic SymPy','matrix_cases':records,
         'symbolic_2x3_null_identity':True,'square_complement_tests':complements,
         'scope':'Finite checks supplement, and do not replace, the exterior-power proof.'}
    (ROOT/'results'/'nm04_margin_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':
    main()
