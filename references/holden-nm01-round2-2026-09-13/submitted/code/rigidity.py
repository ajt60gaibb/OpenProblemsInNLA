#!/usr/bin/env python3
"""Exact identities and interval certificate for weak-SSC projective rigidity."""
from __future__ import annotations
import json
from itertools import combinations
from pathlib import Path
import sympy as s


def bernstein_coefficients(poly, t, lo, hi):
    """Exact coefficients on [lo,hi], all positive => polynomial positive."""
    x=s.Symbol('x'); p=s.Poly(s.expand(poly.subs(t,lo+(hi-lo)*x)),x)
    degree=max(0,p.degree())
    return [s.factor(sum(p.nth(k)*s.binomial(j,k)/s.binomial(degree,k)
                       for k in range(j+1))) for j in range(degree+1)]


def certificate():
    t=s.Symbol('t'); e=s.ones(3,1)
    q1=s.Matrix([-s.Rational(1,3),s.Rational(2,3),s.Rational(2,3)])
    q2=s.Matrix([s.Rational(15,19),-s.Rational(6,19),s.Rational(10,19)])
    q3=s.Matrix([s.Rational(6,7),s.Rational(3,7),-s.Rational(2,7)])
    qs=[q1,q2,q3]; normals=[s.eye(3)[:,i] for i in range(3)]+qs
    weights=s.Matrix([243,361,392])
    B=s.Matrix.hstack(*[q-q.multiply_elementwise(q) for q in qs])
    if B*weights!=s.zeros(3,1): raise ValueError('Rigidity identity failed.')
    if any(q.dot(e)!=1 or q.dot(q)!=1 or 0 in q for q in qs):
        raise ValueError('Invalid extra contacts.')
    if any(q.dot(p)==0 for q,p in combinations(qs,2)):
        raise ValueError('Unexpected extra orthogonality.')
    verts=[]
    for a,b in combinations(normals,2):
        A=s.Matrix.vstack(e.T,a.T,b.T)
        if A.det()==0: continue
        v=A.inv()*s.Matrix([1,0,0])
        if all(q.dot(v)>=0 for q in normals) and v not in verts: verts.append(v)
    H=s.Matrix.hstack(*verts)
    if len(verts)!=6 or H.rank()!=3: raise ValueError('Vertex count failed.')
    lo=-s.Rational(1,1000); hi=-lo; ell=s.Matrix([1+t,1,1]); rows=[]
    for ids in combinations(range(6),3):
        C=s.Matrix.vstack(*[normals[i].T for i in ids])
        if C.det()==0: raise ValueError('Unexpected singular triple.')
        u=C.T.inv()*ell
        p=s.factor(C.det()*s.prod(u))
        row={'triple':list(ids),'scales':[str(s.factor(v)) for v in u],
             'determinant_product':str(p)}
        identically_zero=[i for i,v in enumerate(u) if v==0]
        negative=[i for i,v in enumerate(u) if v.subs(t,lo)<0 and v.subs(t,hi)<0]
        if identically_zero:
            row.update(classification='infeasible_zero_scale',witness=identically_zero[0])
        elif negative:
            row.update(classification='infeasible_negative_scale',witness=negative[0])
        else:
            if not all(v.subs(t,lo)>0 and v.subs(t,hi)>0 for v in u):
                raise ValueError(f'Undecided scales for {ids}.')
            if ids==(0,1,2):
                if p!=1+t: raise ValueError('Identity value failed.')
                row['classification']='identity'
            else:
                gap=s.expand((1+t)**2-p**2)
                bc=bernstein_coefficients(gap,t,lo,hi)
                if not all(c>0 for c in bc):
                    raise ValueError(f'Interval dominance failed for {ids}.')
                row.update(classification='strictly_worse',
                           comparison_polynomial=str(gap),
                           bernstein_coefficients=[str(c) for c in bc])
        rows.append(row)
    return {'schema':'nm01-rigidity-v1','accepted':True,
            'H':[[str(v) for v in row] for row in H.tolist()],
            'extra_contacts':[[str(v) for v in q] for q in qs],
            'positive_weights':[243,361,392],
            'weighted_tangent_identity':[[str(v) for v in row] for row in B.tolist()],
            'extra_contact_pair_dots':[str(q.dot(p)) for q,p in combinations(qs,2)],
            'interval':[str(lo),str(hi)],'excluded_projective_parameter':0,
            'triples':rows,'triples_checked':len(rows),
            'claim':'X_t leaves the original weak-SSC promise for 0<|t|<=1/1000; no global-minimization claim is made for these off-promise inputs.'}


def main():
    import argparse
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path)
    p.add_argument('--verify',type=Path)
    args=p.parse_args(); result=certificate()
    if args.verify and json.loads(args.verify.read_text())!=result:
        raise ValueError('Frozen certificate differs from regenerated exact certificate.')
    if args.output: args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('triples','H','weighted_tangent_identity')},indent=2))

if __name__=='__main__': main()
