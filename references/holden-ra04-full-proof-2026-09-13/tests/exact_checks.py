#!/usr/bin/env python3
"""Exact finite checks for identities in the RA-04 full-resolution manuscript.

These are regression checks, not a formal verification of the universal theorem.
Run from the package root: python tests/exact_checks.py --output results/exact_checks.json
"""
from __future__ import annotations
import argparse
import json
import platform
import random
from fractions import Fraction as F
from pathlib import Path
import sympy as sp


def krylov(nodes: list[sp.Rational], h: sp.Matrix, t: int) -> sp.Matrix:
    lam = sp.diag(*nodes)
    return sp.Matrix.hstack(*[lam**j * h for j in range(t)])


def nonzero_fixture(nodes: list[int], b: int, seed: int) -> tuple[sp.Matrix, sp.Matrix]:
    rng = random.Random(seed)
    m, t = len(nodes), len(nodes)//b
    for _ in range(1000):
        h = sp.Matrix(m, b, lambda i, j: rng.randint(-5, 5))
        k = krylov(list(map(sp.Rational, nodes)), h, t)
        if k.det() and all(h[r:r+b, :].det() for r in range(m-b+1)):
            return h, k
    raise RuntimeError('Could not construct nonsingular rational fixture.')


def subtract_closed(regions: list[tuple[F, F]], lo: F, hi: F) -> list[tuple[F, F]]:
    out = []
    for a, b in regions:
        if b <= lo or a >= hi:
            out.append((a, b))
        else:
            if a < lo:
                out.append((a, min(b, lo)))
            if hi < b:
                out.append((max(a, hi), b))
    return [(a,b) for a,b in out if a < b]


def merge_closed(intervals: list[tuple[F, F]]) -> list[tuple[F, F]]:
    out: list[tuple[F, F]] = []
    for a,b in sorted(intervals):
        if out and a <= out[-1][1]:
            out[-1] = (out[-1][0], max(b, out[-1][1]))
        else:
            out.append((a,b))
    return out


def cartan_fixture(roots: list[F], h: F) -> dict:
    """Finite implementation of the interval-family selection in Lemma 3.1."""
    roots = sorted(roots)
    s = len(roots)
    regions: dict[int, list[tuple[F, F]]] = {}
    original = []
    for j in range(1, s+1):
        r = F(j, s)*h
        regions[j] = [(roots[i+j-1]-r, roots[i]+r)
                      for i in range(s-j+1) if roots[i+j-1]-r < roots[i]+r]
        original.extend(regions[j])
    selected: list[tuple[F,F,int]] = []
    while any(regions.values()):
        j = max(j for j in regions if regions[j])
        a,b = regions[j][0]
        c, r = (a+b)/2, F(j,s)*h
        assert sum(abs(c-x) < r for x in roots) >= j
        assert all(abs(c-d) >= r+q for d,q,_ in selected)
        selected.append((c,r,j))
        for jj in regions:
            rr = F(jj,s)*h
            regions[jj] = subtract_closed(regions[jj], c-r-rr, c+r+rr)
        assert len(selected) <= s
    cover = merge_closed([(c-3*r,c+3*r) for c,r,_ in selected])
    assert sum((b-a for a,b in cover), F(0)) <= 6*h
    assert sum(j for _,_,j in selected) <= s
    for a,b in original:
        left = [(a,b)]
        for lo,hi in cover:
            left = subtract_closed(left,lo,hi)
        assert not left
    return {'s':s, 'selected_intervals':len(selected),
            'cover_length':str(sum((b-a for a,b in cover), F(0))),
            'six_h':str(6*h)}


def main(output: Path) -> None:
    records = []
    # A deterministic rank witness with exact repeated eigenvalues allowed.
    for b,t in [(1,1),(3,1),(1,4),(2,3),(3,3)]:
        nodes = [sp.Integer(t-i//b+1) for i in range(b*t)]
        h = sp.zeros(b*t,b)
        for i in range(b*t): h[i,i % b] = 1
        det = krylov(nodes,h,t).det()
        assert det != 0
        records.append({'test':'residue_class_rank_witness','b':b,'t':t,'determinant':str(det)})

    x,z = sp.symbols('x z')
    configs = [([9,9,5,4,2,1],2,142),
               ([12,11,9,8,6,5,4,3,1],3,198),
               ([8,6,3,1],1,76)]
    identity_count = 0
    residue_count = 0
    for integers,b,seed in configs:
        nodes = list(map(sp.Rational, integers)); m=len(nodes); t=m//b
        h,k = nonzero_fixture(integers,b,seed)
        lam = sp.diag(*nodes); inv=k.inv(); e=inv[:b,:]
        higher = k[:,b:]
        r = sp.eye(m)-higher*(higher.T*higher).inv()*higher.T
        schur = h.T*r*h
        assert sp.simplify(e*e.T-schur.inv()) == sp.zeros(b,b)
        assert sp.simplify(e*k-sp.Matrix.hstack(sp.eye(b),sp.zeros(b,m-b))) == sp.zeros(b,m)
        # Exact translation invariance of the extrapolation map.
        shift=sp.Rational(1,3)
        ex=sp.Matrix.hstack(*[shift**j*sp.eye(b) for j in range(t)])*inv
        shifted=krylov([a-shift for a in nodes],h,t).inv()[:b,:]
        assert ex==shifted
        assert krylov([a-shift for a in nodes],h,t).det()==k.det()
        # Head identity and direct graph construction at several rational tail nodes.
        tailnodes=[sp.Rational(0),nodes[-1]/3,nodes[-1]]
        tail=sp.Matrix([[2+j, -1+j][:b] for j in range(3)]) if b<=2 else sp.Matrix([[1,2,3],[-2,1,4],[3,-1,2]])
        kt=sp.Matrix.hstack(*[sp.diag(*tailnodes)**j*tail for j in range(t)])
        graph=sp.Matrix.vstack(k,kt)*inv
        assert graph[:m,:]==sp.eye(m)
        for j,node in enumerate(tailnodes):
            ev=sp.Matrix.hstack(*[node**ell*sp.eye(b) for ell in range(t)])*inv
            assert graph[m+j,:]==tail[j,:]*ev
        # Exact first-order optimality for a fixed constant coefficient.
        a=sp.eye(b)[:,0]
        coeff=sp.Matrix.vstack(a,-(higher.T*higher).inv()*higher.T*h*a)
        residual=k*coeff
        assert higher.T*residual==sp.zeros(m-b,1)
        # Test the rational resolvent identity for every basis vector of the moment nullspace.
        p=sp.prod(1-x/nodes[min(2*j,m-1)] for j in range(t-1))
        for u in higher.T.nullspace():
            w=sp.diag(*[p.subs(x,v) for v in nodes])*u
            resolvent=sp.diag(*[v/(z*(z-v)) for v in nodes])
            lhs=h.T*resolvent*u
            rhs=h.T*resolvent*w/p.subs(x,z)
            diff=lhs-rhs
            assert all(sp.cancel(v)==0 for v in diff)
            identity_count += 1
            for node in sorted(set(nodes)):
                observed=sp.Matrix([sp.residue(v,z,node) for v in lhs])
                expected=sum((h[i,:].T*u[i] for i,v in enumerate(nodes) if v==node),sp.zeros(b,1))
                assert observed==expected
                residue_count += b
            assert sp.Matrix([sp.residue(v,z,0) for v in lhs]) == -h.T*u
        records.append({'test':'interpolation_and_resolvent_fixture','b':b,'t':t,
                        'head_determinant':str(k.det()),'schur_identity':True,
                        'translation_identity':True,'graph_identity':True})

    # Exact selected covers in logarithmic coordinates, including many repeated roots.
    cover_records=[]
    for roots,h in [([F(0)]*5,F(1,16)),
                    ([F(-2),F(0),F(1,100),F(2,100),F(1),F(3)],F(1,8)),
                    ([F(i,100) for i in range(12)],F(1,32)),
                    ([F(-1),F(-1),F(0),F(0),F(1),F(1)],F(1,64))]:
        cover_records.append(cartan_fixture(roots,h))

    # Symbolic Pascal changes, with no fixed choice of nodes or translation.
    lam_symbol, shift_symbol = sp.symbols('lambda shift')
    for degree in range(13):
        expanded = sum(sp.binomial(degree, j)*(-shift_symbol)**(degree-j)*lam_symbol**j
                       for j in range(degree+1))
        assert sp.expand(expanded-(lam_symbol-shift_symbol)**degree) == 0
    records.append({'test':'symbolic_pascal_translation','degrees_checked':13})

    # A tied extremal singular-value fixture. With H=I_2, E=I_2 the minimizing
    # direction need not be unique. A frozen rational unit vector gives a unit
    # Frobenius perturbation for which the anchored minimum decreases as 1-s.
    step = sp.symbols('s', real=True)
    a = sp.Matrix([sp.Rational(3,5),sp.Rational(4,5)])
    perpendicular = sp.Matrix([-a[1],a[0]])
    basis = sp.Matrix.hstack(a,perpendicular)
    direction = -a*a.T
    assert basis.T*basis == sp.eye(2)
    assert sum(v*v for v in direction) == 1
    assert sp.simplify(basis.T*(sp.eye(2)+step*direction)*basis) == sp.diag(1-step,1)
    assert sp.simplify((sp.eye(2)+step*direction)*a) == (1-step)*a
    records.append({'test':'tied_singular_value_descent','basis_diagonalization':True,
                    'unit_frobenius_direction':True})

    # Bookkeeping constants, all rational. The transcendental gap factor is kept symbolic.
    assert 8192*1280 == 10485760
    assert 10485760 < 2**24
    assert 2*(2**24)**2*2**8 == 2**57  # Common-event uniform bound; eta=delta/2.
    payload={'status':'PASS','python':platform.python_version(),'sympy':sp.__version__,
             'records':records,'exact_resolvent_vector_identities':identity_count,
             'exact_positive_pole_coordinate_residues':residue_count,
             'cartan_cover_fixtures':cover_records,
             'limitations':'Finite exact checks; not a machine-checked proof of the universal theorems.'}
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps(payload,indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path('results/exact_checks.json'))
    args=parser.parse_args()
    main(args.output)
