#!/usr/bin/env python3
"""Exact supplementary verification of the NM-04 proof.

The all-dimension proof is in manuscripts/NM-04_sinkhorn_identity.tex.
This script uses rational arithmetic only; no Sinkhorn iteration or numerical
root finding is involved. Run from any directory: python verify_nm04.py
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path
import random
import sympy as sp

Index = tuple[tuple[int, ...], tuple[int, ...]]
ROOT = Path(__file__).resolve().parents[1]


def specifications(m: int, n: int, offset: int = 1) -> list[Index]:
    """Index all equal-order minors; m,n are full bordered dimensions."""
    return [(r, c) for k in range(min(m, n))
            for r in itertools.combinations(range(offset, m - 1 + offset), k)
            for c in itertools.combinations(range(offset, n - 1 + offset), k)]


def catalog_matrix(m: int, n: int, indices: list[Index]) -> sp.Matrix:
    """Implement the four set-difference cases verbatim, independently of Df."""
    h = sp.zeros(len(indices))
    for i, (r, c) in enumerate(indices):
        for j, (rr, cc) in enumerate(indices):
            if i == j:
                h[i, j] = len(r) * (m + n) - m * n
                continue
            a, b, d, e = set(r)-set(rr), set(rr)-set(r), set(c)-set(cc), set(cc)-set(c)
            if not a and len(b) == 1 and not d and len(e) == 1:
                s, t = next(iter(b)), next(iter(e))
                h[i, j] = m * (-1)**(rr.index(s) + cc.index(t) + 2)
            elif len(a) == 1 and not b and len(d) == 1 and not e:
                s, t = next(iter(a)), next(iter(d))
                h[i, j] = n * (-1)**(r.index(s) + c.index(t) + 3)
            elif not a and not b and len(d) == 1 and len(e) == 1:
                s, t = next(iter(d)), next(iter(e))
                h[i, j] = m * (-1)**(c.index(s) + cc.index(t) + 2)
            elif len(a) == 1 and len(b) == 1 and not d and not e:
                s, t = next(iter(a)), next(iter(b))
                h[i, j] = n * (-1)**(r.index(s) + rr.index(t) + 2)
    return h


def minor_vectors(a: sp.Matrix, indices: list[Index]) -> tuple[sp.Matrix, sp.Matrix]:
    delta = sp.Matrix([a.extract((0,)+r, (0,)+c).det() for r,c in indices])
    gamma = sp.Matrix([a[0,0] * a.extract(r,c).det() for r,c in indices])
    return delta, gamma


def balanced_matrix(m: int, n: int, seed: int) -> sp.Matrix:
    """A positive rational matrix with exact prescribed margins."""
    rng = random.Random(seed)
    a = sp.ones(m,n)/n
    denominator = 100*m*n*max(1,(m-1)*(n-1))
    for i in range(m-1):
        for j in range(n-1):
            z = sp.Rational(rng.randrange(-9,10), denominator)
            a[i,j] += z
            a[i,n-1] -= z
            a[m-1,j] -= z
            a[m-1,n-1] += z
    assert all(v > 0 for v in a)
    assert a*sp.ones(n,1) == sp.ones(m,1)
    assert sp.ones(1,m)*a == sp.ones(1,n)*sp.Rational(m,n)
    return a


def verify_balanced(a: sp.Matrix, label: str) -> dict:
    m,n = a.shape
    inds = specifications(m,n)
    h = catalog_matrix(m,n,inds)
    delta,gamma = minor_vectors(a,inds)
    w = sp.Matrix([sp.Rational(n,m)**len(r) for r,c in inds])
    residual = gamma.multiply_elementwise(w) + (a[0,0]/m)*h*delta.multiply_elementwise(w)
    assert residual == sp.zeros(len(inds),1), (label,list(residual))
    # Check the covariance at a scalar unrelated to the Sinkhorn entry.
    left = [sp.Rational(i+2,i+1) for i in range(m)]
    right = [sp.Rational(2*j+3,j+2) for j in range(n)]
    scaled = sp.diag(*left)*a*sp.diag(*right)
    dd,gg = minor_vectors(scaled,inds)
    scales = sp.Matrix([left[0]*right[0]*sp.prod(left[i] for i in r)*sp.prod(right[j] for j in c)
                        for r,c in inds])
    assert dd == delta.multiply_elementwise(scales)
    assert gg == gamma.multiply_elementwise(scales)
    scaled_null = sp.Matrix([w[i]/scales[i] for i in range(len(inds))])
    assert gg.multiply_elementwise(scaled_null)+(a[0,0]/m)*h*dd.multiply_elementwise(scaled_null) == sp.zeros(len(inds),1)
    return {"case": label,"dimensions":[m,n],"number_of_minors":len(inds),
            "null_vector_exact":True,"scaling_covariance_exact":True,
            "zero_delta_minors":sum(v==0 for v in delta)}


def derivative(t: sp.Matrix, r: tuple[int,...], c: tuple[int,...], z: sp.Matrix) -> sp.Expr:
    return sum((-1)**(i+j)*t.extract(r[:i]+r[i+1:],c[:j]+c[j+1:]).det()*z[r[i],c[j]]
               for i in range(len(r)) for j in range(len(c)))


def verify_four_identities(p: int, q: int, seed: int) -> int:
    rng = random.Random(seed)
    t = sp.Matrix(p,q,lambda i,j:sp.Rational(rng.randrange(-5,6),rng.randrange(1,5)))
    inds = specifications(p+1,q+1,offset=0)
    f = {(r,c):t.extract(r,c).det() for r,c in inds}
    onep,oneq = sp.ones(p,1),sp.ones(q,1)
    directions = [onep*oneq.T,(t*oneq)*oneq.T,onep*(onep.T*t),(t*oneq)*(onep.T*t)]
    for r,c in inds:
        lower = sum((-1)**(i+j)*f[r[:i]+r[i+1:],c[:j]+c[j+1:]]
                    for i in range(len(r)) for j in range(len(c)))
        upper = sp.S.Zero
        for i in set(range(p))-set(r):
            for j in set(range(q))-set(c):
                rr,cc=tuple(sorted(r+(i,))),tuple(sorted(c+(j,)))
                upper += (-1)**(rr.index(i)+cc.index(j))*f[rr,cc]
        cswap = sp.S.Zero
        for i,s in enumerate(c):
            for j in set(range(q))-set(c):
                cc=tuple(sorted(tuple(x for x in c if x!=s)+(j,)))
                cswap += (-1)**(i+cc.index(j))*f[r,cc]
        rswap = sp.S.Zero
        for i,s in enumerate(r):
            for j in set(range(p))-set(r):
                rr=tuple(sorted(tuple(x for x in r if x!=s)+(j,)))
                rswap += (-1)**(i+rr.index(j))*f[rr,c]
        rhs=[lower,len(r)*f[r,c]+cswap,len(r)*f[r,c]+rswap,sum(t)*f[r,c]-upper]
        for direction,value in zip(directions,rhs):
            assert sp.expand(derivative(t,r,c,direction)-value)==0,(p,q,r,c)
    return 4*len(inds)


def verify_principal_expansion() -> int:
    a = sp.Matrix([[2,3,5],[7,11,13]])
    inds=specifications(2,3);h=catalog_matrix(2,3,inds)
    d,g=minor_vectors(a,inds);z=sp.Symbol('z')
    k=sp.diag(*g)+(z/2)*h*sp.diag(*d)
    expansion=sp.S.Zero
    for bits in itertools.product((0,1),repeat=len(inds)):
        chosen=[i for i,b in enumerate(bits) if b]
        other=[i for i,b in enumerate(bits) if not b]
        expansion += h.extract(chosen,chosen).det()*sp.prod(d[i] for i in chosen)*sp.prod(g[i] for i in other)*(z/2)**len(chosen)
    assert sp.expand(k.det()-expansion)==0
    return len(inds)


def main() -> None:
    cases=[]
    for m,n in [(1,1),(1,7),(7,1),(2,2),(2,3),(3,2),(3,3),(3,4),(4,3),(4,4),(4,5),(5,4),(5,5),(3,6),(6,3)]:
        cases.append(verify_balanced(balanced_matrix(m,n,1000*m+n),f"rational_{m}x{n}"))
    for m,n in [(2,5),(4,4),(3,5)]:
        cases.append(verify_balanced(sp.ones(m,n)/n,f"uniform_degenerate_{m}x{n}"))
    checks=sum(verify_four_identities(p,q,71*p+q) for p,q in [(1,1),(2,3),(3,2),(3,3),(4,4)])
    expansion_size=verify_principal_expansion()
    result={"arithmetic":"exact sympy rational/integer", "sympy_version":sp.__version__,
            "balanced_cases":cases,"four_minor_identity_checks":checks,
            "principal_expansion_checked_size":expansion_size,"all_checks_passed":True,
            "scope":"Finite supplementary checks, not a replacement for the all-dimension proof."}
    out=ROOT/'results'/'nm04_verification.json';out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
