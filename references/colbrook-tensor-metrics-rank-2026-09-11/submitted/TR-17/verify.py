#!/usr/bin/env python3
"""Exact finite checks for the identities in the TR-17 proof.

Run: python verify.py
Only Python's standard library is required. The geometric lemmas are proved
in solution.pdf; these finite coefficient tests are not a proof substitute.
"""
from __future__ import annotations
from itertools import product
from math import comb, factorial, prod
import json
from pathlib import Path
import sys

Index = tuple[int, ...]
Poly = dict[Index, int]


def indices(bounds: Index):
    return product(*(range(b+1) for b in bounds))


def multiply(a: Poly, b: Poly, bounds: Index) -> Poly:
    result: Poly = {}
    for i, x in a.items():
        for j, y in b.items():
            index = tuple(u+v for u,v in zip(i,j))
            if all(u<=v for u,v in zip(index,bounds)):
                result[index] = result.get(index,0)+x*y
    return {i:x for i,x in result.items() if x}


def axis_poly(j: int, coeffs: list[int], bounds: Index) -> Poly:
    result: Poly = {}
    for power, coefficient in enumerate(coeffs):
        if coefficient and power<=bounds[j]:
            ind = [0]*len(bounds)
            ind[j] = power
            result[tuple(ind)] = coefficient
    return result


def inv_linear(d: Index, bounds: Index) -> Poly:
    # Coefficients of 1/(1+sum d_j h_j), by the multinomial theorem.
    return {a: (-1)**sum(a)*factorial(sum(a))*prod(dj**aj for dj,aj in zip(d,a))
                //prod(factorial(aj) for aj in a) for a in indices(bounds)}


def b_series(beta: Index, d: Index) -> int:
    # Direct coefficient in the formal series defining B_beta.
    ans = 0
    for ell in indices(beta):
        nu = tuple(b-e for b,e in zip(beta,ell))
        multinomial = factorial(sum(nu))//prod(factorial(u) for u in nu)
        ans += (-1)**sum(ell)*prod(comb(b,e) for b,e in zip(beta,ell))*multinomial*prod(dj**u for dj,u in zip(d,nu))
    return ans


def b_positive(beta: Index, d: Index) -> int:
    # Independent multiplication of the nonnegative linear factors L-h_j.
    zero = (0,)*len(beta)
    poly: Poly = {zero:1}
    for j, exponent in enumerate(beta):
        linear: Poly = {}
        for i, di in enumerate(d):
            a = [0]*len(beta)
            a[i] = 1
            coefficient = di-int(i==j)
            if coefficient:
                linear[tuple(a)] = coefficient
        for _ in range(exponent):
            poly = multiply(poly,linear,beta)
    return poly.get(beta,0)


def frobenius_csm(m: Index) -> Poly:
    poly: Poly = {(0,)*len(m):1}
    for j, mj in enumerate(m):
        numerator = axis_poly(j,[comb(mj+1,a) for a in range(mj+1)],m)
        inverse = axis_poly(j,[(-2)**a for a in range(mj+1)],m)
        poly = multiply(poly,multiply(numerator,inverse,m),m)
    return poly


def basis_class(m: Index, g: dict[Index,int]) -> Poly:
    result: Poly = {}
    for alpha, coefficient in g.items():
        term = {alpha:coefficient*(-1)**sum(alpha)}
        for j, (mj,aj) in enumerate(zip(m,alpha)):
            term = multiply(term,axis_poly(j,[comb(mj-aj,t) for t in range(mj-aj+1)],m),m)
        for i,x in term.items():
            result[i] = result.get(i,0)+x
    return {i:x for i,x in result.items() if x}


def section_integers(csm: Poly, m: Index) -> dict[Index,int]:
    result: dict[Index,int] = {}
    for alpha in indices(m):
        p = {i:x for i,x in csm.items() if all(u<=v for u,v in zip(i,alpha))}
        for j, (mj,aj) in enumerate(zip(m,alpha)):
            exponent = mj-aj+1
            inverse = axis_poly(j,[(-1)**t*comb(exponent+t-1,t) for t in range(aj+1)],alpha)
            p = multiply(p,inverse,alpha)
        result[alpha] = (-1)**sum(alpha)*p.get(alpha,0)
    return result


def ed_direct(csm: Poly, m: Index, d: Index) -> int:
    return (-1)**sum(m)*multiply(csm,inv_linear(d,m),m).get(m,0)


def main() -> None:
    identity_tests = 0
    for k in range(1,5):
        maximum = 5 if k==1 else 3 if k==2 else 2
        for beta in indices((maximum,)*k):
            for d in product(range(1,4 if k<=2 else 3),repeat=k):
                a, b = b_series(beta,d), b_positive(beta,d)
                assert a == b >= 0, (beta,d,a,b)
                identity_tests += 1
    print(f"PASS: nonnegative coefficient identity in {identity_tests} exact cases")
    format_tests = 0
    for k in range(1,4):
        for m in indices((3,)*k):
            if sum(m)>7:
                continue
            csm = frobenius_csm(m)
            ones = {alpha:1 for alpha in indices(m)}
            assert csm == basis_class(m,ones), m
            assert section_integers(csm,m) == ones, m
            arbitrary_g = {a:(-1)**sum(a)*(1+sum((j+1)*u for j,u in enumerate(a))) for a in indices(m)}
            assert section_integers(basis_class(m,arbitrary_g),m) == arbitrary_g, m
            for d in product(range(1,4),repeat=k):
                direct = ed_direct(csm,m,d)
                positive_sum = sum(b_positive(beta,d) for beta in indices(m))
                assert direct == positive_sum, (m,d,direct,positive_sum)
                arbitrary_ed = ed_direct(basis_class(m,arbitrary_g),m,d)
                expansion = sum(arbitrary_g[a]*b_positive(tuple(mi-ai for mi,ai in zip(m,a)),d) for a in indices(m))
                assert arbitrary_ed == expansion, (m,d)
                format_tests += 1
    print(f"PASS: Frobenius CSM, section inversion, and ED expansion in {format_tests} formats")
    smooth_tests = 0
    for k in range(1,4):
        for m in product(range(1,4),repeat=k):
            if sum(m)>6:
                continue
            for d in product(range(1,3),repeat=k):
                # The CSM class for a smooth zero divisor of multidegree 2*d.
                csm: Poly = {(0,)*k:1}
                for j,mj in enumerate(m):
                    csm = multiply(csm,axis_poly(j,[comb(mj+1,a) for a in range(mj+1)],m),m)
                csm = multiply(csm,inv_linear(tuple(2*x for x in d),m),m)
                g = section_integers(csm,m)
                assert all(x>=1 and x%2==1 for x in g.values()), (m,d,g)
                assert ed_direct(csm,m,d) >= ed_direct(frobenius_csm(m),m,d)
                smooth_tests += 1
    print(f"PASS: all section integers are positive odd integers in {smooth_tests} smooth-divisor checks")
    examples = []
    for m,d,label in [((1,),(3,),"binary cubics"),((2,),(3,),"ternary cubics"),((1,1),(1,1),"2 x 2 matrices"),((1,1,1),(1,1,1),"2 x 2 x 2 tensors"),((2,2,2),(1,1,1),"3 x 3 x 3 tensors"),((1,2),(1,2),"P1 x P2 of multidegree (1,2)")]:
        value = ed_direct(frobenius_csm(m),m,d)
        examples.append({"description":label,"projective_dimensions":m,"multidegrees":d,"frobenius_ed_degree":value})
        print(f"CHECK: {label}: Frobenius ED degree {value}")
    known = {"binary cubics":3,"ternary cubics":7,"2 x 2 matrices":2,"2 x 2 x 2 tensors":6,"3 x 3 x 3 tensors":37}
    assert all(x["frobenius_ed_degree"]==known[x["description"]] for x in examples if x["description"] in known)
    Path(__file__).with_name("checked_examples.json").write_text(json.dumps(examples,indent=2)+"\n",encoding="utf-8")
    print(f"All exact checks passed. Python {sys.version.split()[0]} (standard library only).")
    print("These checks supplement, and do not replace, the general geometric proof.")


if __name__ == "__main__":
    main()
