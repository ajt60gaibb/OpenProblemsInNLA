#!/usr/bin/env python3
"""TR-20 diagnostics REBUILT during recovery from the restored manuscript.

Tests the Chern-class arithmetic, coefficient formula, requested closed
forms, and local symbolic models. These tests do not certify incidence
irreducibility, global transversality, or the generic degree of a map.
"""
from __future__ import annotations
import json
from math import comb
from pathlib import Path
import sympy as sp

Poly = dict[tuple[int, int], int]


def add(*polys: Poly) -> Poly:
    result: Poly = {}
    for p in polys:
        for term, coefficient in p.items():
            result[term] = result.get(term, 0)+coefficient
    return {t: c for t, c in result.items() if c}


def scale(p: Poly, scalar: int) -> Poly:
    return {t: c*scalar for t, c in p.items() if c*scalar}


def mul(p: Poly, q: Poly, m: int, n: int) -> Poly:
    result: Poly = {}
    for (a, b), c in p.items():
        for (i, j), d in q.items():
            if a+i < m and b+j < n:
                t = (a+i, b+j)
                result[t] = result.get(t, 0)+c*d
    return {t: c for t, c in result.items() if c}


def ell_power(degree: int, m: int, n: int) -> Poly:
    return {(i, degree-i): 2**degree*comb(degree, i)
            for i in range(degree+1) if i < m and degree-i < n}


def log_class(m: int, n: int) -> Poly:
    cm = [sum((-1)**a*comb(m, a)*2**(i-a) for a in range(i+1))
          for i in range(m)]
    cn = [sum((-1)**a*comb(n, a)*2**(j-a) for a in range(j+1))
          for j in range(n)]
    return {(i, j): cm[i]*cn[j] for i in range(m) for j in range(n)
            if cm[i]*cn[j]}


def chern_calculation(m: int, n: int) -> dict:
    if min(m, n) < 2:
        raise ValueError("Both dimensions must be at least two")
    k = m+n-2
    F = log_class(m, n)
    Fi = [{t: c for t, c in F.items() if sum(t) == i} for i in range(k+1)]
    C = add(*(mul(Fi[i], ell_power(k-i, m, n), m, n) for i in range(k+1)))
    A = add(*(scale(mul(Fi[i], ell_power(k-1-i, m, n), m, n), k-i)
              for i in range(k)))
    T = add(*(scale(mul(Fi[i], ell_power(k-2-i, m, n), m, n), k-1-i)
              for i in range(k-1)))
    total_poly = add(scale(C, k), mul({(1, 0): 2*(n-1), (0, 1): 2*(m-1)}, A, m, n))
    da = add(mul({(1, 0): 2}, A, m, n), mul({(1, 1): -4}, T, m, n))
    db = add(mul({(0, 1): 2}, A, m, n), mul({(1, 1): -4}, T, m, n))
    top = lambda p: p.get((m-1, n-1), 0)
    rr, total, iso = top(C), top(total_poly), top(da)+top(db)
    return {"m": m, "n": n, "critical_point_count": rr,
            "total_ramification": total, "boundary_a": top(da),
            "boundary_b": top(db), "nonisotropic_degree": total-iso}


def direct_coefficient(m: int, n: int) -> int:
    """Expand the final rational formula separately, before truncation."""
    numerator: Poly = {(i, j): (-1)**(i+j)*comb(m, i)*comb(n, j)
                       for i in range(m) for j in range(n)}
    numerator = mul(numerator, {(0, 0): m+n-2, (1, 0): -2*m,
                               (0, 1): -2*n, (1, 1): 8}, m, n)
    inverse_xy = {(i, j): 2**(i+j) for i in range(m) for j in range(n)}
    inverse_total = {(i, j): (i+j+1)*comb(i+j, i)*2**(i+j)
                     for i in range(m) for j in range(n)}
    return mul(mul(numerator, inverse_xy, m, n), inverse_total, m, n).get((m-1, n-1), 0)


def symbolic_checks() -> dict:
    x, y, z, n = sp.symbols("x y z n")
    extracted = {}
    for m in (2, 3):
        rational = ((m+n-2-2*m*x-2*n*y+8*x*y)*(1-x)**m /
                    ((1-2*x)*(1-2*y)*(1-2*x-2*y)**2))
        coefficient = sp.diff(rational, x, m-1).subs(x, 0)/sp.factorial(m-1)
        c = 1-2*y
        expected = (4*(n-1+2*y)/c**3 if m == 2 else
                    12/c**5+12*(n-1)/c**4-(4*n+13)/c**3+(n+4)/c**2)
        assert sp.factor(coefficient-expected) == 0
        transformed = sp.factor(expected.subs(y, z/(1+z))/(1+z)**2)
        extracted[str(m)] = {"x_coefficient_without_1_minus_y_power": str(sp.factor(coefficient)),
                             "after_residue_substitution": str(transformed)}
    binom = lambda a, j: sp.prod(a-i for i in range(j))/sp.factorial(j)
    formula2 = 4*((n-1)*binom(n+1, 2)+(n+1)*binom(n, 2))
    formula3 = ((9*n-9)*binom(n+3, 4)+(13*n+25)*binom(n+2, 4)
                +(73-5*n)*binom(n+1, 4)+(7-17*n)*binom(n, 4))
    assert sp.expand(formula2-4*n*(n**2-1)) == 0
    assert sp.expand(formula3-12*n**3*(n-1)) == 0
    # Boundary local equations, including the empty tangential block when k=2.
    u, v, s, aa, bb, beta, gamma = sp.symbols("u v s aa bb beta gamma")
    p_single = aa*u+bb*s+beta*u*u/2
    assert sp.expand(u*sp.diff(p_single, u)-p_single) == -bb*s+beta*u*u/2
    p_cross = aa*u+bb*v+gamma*s
    equations = sp.Matrix([u*sp.diff(p_cross, u)-p_cross,
                           v*sp.diff(p_cross, v)-p_cross])
    jacobian = equations.jacobian([u, v])
    assert jacobian == sp.Matrix([[0, -bb], [-aa, 0]])
    assert jacobian.det() == -aa*bb
    # Unique rank-one direction in the pencil spanned by a rank-one point
    # and a nonzero projective tangent direction.
    alpha, b = sp.symbols("alpha b")
    tangent_pencil = sp.Matrix([[alpha, b], [b, 0]])
    assert tangent_pencil.det() == -b*b
    A, Ua = sp.Matrix([[1, 0], [0, 0]]), sp.Matrix([[0, 1], [1, 0]])
    vector = lambda M: sp.Matrix(list(M))
    normal = vector(Ua)*vector(A).T+vector(A)*vector(Ua).T
    assert normal.rank() == 2
    return {"coefficient_extractions": extracted,
            "two_binomial_identities": True,
            "simple_boundary_model": str(-bb*s+beta*u*u/2),
            "crossing_jacobian_determinant": str(jacobian.det()),
            "tangent_pencil_determinant": str(tangent_pencil.det()),
            "example_mixed_normal_flattening_rank": 2}


def main() -> None:
    cases = []
    for m in range(2, 9):
        for n in range(2, 11):
            case = chern_calculation(m, n)
            direct = direct_coefficient(m, n)
            assert case["nonisotropic_degree"] == direct
            assert direct == direct_coefficient(n, m)
            known_rr = sum(4**(i-1)*comb(m, i)*comb(n, i)
                           for i in range(1, min(m, n)+1))
            assert case["critical_point_count"] == known_rr
            if m == 2:
                assert direct == 24*comb(n+1, 3)
            if m == 3:
                assert direct == 24*n*n*comb(n, 2)
            cases.append(case)
    extended = []
    for n in range(2, 51):
        for m in (2, 3):
            degree = direct_coefficient(m, n)
            expected = 24*comb(n+1, 3) if m == 2 else 24*n*n*comb(n, 2)
            assert degree == expected
            extended.append({"m": m, "n": n, "degree": degree})
    result = {"target": "TR-20", "status": "PASS", "arithmetic": "exact integer / symbolic",
              "code_provenance": "Rebuilt during recovery from restored proof and surviving formula calculation.",
              "scope": "Arithmetic and local-model diagnostics only; not global geometric verification.",
              "chern_grid": cases, "extended_two_formula_grid": extended,
              "symbolic_checks": symbolic_checks()}
    out = Path(__file__).resolve().parents[1]/"evidence/TR-20.json"
    out.write_text(json.dumps(result, indent=2)+"\n")
    print(f"TR-20: PASS; {len(cases)} Chern/direct-formula comparisons, "
          f"{len(extended)} extended formula cases, symbolic identities and local models")


if __name__ == "__main__":
    main()
