#!/usr/bin/env python3
"""Exact singular-metric stress checks for the TR-17 proof.

This is not a proof of the universal theorem.  Over QQ it checks four
explicit positive-definite metrics, counts critical schemes with algebraic
multiplicity, and excludes critical points missed by the main affine chart.
It also checks transversality of the chosen distance hyperplane to the
reduced divisor and avoidance of its singular strata.

Requires SymPy.  Run: python verify_critical_examples.py
Results are written alongside this script as critical_examples.json.
"""
from __future__ import annotations

from collections import deque
from itertools import product
from pathlib import Path
from typing import Sequence
import json
import sys
import sympy as sp


class VerificationFailure(RuntimeError):
    """An exact identity or geometric certificate did not match."""


def demand(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationFailure(message)


def basis(polys: Sequence[sp.Expr], variables: Sequence[sp.Symbol]):
    return sp.groebner(polys, *variables, order="grevlex", domain=sp.QQ)


def unit_ideal(polys: Sequence[sp.Expr], variables: Sequence[sp.Symbol]) -> bool:
    g = basis(polys, variables)
    return len(g.polys) == 1 and g.polys[0].as_expr() == 1


def quotient_length(polys: Sequence[sp.Expr], variables: Sequence[sp.Symbol]) -> int:
    """Count standard monomials, hence scheme length, not distinct roots."""
    g = basis(polys, variables)
    if len(g.polys) == 1 and g.polys[0].as_expr() == 1:
        return 0
    demand(g.is_zero_dimensional, "Critical ideal is not zero-dimensional")
    leading = [p.LM(order=g.order).exponents for p in g.polys]
    zero = (0,) * len(variables)
    standard = {zero}
    queue = deque([zero])
    while queue:
        monomial = queue.popleft()
        for j in range(len(variables)):
            child = tuple(e + (i == j) for i, e in enumerate(monomial))
            if child in standard:
                continue
            if any(all(a >= b for a, b in zip(child, lm)) for lm in leading):
                continue
            standard.add(child)
            queue.append(child)
    return len(standard)


def logarithmic_numerators(factors, variables):
    """P*dlog(q), where P is the reduced support and q=prod(f_i**m_i)."""
    support = sp.expand(sp.prod(f for f, _ in factors))
    numerators = [
        sp.expand(sum(m * sp.diff(f, v) * sp.cancel(support / f)
                      for f, m in factors))
        for v in variables
    ]
    return support, numerators


def check_example(name, blocks, homogeneous_factors, ell, gram,
                  expected_auxiliary, expected_ed):
    saturation = sp.Symbol("saturation")
    # Sylvester's criterion is exact here, with the specified monomial basis.
    minors = [sp.det(gram[:j, :j]) for j in range(1, gram.rows + 1)]
    demand(all(value > 0 for value in minors), f"{name}: Gram matrix not SPD")
    charts = list(product(*(range(len(b)) for b in blocks)))
    main_chart = (0,) * len(blocks)
    original_infinity = sp.prod(b[0] for b in blocks)
    auxiliary_length = None
    ed_length = None
    boundary_checks = 0
    transversality_checks = 0

    for chart in charts:
        substitutions = {block[j]: sp.Integer(1) for block, j in zip(blocks, chart)}
        variables = tuple(v for block, j in zip(blocks, chart)
                          for i, v in enumerate(block) if i != j)
        demand(len(variables) == 2, "These stress examples are surfaces")
        factors = [(sp.expand(f.subs(substitutions)), m)
                   for f, m in homogeneous_factors]
        ell_chart = sp.expand(ell.subs(substitutions))
        support, numerators = logarithmic_numerators(factors, variables)
        critical = [sp.expand(2 * support * sp.diff(ell_chart, v)
                              - ell_chart * num)
                    for v, num in zip(variables, numerators)]
        equations = critical + [saturation * support * ell_chart - 1]
        all_variables = (saturation,) + variables

        if chart == main_chart:
            auxiliary_length = quotient_length(
                numerators + [saturation * support - 1], all_variables)
            ed_length = quotient_length(equations, all_variables)
        else:
            infinity = sp.expand(original_infinity.subs(substitutions))
            demand(unit_ideal(equations + [infinity], all_variables),
                   f"{name}: distance critical point at infinity in chart {chart}")
            boundary_checks += 1

        a, b = variables
        jac = sp.expand(sp.diff(support, a) * sp.diff(ell_chart, b)
                        - sp.diff(support, b) * sp.diff(ell_chart, a))
        demand(unit_ideal([support, ell_chart, jac], variables),
               f"{name}: distance hyperplane not transverse in chart {chart}")
        demand(unit_ideal([ell_chart, sp.diff(ell_chart, a),
                           sp.diff(ell_chart, b)], variables),
               f"{name}: singular distance hyperplane in chart {chart}")
        transversality_checks += 2

        # Auxiliary coordinate hyperplanes meet the support transversely,
        # avoid its singular points, and have no triple crossing with it.
        hyperplanes = [sp.expand(block[0].subs(substitutions)) for block in blocks]
        for h in hyperplanes:
            jac_h = sp.expand(sp.diff(support, a) * sp.diff(h, b)
                              - sp.diff(support, b) * sp.diff(h, a))
            demand(unit_ideal([support, h, jac_h], variables),
                   f"{name}: auxiliary boundary is not general enough")
            transversality_checks += 1
        if len(hyperplanes) == 2:
            demand(unit_ideal([support] + hyperplanes, variables),
                   f"{name}: auxiliary triple crossing")
            transversality_checks += 1

    demand(auxiliary_length == expected_auxiliary, f"{name}: wrong auxiliary length")
    demand(ed_length == expected_ed, f"{name}: wrong ED length")
    result = {
        "name": name,
        "auxiliary_critical_scheme_length": auxiliary_length,
        "distance_critical_scheme_length": ed_length,
        "projective_charts": len(charts),
        "no_missing_distance_points_checks": boundary_checks,
        "transversality_checks": transversality_checks,
        "gram_leading_principal_minors": list(map(str, minors)),
        "status": "PASS",
    }
    print(json.dumps(result, indent=2), flush=True)
    return result


def main() -> None:
    u0, u1, v0, v1 = sp.symbols("u0 u1 v0 v1")
    blocks = [(u0, u1), (v0, v1)]
    monomials = sp.Matrix([u0*v0, u1*v0, u0*v1, u1*v1])
    ell = u0*v0 + 2*u1*v0 + 3*u0*v1 + 5*u1*v1
    nodal_gram = sp.diag(1, 1, 1, 4)
    nodal_gram[0, 3] = nodal_gram[3, 0] = -1
    q_node = sp.expand((monomials.T * nodal_gram * monomials)[0])
    q_smooth = sp.expand((monomials.T * sp.diag(1, 1, 1, 2) * monomials)[0])
    results = []
    results.append(check_example(
        "2x2 Frobenius", blocks,
        [(u0**2+u1**2, 1), (v0**2+v1**2, 1)], ell,
        sp.eye(4), 1, 2))
    results.append(check_example(
        "2x2 smooth biquadric", blocks, [(q_smooth, 1)], ell,
        sp.diag(1, 1, 1, 2), 5, 6))
    results.append(check_example(
        "2x2 reducible nodal biquadric; non-Morse auxiliary point", blocks,
        [(q_node, 1)], ell, nodal_gram, 3, 4))

    # The auxiliary critical point at the origin is not Morse: Hessian rank 1.
    node_affine = q_node.subs({u0: 1, v0: 1})
    hessian = sp.hessian(node_affine, (u1, v1)).subs({u1: 0, v1: 0})
    demand(hessian.rank() == 1, "Non-Morse check failed")
    # Its saturated quotient is supported only at the origin and has length 3.
    s = sp.Symbol("saturation")
    node_ideal = basis([sp.diff(node_affine, u1), sp.diff(node_affine, v1),
                        s*node_affine-1], (s, v1, u1))
    demand(node_ideal.reduce(u1**3)[1] == 0 and
           node_ideal.reduce(v1-u1)[1] == 0,
           "The length-three auxiliary scheme is not supported as expected")

    z0, z1, z2 = sp.symbols("z0 z1 z2")
    A, B = z0**2+z1**2+z2**2, z0**2+z1**2+2*z2**2
    q = sp.Poly(sp.expand(A*B**2), z0, z1, z2)
    cubic_exponents = [(a, b, 3-a-b) for a in range(4) for b in range(4-a)]
    gram = sp.diag(*[q.coeff_monomial(z0**(2*a)*z1**(2*b)*z2**(2*c))
                    for a, b, c in cubic_exponents])
    cubic = (z0**3 + 2*z0**2*z1 + 3*z0**2*z2 + 5*z0*z1**2
             + 7*z0*z1*z2 + 11*z0*z2**2 + 13*z1**3
             + 17*z1**2*z2 + 19*z1*z2**2 + 23*z2**3)
    results.append(check_example(
        "Ternary cubic metric: repeated factor and tangent conics",
        [(z0, z1, z2)], [(A, 1), (B, 2)], cubic, gram, 3, 13))
    output = {
        "arithmetic": "Exact rational Groebner bases",
        "sympy_version": sp.__version__,
        "warning": "Finite stress checks, not a proof of the universal theorem",
        "examples": results,
        "non_morse_auxiliary_hessian_rank": 1,
        "non_morse_auxiliary_scheme_length": 3,
        "all_checks": "PASS",
    }
    Path(__file__).with_name("critical_examples.json").write_text(
        json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print("PASS: all exact critical-scheme and projective-boundary checks")


if __name__ == "__main__":
    try:
        main()
    except (VerificationFailure, sp.PolynomialError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
