#!/usr/bin/env python3
"""Exact, implicit Vandermonde decompositions for rational complex Hankel tensors.

The output describes a sum over the distinct complex roots beta of P:
    H = sum_beta U(beta)/P'(beta) * f(beta) ** tensor_power(m).
P, U and the coordinates of f have rational coefficients. No numerical root
approximation is used. The certificate can be checked by polynomial remainders.
This decomposition is ordinary/symmetric optimal when its length equals the
rank formula; an optimal local construction is described in the manuscript.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict
from math import comb
import json
from pathlib import Path
from typing import Sequence

import sympy as sp

from hankel_rank import RationalInput, _rational, exact_hankel_rank


def coefficients(poly: sp.Poly, length: int | None = None) -> list[str]:
    length = length if length is not None else max(1, int(poly.degree()) + 1)
    return [str(poly.nth(i)) for i in range(length)]


def binary_certificate(order: int, dimension: int,
                       moments: Sequence[RationalInput]) -> dict:
    """Return and internally verify an exact algebraic-root decomposition."""
    rank_result = exact_hankel_rank(order, dimension, moments)
    h = [_rational(x) for x in moments]
    D = order * (dimension - 1)
    if not rank_result.ordinary_rank:
        return {"zero_tensor": True, "summands": 0, "ranks": asdict(rank_result)}
    r, q = rank_result.apolar_degree, dimension - 1
    t = sp.Symbol("t")

    # The shear X -> X + cY, Y -> Y moves every projective support point
    # away from infinity for some integer c. In the balanced case choose
    # a kernel element with nonzero final coefficient, rather than assuming
    # that an arbitrary first nullspace vector is monic.
    for c in range(r + 2):
        hp = [sum(comb(D-j, a) * c**a * h[j+a] for a in range(D-j+1))
              for j in range(D+1)]
        C = sp.Matrix(D-r+1, r+1, lambda j, i: hp[j+i])
        monic_vectors = [b / b[r] for b in C.nullspace() if b[r] != 0]
        if monic_vectors:
            g = sp.Poly(sum(monic_vectors[0][i] * t**i for i in range(r+1)),
                        t, domain=sp.QQ)
            break
    else:
        raise ArithmeticError("Failed to find a finite projective chart.")

    def top_remainder(expr, modulus: sp.Poly):
        return sp.Poly(expr, t, domain=sp.QQ).rem(modulus).nth(modulus.degree()-1)

    def functional_multiplier(modulus: sp.Poly, initial_moments):
        v = int(modulus.degree())
        pairing = sp.Matrix(v, v, lambda i, j: top_remainder(t**(i+j), modulus))
        result = pairing.inv() * sp.Matrix(initial_moments[:v])
        return sp.Poly(sum(result[i] * t**i for i in range(v)), t, domain=sp.QQ)

    pencil = None
    if sp.gcd(g, g.diff()).degree() == 0:
        P = g
    else:
        v = D-r+2
        u = functional_multiplier(g, hp)
        if sp.gcd(u, g).degree() != 0:
            raise ArithmeticError("The minimal moment functional is not Frobenius.")
        b = sp.Poly(sp.invert(u.as_expr(), g.as_expr(), t), t, domain=sp.QQ)
        delta = 0
        while b.eval(delta) == 0:
            delta += 1
        Q = sp.Poly((t-delta)**(v-r), t, domain=sp.QQ)
        # A finite set of pencil parameters produces multiple roots.
        parameter = 1
        while True:
            trial = b + parameter * g * Q
            if sp.gcd(trial, trial.diff()).degree() == 0:
                P = trial.monic()
                break
            parameter += 1
        pencil = {"b": coefficients(b), "Q": coefficients(Q),
                  "parameter": parameter}
    v = int(P.degree())
    U = functional_multiplier(P, hp)
    assert sp.gcd(P, P.diff()).degree() == 0
    for j in range(D+1):
        if top_remainder(U.as_expr() * t**j, P) != hp[j]:
            raise ArithmeticError(f"Moment certificate failed at index {j}.")

    # H' = (M^T)^{tensor m} H, hence factors for H are M^{-T} v(beta).
    M = sp.Matrix(dimension, dimension,
                  lambda k, i: comb(q-i, k-i) * c**(k-i) if k >= i else 0)
    factors = M.T.inv() * sp.Matrix([t**i for i in range(dimension)])
    factor_polynomials = [sp.Poly(f, t, domain=sp.QQ) for f in factors]
    assert v == rank_result.vandermonde_rank
    assert sp.gcd(P, U).degree() == 0  # no vanishing root weights at minimal V rank
    return {
        "zero_tensor": False,
        "order": order, "dimension": dimension,
        "original_moments": [str(x) for x in h],
        "ranks": asdict(rank_result),
        "summands": v,
        "optimal_ordinary_and_symmetric": v == rank_result.ordinary_rank,
        "coefficient_order": "ascending powers of t",
        "decomposition": "Sum over P(beta)=0 of U(beta)/P'(beta) * f(beta)^tensor(m)",
        "P": coefficients(P), "U": coefficients(U),
        "factor_polynomials": [coefficients(f, dimension) for f in factor_polynomials],
        "finite_chart_shear": c,
        "finite_chart_moments": [str(x) for x in hp],
        "finite_chart_minimal_apolar": coefficients(g),
        "pencil": pencil,
        "verification": "All transformed moments checked by exact rational polynomial remainders",
    }


def verify_certificate(certificate: dict, full_tensor: bool = False) -> dict:
    """Independently reconstruct moments, or every original tensor entry.

    This checks the decomposition certificate, not the universal rank lower bound.
    """
    if not __debug__:
        raise RuntimeError("Certificate verification requires Python assertions; do not use -O.")
    from itertools import product
    if certificate.get("zero_tensor"):
        return {"zero_tensor": True, "entries_checked": 0}
    t = sp.Symbol("t")
    def poly(values):
        return sp.Poly(sum(sp.Rational(x)*t**i for i, x in enumerate(values)),
                       t, domain=sp.QQ)
    P, U = poly(certificate["P"]), poly(certificate["U"])
    v = int(P.degree())
    assert P.LC() == 1 and sp.gcd(P, P.diff()).degree() == 0
    assert sp.gcd(P, U).degree() == 0
    m, n = certificate["order"], certificate["dimension"]
    h = [sp.Rational(x) for x in certificate["original_moments"]]
    hp = [sp.Rational(x) for x in certificate["finite_chart_moments"]]
    for j, hj in enumerate(hp):
        assert (U * sp.Poly(t**j, t)).rem(P).nth(v-1) == hj
    entries = 0
    if full_tensor:
        factors = [poly(a) for a in certificate["factor_polynomials"]]
        for index in product(range(n), repeat=m):
            expr = U
            for i in index:
                expr = (expr * factors[i]).rem(P)
            assert expr.nth(v-1) == h[sum(index)], index
            entries += 1
    return {"summands": v, "moments_checked": len(hp),
            "original_tensor_entries_checked": entries,
            "arithmetic": "exact rational polynomial remainders"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", "-m", type=int, required=True)
    parser.add_argument("--dimension", "-n", type=int, required=True)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--moments")
    source.add_argument("--moments-file", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify-full-tensor", action="store_true")
    args = parser.parse_args()
    try:
        values = json.loads(args.moments_file.read_text() if args.moments_file else args.moments)
        if not isinstance(values, list):
            raise ValueError("The moments JSON must be a list")
        result = binary_certificate(args.order, args.dimension, values)
        result["independent_verification"] = verify_certificate(result, args.verify_full_tensor)
        rendered = json.dumps(result, indent=2)
    except (TypeError, ValueError, OSError) as exc:
        parser.error(str(exc))
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered+"\n")
    print(rendered)


if __name__ == "__main__":
    main()
