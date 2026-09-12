#!/usr/bin/env python3
"""Exact arithmetic checks for TR-27. The universal lower bound is in solution.pdf.

Run: python verify.py
Requires Python 3.10+ and SymPy. No network, random numbers, or floating point.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import sympy as sp


def require(condition: bool, description: str) -> None:
    if not condition:
        raise AssertionError(description)
    print(f"PASS: {description}")


def main() -> None:
    r, m = 3, 2
    D = r**m + r
    t = sp.Symbol("t")
    J = [0, *range(2, D + 1)]
    S = [sum(a**j for a in range(1, r + 1)) for j in range(D + 1)]
    curve = lambda a: sp.Matrix([a**j for j in range(D + 1)])
    e1 = sp.eye(D + 1)[:, 1]
    b = sum((curve(a) for a in range(1, r + 1)), sp.zeros(D + 1, 1))
    z = e1 - b
    P = sp.zeros(D, D + 1)
    for row, j in enumerate(J):
        P[row, j] = 5
        P[row, 1] = -S[j]
    require(P.rank() == D, "the quotient matrix has rank 12")
    require(P * z == sp.zeros(D, 1), "the center vector is in the quotient kernel")
    require(P.nullspace() == [z / z[-1]], "the kernel is exactly the center line")
    g = P * curve(t)
    v = P * e1
    require(g == sp.Matrix([5*t**j - S[j]*t for j in J]), "the displayed affine parametrization")
    require(g.diff(t).subs(t, 0) == v, "the tangent coefficient is the target vector")
    summands = [g.subs(t, a) for a in range(1, r + 1)]
    require(sum(summands, sp.zeros(D, 1)) == v, "the three-term target decomposition")
    nine = sum((sp.kronecker_product(a, b) for a in summands for b in summands), sp.zeros(D*D, 1))
    require(nine == sp.kronecker_product(v, v), "the nine-term tensor-square decomposition")
    require(sp.Matrix.hstack(*summands).rank() == r, "the three displayed points are independent")
    require(g[0] == 5-3*t and g[1].subs(t, sp.Rational(5,3)) == -sp.Rational(85,9),
            "no finite base point (the first two coordinates cannot vanish together)")
    require(g[-1].coeff(t, D) == 5, "no base point at infinity")
    H = sp.Matrix(r+2, r+2, lambda i,j: z[i+j])
    u = lambda a: sp.Matrix([a**j for j in range(r+2)])
    B = sp.Matrix.hstack(u(0), u(t).diff(t).subs(t,0), *(u(a) for a in range(1,r+1)))
    M = sp.diag(sp.Matrix([[0,1],[1,0]]), -sp.eye(r))
    require(H == B*M*B.T, "the exact confluent-Vandermonde Hankel factorization")
    require(B.det() == 72 and H.det() == 5184 and H.rank() == 5,
            "det(B)=72, det(H)=5184, and rank(H)=5")
    # The polynomial annihilator proof includes finite parameters, 0, and infinity.
    for include_zero, include_infinity in [(False,False),(True,False),(False,True),(True,True)]:
        finite_nonzero = list(range(1, D - int(include_zero) - int(include_infinity)))
        f = sp.Poly(t*sp.prod(t-a for a in finite_nonzero), t)
        ell = len(finite_nonzero) + int(include_zero) + int(include_infinity)
        require(ell == D-1 and f.degree() <= D-int(include_infinity)
                and f.diff().eval(0) != 0 and all(f.eval(a) == 0 for a in finite_nonzero),
                f"annihilator example with zero={include_zero}, infinity={include_infinity}")
    require([j for j in range(D+1) if (j-1) % D == 0] == [1],
            "roots-of-unity extraction for tangent rank upper bound")
    for k in range(1, 51):
        L = k*(D-1)+1
        require([j for j in range(k,k*D+1) if (j-k)%L == 0] == [k],
                f"eventual-saving coefficient extraction, power {k}")
    require((13*(D-1)+1)*2**13 == 1179648 < 3**13 == 1594323,
            "the eventual upper bound is strictly smaller at power 13")
    require(all(2*r-1 <= r**m-1 and r**k-1 <= r**m-1 for k in range(1,m+1)),
            "the independence thresholds needed in the proof")
    result = {
        "r":r,"m":m,"D":D,"coordinate_indices":J,
        "center_vector":[int(x) for x in z],
        "target_vector":[int(x) for x in v],
        "rank_three_summands":[[int(x) for x in a] for a in summands],
        "center_hankel_determinant":int(H.det()),
        "claimed_ranks":{"border_rank":2,"rank":3,"tensor_square_rank":9},
        "warning":"The rank lower bounds are proved in solution.pdf, not by finite tests."
    }
    Path(__file__).with_name("coordinates.json").write_text(json.dumps(result,indent=2)+"\n", encoding="utf-8")
    print(f"All exact checks passed. Python {sys.version.split()[0]}; SymPy {sp.__version__}.")
    print("These checks supplement, and do not replace, the universal mathematical proof.")


if __name__ == "__main__":
    main()
