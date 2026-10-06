#!/usr/bin/env python3
"""Check the ordered MI-18 certificate using exact Gaussian-integer arithmetic.

This independently written, Python-standard-library checker verifies the finite
arithmetic used in solution.md.  The mathematical identities and the existence
of a suitable positive diagonal perturbation are proved in that manuscript.
No floating-point computation is used in any acceptance condition.
"""

import argparse
from decimal import Decimal, localcontext
import hashlib
import json
from math import factorial
from pathlib import Path


ZERO = (0, 0)
ONE = (1, 0)
ROW_DIGEST = "213d6aacc5262c80ca8f27ae598b3205ad759a23422eab5fd79ea73ff98aa550"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def scale(a, x):
    return a * x[0], a * x[1]


def multiply(x, y):
    return x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0]


def linear_product(coefficients, a, b):
    """Ascending coefficients of (a + b*z) times the given polynomial."""
    result = [ZERO] * (len(coefficients) + 1)
    for k, value in enumerate(coefficients):
        result[k] = add(result[k], scale(a, value))
        result[k + 1] = add(result[k + 1], multiply(b, value))
    return result


def weighted_norm(coefficients, degree):
    require(len(coefficients) <= degree + 1, "Coefficient list exceeds degree")
    return sum(
        factorial(k) * factorial(degree - k) * (x * x + y * y)
        for k, (x, y) in enumerate(coefficients)
    )


def verify(path):
    certificate = json.loads(path.read_text(encoding="utf-8"))
    rows = certificate["rows"]
    require(len(rows) == 144, "Expected exactly 144 ordered rows")
    require(all(isinstance(r, list) and len(r) == 3 for r in rows),
            "Every row must have three integer coordinates")
    require(all(type(x) is int for r in rows for x in r),
            "Every coordinate must be an integer")
    digest = hashlib.sha256(
        json.dumps(rows, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    require(digest == ROW_DIGEST, "Ordered rows differ from the published certificate")
    require(certificate["rows_sha256"] == digest, "Incorrect row digest metadata")

    n = len(rows)
    p, g, wedge = [ONE], [], []
    for j, (a, real, imag) in enumerate(rows):
        b = real, imag
        # Fixed final-order weights in the product-rule polynomial g.
        next_g = linear_product(g, a, b)
        for k, value in enumerate(p):
            next_g[k] = add(next_g[k], scale(n - 1 - 2 * j, multiply(b, value)))

        # A second recurrence, obtained directly by adjoining the new row
        # to the sum over wedges: F_(j+1) = l_j F_j + j b_j p_j - l_j p_j'.
        # This checks the g = -F identity without reusing its fixed weights.
        derivative = [scale(k, p[k]) for k in range(1, len(p))]
        next_wedge = linear_product(wedge, a, b)
        derivative_term = linear_product(derivative, a, b)
        require(len(next_wedge) == len(p) == len(derivative_term),
                "Internal polynomial-shape mismatch")
        for k, value in enumerate(p):
            next_wedge[k] = add(
                add(next_wedge[k], scale(j, multiply(b, value))),
                scale(-1, derivative_term[k]),
            )

        p, g, wedge = linear_product(p, a, b), next_g, next_wedge

    require(len(p) == 145 and len(g) == 144, "Incorrect final polynomial sizes")
    require(g[-1] == ZERO, "The degree-143 coefficient of g must vanish")
    require(wedge == [scale(-1, x) for x in g], "Wedge and weighted recurrences disagree")
    P = weighted_norm(p, n)
    S = weighted_norm(g[:-1], n - 2)
    require(P > 0, "The permanent norm must be positive")
    require(10300 * P < S < 10301 * P, "Exact rational bounds on S/P failed")
    endpoint_numerator = n * (n - 1) // 2 * P - S
    require(endpoint_numerator < -4 * P, "Negative endpoint margin failed")

    a0, u0, v0 = rows[0]
    a1, u1, v1 = rows[1]
    h01 = add((a0 * a1, 0), multiply((u0, v0), (u1, -v1)))
    require(h01 == (9795, -1288), "Off-diagonal witness failed")
    require(all(a * a + u * u + v * v > 0 for a, u, v in rows),
            "A diagonal Gram entry vanishes")

    with localcontext() as context:
        context.prec = 30
        ratio = Decimal(S) / Decimal(P)
        normalized_derivative = (Decimal(10296) - ratio) / 2
    return {
        "result": "PASS",
        "rows": n,
        "rows_sha256": digest,
        "P_decimal_digits": len(str(P)),
        "S_decimal_digits": len(str(S)),
        "P_sha256_decimal": hashlib.sha256(str(P).encode("ascii")).hexdigest(),
        "S_sha256_decimal": hashlib.sha256(str(S).encode("ascii")).hexdigest(),
        "exact_ratio_bounds": "10300 < S/P < 10301",
        "S_over_P_approximate": str(ratio),
        "endpoint_derivative_over_P_approximate": str(normalized_derivative),
        "endpoint_derivative_bound": "P'_1(H) < -2*P < 0",
        "g_degree_143_coefficient": list(g[-1]),
        "independent_wedge_recurrence": "PASS",
        "H_0_1": list(h01),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path,
                        default=Path(__file__).with_name("certificate.json"))
    arguments = parser.parse_args()
    print(json.dumps(verify(arguments.certificate), indent=2))
