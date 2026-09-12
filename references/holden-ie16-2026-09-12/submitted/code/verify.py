#!/usr/bin/env python3
"""Exact-arithmetic verification of the IE-16 nine-point counterexample.

Python 3.10+; standard library only. No floating-point optimization is used.
Run from any directory. The optional output directory receives a complete
126-subset certificate and a human-readable verification report.

All nodes belong to Q(omega), omega^2 + omega + 1 = 0. Their squared
absolute values, all squared Lagrange weights, and the proposed optimal
residual value are rational. Square roots are enclosed by integer arithmetic.
The positive weighted orthogonality certificate proves global optimality,
not merely feasibility of a proposed residual polynomial.
"""
from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
from typing import Iterable


class VerificationError(RuntimeError):
    """Raised if any part of the mathematical certificate fails."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


@dataclass(frozen=True)
class Eisenstein:
    """The exact number a + b*omega, where omega = (-1+i*sqrt(3))/2."""
    a: F
    b: F

    def __add__(self, other: Eisenstein) -> Eisenstein:
        return Eisenstein(self.a + other.a, self.b + other.b)

    def __sub__(self, other: Eisenstein) -> Eisenstein:
        return Eisenstein(self.a - other.a, self.b - other.b)

    def __mul__(self, other: Eisenstein) -> Eisenstein:
        return Eisenstein(self.a * other.a - self.b * other.b,
                          self.a * other.b + self.b * other.a - self.b * other.b)

    def scale(self, factor: F) -> Eisenstein:
        return Eisenstein(factor * self.a, factor * self.b)

    def conjugate(self) -> Eisenstein:
        return Eisenstein(self.a - self.b, -self.b)

    def norm_squared(self) -> F:
        return self.a * self.a - self.a * self.b + self.b * self.b

    def power(self, exponent: int) -> Eisenstein:
        require(exponent >= 0, "Only nonnegative integer powers are supported.")
        result = ONE
        base = self
        while exponent:
            if exponent & 1:
                result = result * base
            base = base * base
            exponent //= 2
        return result


ZERO = Eisenstein(F(0), F(0))
ONE = Eisenstein(F(1), F(0))
OMEGA = Eisenstein(F(0), F(1))
ROOTS = (ONE, OMEGA, Eisenstein(F(-1), F(-1)))


def exact_sum(values: Iterable[Eisenstein]) -> Eisenstein:
    result = ZERO
    for value in values:
        result = result + value
    return result


def fraction_string(value: F) -> str:
    return f"{value.numerator}/{value.denominator}"


def decimal_string(value: F, digits: int = 24) -> str:
    with localcontext() as ctx:
        ctx.prec = digits + 30
        number = Decimal(value.numerator) / Decimal(value.denominator)
        return f"{number:.{digits}f}"


def sqrt_interval(value: F, digits: int) -> tuple[F, F]:
    """Return certified decimal-grid lower/upper bounds for sqrt(value)."""
    require(value >= 0, "A square root argument is negative.")
    scale = 10 ** digits
    integer = math.isqrt((value.numerator * scale * scale) // value.denominator)
    lower = F(integer, scale)
    upper = F(integer + 1, scale)
    require(lower * lower <= value < upper * upper,
            "Integer square-root enclosure failed.")
    return lower, upper


def arctan_interval(x: F, terms: int) -> tuple[F, F]:
    """Alternating-series enclosure for arctan(x), 0 < x < 1."""
    require(0 < x < 1 and terms > 0, "Invalid arctangent parameters.")
    partial = sum(((-1) ** j) * x ** (2*j + 1) / (2*j + 1)
                  for j in range(terms))
    next_term = ((-1) ** terms) * x ** (2*terms + 1) / (2*terms + 1)
    return min(partial, partial + next_term), max(partial, partial + next_term)


def pi_interval(terms: int = 70) -> tuple[F, F]:
    """Machin's identity and rational alternating-series bounds.

    tan(4*atan(1/5)-atan(1/239))=1, and the angle is in (0,pi/2).
    Consequently pi=16*atan(1/5)-4*atan(1/239).
    """
    t2 = 2 * F(1, 5) / (1 - F(1, 5)**2)
    t4 = 2 * t2 / (1 - t2**2)
    require((t4 - F(1, 239)) / (1 + t4 * F(1, 239)) == 1,
            "Machin tangent identity failed.")
    a0, a1 = arctan_interval(F(1, 5), terms)
    b0, b1 = arctan_interval(F(1, 239), terms)
    return 16*a0 - 4*b1, 16*a1 - 4*b0


def verify(digits: int, output: Path) -> str:
    require(20 <= digits <= 200, "Use between 20 and 200 square-root digits.")
    eps = F(1, 1000)
    D = 1 + eps + 3*eps**2 + eps**3 + eps**4
    H = 1 - 3*eps + eps**2 - 3*eps**3 + eps**4
    Q = (1 + eps)**2 * (1 + eps + eps**2)
    c = -(1 + eps) / D
    M = 3 * eps * (1 + eps + eps**2) / D
    mu = (H / (3*D), Q / (3*D), Q / (3*D))

    nodes = [ROOTS[a] + ROOTS[b].scale(eps) for a in range(3) for b in range(3)]
    labels = [(a, b) for a in range(3) for b in range(3)]
    weights = [mu[(b-a) % 3] / 3 for a, b in labels]
    residuals = [ONE + z.power(3).scale(c) for z in nodes]

    require(len(set(nodes)) == 9, "The nodes are not all distinct.")
    require(all(z.norm_squared() > 0 for z in nodes), "A node is zero.")
    require(all(w > 0 for w in weights), "A certificate weight is not positive.")
    require(sum(weights) == 1, "The certificate weights do not sum to one.")
    require(all(p.norm_squared() == M*M for p in residuals),
            "The proposed residual does not have constant modulus M.")
    for power in range(1, 5):
        moment = exact_sum((p.conjugate() * z.power(power)).scale(w)
                           for p, z, w in zip(residuals, nodes, weights))
        require(moment == ZERO, f"Weighted orthogonality fails at power {power}.")
    # These identities imply min_p sum_j w_j |p(z_j)|^2 = M^2 for p(0)=1,
    # deg(p)<=4. Since p_star attains modulus M at every node, M_4(L)=M.

    min_distance_squared = min((a-b).norm_squared() for a, b in combinations(nodes, 2))
    require(min_distance_squared == 3*eps*eps, "Unexpected minimum separation.")
    pi_lo, pi_hi = pi_interval(max(70, digits + 10))
    require(pi_lo > F(31, 10), "The required elementary lower bound for pi failed.")
    constant_upper = 4 / pi_lo

    records = []
    minimum_N_lower = None
    minimum_N_upper = None
    profile_counts: dict[str, int] = {}
    for subset in combinations(range(9), 5):
        lower = F(0)
        upper = F(0)
        squared_weights = []
        for j in subset:
            ratio_squared = F(1)
            for h in subset:
                if h != j:
                    ratio_squared *= nodes[h].norm_squared() / (nodes[j]-nodes[h]).norm_squared()
            squared_weights.append(fraction_string(ratio_squared))
            lo, hi = sqrt_interval(ratio_squared, digits)
            lower += lo
            upper += hi
        require(lower > 0, "A Lagrange norm has a nonpositive lower bound.")
        M_lower, M_upper = 1/upper, 1/lower
        require(M_upper < F(23, 10000), "A subset violates the advertised elementary bound.")
        require(M > constant_upper * M_upper,
                "A subset does not certify the conjecture's strict reversal.")
        minimum_N_lower = lower if minimum_N_lower is None else min(minimum_N_lower, lower)
        minimum_N_upper = upper if minimum_N_upper is None else min(minimum_N_upper, upper)
        occupancy = [sum(labels[j][0] == a for j in subset) for a in range(3)]
        profile = ",".join(map(str, sorted(occupancy, reverse=True)))
        profile_counts[profile] = profile_counts.get(profile, 0) + 1
        records.append({
            "indices_zero_based": list(subset),
            "node_labels": [list(labels[j]) for j in subset],
            "cluster_occupancy": occupancy,
            "lagrange_weights_squared": squared_weights,
            "sum_abs_lagrange_lower": fraction_string(lower),
            "sum_abs_lagrange_upper": fraction_string(upper),
            "M_subset_lower": fraction_string(M_lower),
            "M_subset_upper": fraction_string(M_upper),
            "strict_violation_certified": True,
        })

    require(len(records) == math.comb(9, 5) == 126, "Not all subsets were checked.")
    require(profile_counts == {"3,2,0": 18, "3,1,1": 27, "2,2,1": 81},
            "The cluster-profile count is incorrect.")
    require(minimum_N_lower is not None and minimum_N_upper is not None,
            "No subset minima were generated.")
    ratio_lower = M * minimum_N_lower
    ratio_upper = M * minimum_N_upper
    best_subset_lower = 1/minimum_N_upper
    best_subset_upper = 1/minimum_N_lower
    margin_lower = M - constant_upper * best_subset_upper
    require(ratio_lower > F(13, 10) > constant_upper, "The main strict inequality failed.")

    # Independent checks of the simple uniform inequalities used in the proof.
    coarse_bound = eps * (9 + 36*eps + 36*eps**2 + 16*eps**3) / (4*(1-eps)**4)
    require(M > F(299, 100)*eps, "The elementary full-set lower bound failed.")
    require(coarse_bound < F(23, 10)*eps, "The elementary subset upper bound failed.")
    require(4*eps < 3, "The three-point-cluster comparison failed.")

    certificate = {
        "problem": "IE-16",
        "epsilon": fraction_string(eps),
        "degree": 4,
        "number_of_nodes": 9,
        "node_convention": "z_(a,b)=omega^a+epsilon*omega^b; index=3*a+b; omega^2+omega+1=0",
        "nodes_in_Q_omega": [{"index": j, "label": list(labels[j]),
                              "a": fraction_string(z.a), "b": fraction_string(z.b)}
                             for j, z in enumerate(nodes)],
        "residual_polynomial": {"constant": "1/1", "z_cubed": fraction_string(c)},
        "full_set_M_exact": fraction_string(M),
        "positive_weights": [fraction_string(w) for w in weights],
        "weighted_moments_1_through_4_exactly_zero": True,
        "square_root_decimal_grid_digits": digits,
        "pi_lower": fraction_string(pi_lo),
        "pi_upper": fraction_string(pi_hi),
        "subset_profile_counts": profile_counts,
        "max_subset_M_lower": fraction_string(best_subset_lower),
        "max_subset_M_upper": fraction_string(best_subset_upper),
        "ratio_lower": fraction_string(ratio_lower),
        "ratio_upper": fraction_string(ratio_upper),
        "violation_margin_lower": fraction_string(margin_lower),
        "all_subsets": records,
    }
    output.mkdir(parents=True, exist_ok=True)
    (output / "all_subset_certificate.json").write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8")

    report = "\n".join([
        "IE-16 EXACT-ARITHMETIC VERIFICATION: PASS",
        "",
        "Arithmetic: fractions.Fraction and math.isqrt; no floating-point solver.",
        "Nodes: 9 distinct, nonzero elements of Q(omega). Degree: 4.",
        "Positive weights sum exactly to 1.",
        "All nine proposed residual moduli squared equal M^2 exactly.",
        "Weighted residual orthogonality for z,z^2,z^3,z^4 holds exactly.",
        "Therefore the displayed residual polynomial is globally minimax.",
        "",
        f"M_4(L) exactly = {fraction_string(M)}",
        f"M_4(L) = {decimal_string(M)}",
        f"max subset M lower (rounded display) = {decimal_string(best_subset_lower)}",
        f"max subset M upper (rounded display) = {decimal_string(best_subset_upper)}",
        f"ratio lower (rounded display) = {decimal_string(ratio_lower)}",
        f"ratio upper (rounded display) = {decimal_string(ratio_upper)}",
        f"4/pi upper (rounded display) = {decimal_string(constant_upper)}",
        f"strict violation margin lower (rounded display) = {decimal_string(margin_lower)}",
        "",
        "All 126 five-point subsets individually certify strict violation.",
        "Cluster profiles: (3,2,0): 18; (3,1,1): 27; (2,2,1): 81.",
        "Elementary proof bounds M_4(L)>0.00299 and every subset M<0.0023: PASS.",
        "The exact rational endpoints, not the rounded displays above, are the certificate.",
        "This computation verifies the finite witness; the unbounded-family theorem",
        "is proved analytically in the accompanying manuscript, not by enumeration.",
    ]) + "\n"
    (output / "verification_report.txt").write_text(report, encoding="utf-8")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--digits", type=int, default=60,
                        help="Decimal-grid precision for exact square-root intervals (20..200).")
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "certificates")
    args = parser.parse_args()
    print(verify(args.digits, args.output), end="")


if __name__ == "__main__":
    main()
