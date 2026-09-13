"""Exact verification in Z[x]/(x^(2n)+1), using only integer arithmetic.

Set x=exp(pi*i/(2n)). Every supported entry e has 2e represented
by an integer polynomial in x. Verify (2W)(2H)=4S in the quotient ring.
No floating-point tolerance, symbolic simplifier, or external CAS is used.
Nonnegativity follows separately from the angle-index checks below.
"""
from __future__ import annotations
import argparse
import json
import time
from regular_polygon import Entry, exact_expressions, upper_bound

Poly = dict[int, int]


def add_term(p: Poly, exponent: int, coefficient: int, n: int) -> None:
    q, r = divmod(exponent, 2*n)
    coefficient *= -1 if q % 2 else 1
    value = p.get(r, 0) + coefficient
    if value:
        p[r] = value
    else:
        p.pop(r, None)


def doubled_entry(e: Entry, n: int) -> Poly:
    """Exact integer polynomial for 2e."""
    p: Poly = {}
    if e.kind == "zero":
        return p
    if e.kind == "one":
        return {0: 2}
    if e.kind in ("sin", "2sin"):
        a = e.angle
        scale = 2 if e.kind == "2sin" else 1
        add_term(p, 2*a-n, scale, n)
        add_term(p, -2*a-n, -scale, n)
        return p
    if e.kind == "c":
        a = e.angle
        for exponent, coefficient in ((2, 1), (-2, 1),
                                      (4*a+2, -1), (-4*a-2, -1)):
            add_term(p, exponent, coefficient, n)
        return p
    raise ValueError(e.kind)


def add_product(target: Poly, p: Poly, q: Poly, n: int) -> None:
    for a, x in p.items():
        for b, y in q.items():
            add_term(target, a+b, x*y, n)


def nonnegative_by_angle(e: Entry, n: int) -> bool:
    if e.kind in ("zero", "one"):
        return True
    if e.kind in ("sin", "2sin"):
        return 0 < e.angle < n
    if e.kind == "c":
        return 0 <= e.angle < n
    return False


def verify_factors(n: int, W: list[list[Entry]], H: list[list[Entry]]) -> dict:
    """Check the supplied factors, not only factors produced by our constructor."""
    t0 = time.perf_counter()
    r = len(H)
    if len(W) != n or any(len(row) != r for row in W):
        raise AssertionError("W shape mismatch")
    if any(len(row) != n for row in H):
        raise AssertionError("H shape mismatch")
    if not all(nonnegative_by_angle(e, n) for row in W+H for e in row):
        raise AssertionError("Nonnegativity/angle certificate failed")
    WP = [[doubled_entry(e, n) for e in row] for row in W]
    HP = [[doubled_entry(e, n) for e in row] for row in H]
    for i in range(n):
        for j in range(n):
            residual: Poly = {}
            for a in range(r):
                add_product(residual, WP[i][a], HP[a][j], n)
            twice_slack = doubled_entry(Entry("c", (i-j) % n), n)
            for exponent, coefficient in twice_slack.items():
                add_term(residual, exponent, -2*coefficient, n)
            if residual:
                raise AssertionError(f"Exact residual at ({i},{j}): {residual}")
    return dict(n=n, factors=r, target_upper=upper_bound(n),
                exact_polynomial_identity=True, exact_angle_nonnegativity=True,
                entries_checked=n*n, seconds=time.perf_counter()-t0)


def verify(n: int) -> dict:
    return verify_factors(n, *exact_expressions(n))


def verify_file(filename: str) -> dict:
    with open(filename, encoding="utf-8") as f:
        data = json.load(f)
    if data.get("format") != "NR01-exact-factorization-v1":
        raise ValueError("Unrecognized certificate format")
    n = data["n"]
    # Require real integer parameters before using the algebraic certificate.
    if isinstance(n, bool) or not isinstance(n, int) or n < 3:
        raise ValueError("Invalid n")
    def load(matrix):
        result = []
        for row in matrix:
            entries = []
            for kind, angle in row:
                if kind not in ("zero", "one", "sin", "2sin", "c"):
                    raise ValueError("Invalid expression kind")
                if isinstance(angle, bool) or not isinstance(angle, int):
                    raise ValueError("Invalid angle index")
                entries.append(Entry(kind, angle))
            result.append(entries)
        return result
    W, H = load(data["W"]), load(data["H"])
    if data.get("inner_dimension") != len(H):
        raise ValueError("Declared inner dimension does not match H")
    return verify_factors(n, W, H)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", nargs="*", type=int)
    parser.add_argument("--through", type=int)
    parser.add_argument("--certificate", type=str, help="verify a supplied exact factor JSON")
    parser.add_argument("--json", type=str)
    args = parser.parse_args()
    if args.certificate:
        result = verify_file(args.certificate)
        print(json.dumps(result, indent=2))
        if args.json:
            with open(args.json, "w", encoding="utf-8") as f:
                json.dump(result, f, indent=2)
                f.write("\n")
        return
    if args.through is not None and args.through < 3:
        parser.error("--through must be at least 3")
    ns = args.n or [3,4,5,6,7,8,9,12,13,16,17,18,20,24,25,32,33,48,49,64,65]
    if args.through is not None:
        ns = list(range(3, args.through+1))
    results = []
    for n in ns:
        result = verify(n)
        results.append(result)
        print(json.dumps(result), flush=True)
    if args.json:
        with open(args.json, "w", encoding="utf-8") as f:
            json.dump(results, f, indent=2)
            f.write("\n")


if __name__ == "__main__":
    main()
