"""Rebuild the finite cover and verify every exclusion and upper certificate.

Run everything: python code/verify_all.py
Individual stages are available for resource-limited execution; see README.md.
No network, floating-point optimization, or commercial solver is used.
"""
from __future__ import annotations
import argparse
from collections import Counter
import json
from pathlib import Path
import platform
import subprocess
import sys
import time
import numpy as np
import numba
import sympy
from geometry import enumerate_spheres, enumerate_cycles, selected_patterns
from algebra import IncidenceTest
from regular_polygon import exact_expressions, upper_bound
from verify_exact import verify, verify_file, doubled_entry

ROOT = Path(__file__).resolve().parents[1]
PRIMES = {17: (103, 137), 18: (109, 163), 19: (191, 229)}
COUNTS = {17: 6147, 18: 449, 19: 14}


def write_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def freeze_or_compare(path: Path, value, refresh: bool) -> None:
    if refresh:
        write_json(path, value)
    elif read_json(path) != value:
        raise AssertionError(f"Regenerated data differ: {path}")


def check_geometry(out: Path, refresh: bool = False) -> None:
    spheres = enumerate_spheres()
    freeze_or_compare(ROOT / "data" / "spheres8.json", spheres, refresh)
    cycles, geometry = enumerate_cycles(spheres)
    freeze_or_compare(ROOT / "data" / "shadow_cycles.json", cycles, refresh)
    for n in PRIMES:
        patterns = selected_patterns(cycles, n)
        if len(patterns) != COUNTS[n]:
            raise AssertionError("Unexpected selected-pattern count")
        freeze_or_compare(ROOT / "data" / f"patterns_n{n}.json", patterns, refresh)
    write_json(out / "geometry.json", geometry)
    print("GEOMETRY PASSED", json.dumps({k: v for k, v in geometry.items() if k != "per_sphere"}), flush=True)


def algebra_summary(n: int, prime: int, records: list[dict]) -> dict:
    pass_id = PRIMES[n].index(prime)
    gauge = [0, 1, 2] if pass_id == 0 else [2, 7, 13]
    patterns = read_json(ROOT / "data" / f"patterns_n{n}.json")
    if len(records) != COUNTS[n] or len(patterns) != COUNTS[n]:
        raise AssertionError("Incomplete pattern records")
    for i, (record, pattern) in enumerate(zip(records, patterns)):
        cycle = pattern["cycle"]
        pairs = [[a, b] for a in range(n) for b in range(a + 1, n)
                 if cycle[a] ^ cycle[b] == 255]
        ell = record["nullity_mod_prime"]
        if not (record["pattern_index"] == i and record["n"] == n
                and record["prime"] == prime and record["gauge"] == gauge
                and record["reduced_rows"] == bool(pass_id)
                and record["complementary_pairs"] == pairs
                and record["quadratic_rank"] == record["quadratic_target"]
                == ell * (ell + 1) // 2 - len(pairs)
                and record["excluded_as_a_bounded_lift"]):
            raise AssertionError(f"Inconsistent exclusion record: n={n}, p={prime}, index={i}")
    return {"n": n, "prime": prime, "root": records[0]["root"],
            "gauge": gauge, "reduced_rows": bool(pass_id),
            "patterns": len(records), "excluded": len(records),
            "max_complementary_pairs": max(len(x["complementary_pairs"]) for x in records),
            "nullity_minus_pairs": dict(sorted(Counter(
                x["nullity_mod_prime"] - len(x["complementary_pairs"])
                for x in records).items()))}


def check_algebra(n: int, prime: int, out: Path) -> None:
    if n not in PRIMES or prime not in PRIMES[n]:
        raise ValueError("Unsupported n/prime pair; see README.md")
    pass_id = PRIMES[n].index(prime)
    gauge = (0, 1, 2) if pass_id == 0 else (2, 7, 13)
    tester = IncidenceTest(n, prime, gauge)
    records = []
    patterns = read_json(ROOT / "data" / f"patterns_n{n}.json")
    for i, pattern in enumerate(patterns):
        result = tester.check(pattern["cycle"], reduced_rows=bool(pass_id))
        result["pattern_index"] = i
        if not result["excluded_as_a_bounded_lift"]:
            raise AssertionError(f"Unexcluded pattern n={n}, p={prime}, index={i}: {result}")
        records.append(result)
        if (i + 1) % 2000 == 0:
            print(f"ALGEBRA n={n} p={prime}: {i+1}/{len(patterns)} verified", flush=True)
    summary = algebra_summary(n, prime, records)
    write_json(out / f"algebra_n{n}_p{prime}.json", records)
    print("ALGEBRA PASSED", json.dumps(summary), flush=True)


def exact_control_ranks() -> tuple[int, int]:
    """Ordinary ranks over Q[x]/(x^32+1), the 64th cyclotomic field."""
    from sympy.polys.matrices import DomainMatrix
    x = sympy.symbols("x")
    field = sympy.QQ.alg_field_from_poly(sympy.Poly(x**32 + 1, x), alias="alpha")
    ranks = []
    for matrix in exact_expressions(16):
        rows = [[sum((field.convert(c) * field.unit**k
                     for k, c in doubled_entry(e, 16).items()), field.zero)
                 for e in row] for row in matrix]
        ranks.append(DomainMatrix(rows, (len(matrix), len(matrix[0])), field).rank())
    return tuple(ranks)


def check_upper_and_control(out: Path, refresh: bool = False) -> None:
    # A known rank-eight factorization of S_16 gives a feasible Q_H lift.
    _, h = exact_expressions(16)
    def iszero(e):
        return e.kind == "zero" or (e.kind == "c" and e.angle % 16 in (0, 15))
    masks = [sum(1 << i for i in range(8) if iszero(h[i][j])) for j in range(16)]
    control = IncidenceTest(16, 97).check(masks)
    control["active_masks"] = masks
    p, q = exact_control_ranks()
    if (p, q) != (6, 5):
        raise AssertionError("The n=16 control does not have the claimed factor ranks")
    control["ordinary_rank_W_exact"] = p
    control["ordinary_rank_H_exact"] = q
    if control["excluded_as_a_bounded_lift"]:
        raise AssertionError("Known feasible n=16 control was incorrectly excluded")
    write_json(out / "n16_positive_control.json", control)
    results = []
    for n in range(17, 21):
        w, h = exact_expressions(n)
        certificate = {"format": "NR01-exact-factorization-v1", "n": n,
            "inner_dimension": upper_bound(n),
            "W": [[[e.kind, e.angle] for e in row] for row in w],
            "H": [[[e.kind, e.angle] for e in row] for row in h]}
        path = ROOT / "data" / "upper" / f"n{n}_rank9.json"
        freeze_or_compare(path, certificate, refresh)
        results.append(verify_file(str(path)))
    for n in list(range(3, 17)) + list(range(21, 25)) + list(range(43, 49)):
        results.append(verify(n))
    write_json(out / "upper_checks.json", results)
    print("UPPER AND CONTROL PASSED", json.dumps({"upper_matrices": len(results),
        "entry_identities": sum(x["entries_checked"] for x in results),
        "n16_control_excluded": False}), flush=True)


def summarize(out: Path) -> dict:
    """Validate completeness of existing outputs; this is not an arithmetic rerun."""
    geometry = read_json(out / "geometry.json")
    summaries = [algebra_summary(n, p, read_json(out / f"algebra_n{n}_p{p}.json"))
                 for n in PRIMES for p in PRIMES[n]]
    upper = read_json(out / "upper_checks.json")
    control = read_json(out / "n16_positive_control.json")
    if len(upper) != 28 or control["excluded_as_a_bounded_lift"]:
        raise AssertionError("Upper checks or positive control incomplete")
    summary = {"scope": "Finite-case computer-assisted proof draft; universal NR-01 remains partial",
        "new_exact_ranks": {str(n): 9 for n in range(17, 21)},
        "geometry": {k: v for k, v in geometry.items() if k != "per_sphere"},
        "algebra": summaries, "algebra_checks_total": sum(x["patterns"] for x in summaries),
        "upper_matrices": len(upper), "upper_entry_identities": sum(x["entries_checked"] for x in upper),
        "n16_control_excluded": False, "all_stage_records_passed": True,
        "environment": {"python": platform.python_version(), "numpy": np.__version__,
                        "numba": numba.__version__, "sympy": sympy.__version__}}
    write_json(out / "summary.json", summary)
    print("COMPLETE OUTPUT SET", json.dumps(summary), flush=True)
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", choices=("all", "geometry", "algebra", "upper", "summary"), default="all")
    parser.add_argument("--n", type=int, help="Required for the algebra-only stage")
    parser.add_argument("--prime", type=int, help="Required for the algebra-only stage")
    parser.add_argument("--refresh-data", action="store_true", help="Deliberately replace frozen data")
    parser.add_argument("--output", type=Path, default=ROOT / "checks" / "latest")
    args = parser.parse_args()
    if args.stage == "algebra" and (args.n not in PRIMES or args.prime not in PRIMES.get(args.n, ())):
        parser.error("--stage algebra requires an allowed --n and --prime pair")
    if args.stage != "algebra" and (args.n is not None or args.prime is not None):
        parser.error("--n and --prime apply only to --stage algebra")
    started = time.perf_counter()
    if args.stage == "all":
        # Bound memory growth and isolate each exact-arithmetic configuration.
        # This executes the same stages exposed by the documented CLI.
        jobs = [["geometry"]]
        jobs += [["algebra", "--n", str(n), "--prime", str(p)]
                 for n in PRIMES for p in PRIMES[n]]
        jobs += [["upper"], ["summary"]]
        for job in jobs:
            command = [sys.executable, str(Path(__file__).resolve()),
                       "--stage"] + job + ["--output", str(args.output)]
            if args.refresh_data and job[0] in ("geometry", "upper"):
                command.append("--refresh-data")
            subprocess.run(command, check=True)
        print(f"All stages passed ({time.perf_counter()-started:.3f} seconds in this run)", flush=True)
        return
    if args.stage == "geometry":
        check_geometry(args.output, args.refresh_data)
    if args.stage == "algebra":
        check_algebra(args.n, args.prime, args.output)
    if args.stage == "upper":
        check_upper_and_control(args.output, args.refresh_data)
    if args.stage == "summary":
        summarize(args.output)
    print(f"Stage {args.stage}: success ({time.perf_counter()-started:.3f} seconds in this run)", flush=True)


if __name__ == "__main__":
    main()
