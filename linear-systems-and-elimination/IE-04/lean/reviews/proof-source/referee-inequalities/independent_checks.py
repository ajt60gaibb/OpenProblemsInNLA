#!/usr/bin/env python3
"""Supplementary independent exact/source checks; never invokes Lean or Lake.

This is not a formal certificate or an asymptotic proof. The human-readable
review separately checks the generic analytic argument and all Lean sources.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import math
import os
import re
import subprocess

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "source"
AUTHOR = Path("/tmp/nla-lean-next-20260915/elimination/IE-04")
REPO = Path("/Users/georgestepaniants/Research/OpenProblemsInNLA")
BASE = "8f04b905eb2e0827b6b84f37d9d080ae1f05b202"
MATHLIB = Path("/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages/mathlib")
CHECKS = []


def sha(b):
    return hashlib.sha256(b).hexdigest()


def check(name, condition, detail=None):
    assert condition, name
    CHECKS.append({"name": name, "pass": True, "detail": detail})


def write_json(name, obj):
    target = HERE / name
    temporary = target.with_suffix(target.suffix + ".tmp")
    with temporary.open("w") as f:
        json.dump(obj, f, indent=2, ensure_ascii=False)
        f.write("\n")
        f.flush()
        os.fsync(f.fileno())
    os.replace(temporary, target)


def strip_comments(s):
    out = []
    i = 0
    depth = 0
    while i < len(s):
        if s[i:i+2] == "/-":
            depth += 1
            i += 2
        elif depth and s[i:i+2] == "-/":
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif s[i:i+2] == "--":
            j = s.find("\n", i)
            i = len(s) if j < 0 else j
        else:
            out.append(s[i])
            i += 1
    assert depth == 0
    return "".join(out)


def norm(s):
    return re.sub(r"\s+", "", strip_comments(s))


inputs = json.loads((HERE / "INPUTS.json").read_text())
for rel, expected in inputs["source_files"].items():
    b = (SOURCE / rel).read_bytes()
    check("snapshot SHA " + rel, sha(b) == expected)
    check("current author bytes " + rel, (AUTHOR / rel).read_bytes() == b)
for rel, expected in inputs["canonical_files"].items():
    b = (HERE / "canonical" / rel).read_bytes()
    actual = subprocess.run(["git", "show", f"{BASE}:{rel}"], cwd=REPO,
                            check=True, capture_output=True).stdout
    check("immutable canonical Git bytes " + rel, sha(b) == expected and actual == b)

freeze = json.loads((SOURCE / "STATEMENT-FREEZE.json").read_text())
for rel, expected in freeze["source_hashes"].items():
    check("frozen boundary " + rel, sha((SOURCE / rel).read_bytes()) == expected)
for rel, expected in freeze["reviews"].items():
    check("frozen independent review " + rel, sha(Path(rel).read_bytes()) == expected)

lean = {str(p.relative_to(SOURCE)): strip_comments(p.read_text())
        for p in SOURCE.rglob("*.lean")}
implementation = {k: v for k, v in lean.items() if k != "Challenge.lean"}
check("14 implementation-graph files including Definitions and Solution", len(implementation) == 14)
bad = {}
for rel, code in implementation.items():
    matches = re.findall(r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|run_tac|run_elab)\b", code)
    if matches:
        bad[rel] = matches
check("no proof holes/custom axioms/unsafe execution in proof sources", not bad, bad)
check("exactly 21 deliberate Challenge placeholders",
      len(re.findall(r"\bsorry\b", lean["Challenge.lean"])) == 21)

graph = {}
for rel, code in implementation.items():
    deps = []
    for module in re.findall(r"(?m)^import\s+(\S+)", code):
        check("Challenge import excluded " + rel + ":" + module, module != "Challenge")
        if module.startswith("NLA."):
            dependency = module.replace(".", "/") + ".lean"
            check("local import resolves " + rel + ":" + module, dependency in implementation)
            deps.append(dependency)
    graph[rel] = deps
seen, active = set(), set()


def visit(rel):
    assert rel not in active, ("cycle", rel)
    if rel in seen:
        return
    active.add(rel)
    for dependency in graph[rel]:
        visit(dependency)
    active.remove(rel)
    seen.add(rel)


visit("Solution.lean")
check("complete acyclic Solution import closure", seen == set(implementation))
cfg = json.loads((SOURCE / "comparator.json").read_text())
targets = cfg["theorem_names"]
challenge_names = re.findall(r"(?m)^theorem\s+(\S+)", lean["Challenge.lean"])
check("all 21 independent declarations in Comparator order",
      ["NLA.IE04." + n for n in challenge_names] == targets and len(targets) == 21)
check("standard axiom allowlist only", set(cfg["permitted_axioms"]) ==
      {"propext", "Classical.choice", "Quot.sound"})
contracts = {}
for full in targets:
    name = full.removeprefix("NLA.IE04.")
    pattern = r"(?m)^theorem\s+" + re.escape(name) + r"(?=\s|\{)([\s\S]*?)\s*:="
    expected = re.search(pattern, lean["Challenge.lean"])
    found = [(rel, m.group(1)) for rel, code in implementation.items()
             for m in re.finditer(pattern, code)]
    check("unique actual target " + name, len(found) == 1)
    rel, header = found[0]
    check("textually exact full target type " + name, norm(header) == norm(expected.group(1)))
    check("target requested kernel trust assertion " + name,
          bool(re.search(r"#assert_trust\s+kernel\s+" + re.escape(name) + r"\s", lean["Solution.lean"])))
    contracts[full] = {"source": rel, "normalized_type_sha256": sha(norm(header).encode())}

# Independently compare the complete reusable definitions, rather than trust the
# author's correspondence JSON. Declarations end at the next top-level command.
old_defs = strip_comments((HERE / "canonical/linear-systems-and-elimination/IE-05/lean/NLA/IE05/Definitions.lean").read_text())
new_defs = lean["NLA/IE04/Definitions.lean"]
reused = json.loads((SOURCE / "GENERIC-DEFINITION-REUSE.json").read_text())["definitions"]
for item in reused:
    name = item["declaration"]
    pattern = r"(?m)^def\s+" + re.escape(name) + r"(?=\s|\{)([\s\S]*?)(?=\n(?:def|abbrev|instance|theorem|end)\b|\Z)"
    old, new = re.search(pattern, old_defs), re.search(pattern, new_defs)
    check("generic GEPP definition preserved " + name,
          old is not None and new is not None and norm(old.group(1)) == norm(new.group(1)))

for short in ["Pivot", "GEPP"]:
    old = strip_comments((HERE / f"canonical/linear-systems-and-elimination/IE-05/lean/NLA/IE05/{short}.lean").read_text()).replace("NLA.IE05", "NLA.IE04")
    new = lean[f"NLA/IE04/{short}.lean"]
    if short == "GEPP":
        old = re.sub(r"(?m)^theorem orthogonalGrowthSet_bounded_proved\b[\s\S]*?(?=^#assert_trust)", "", old)
        old = re.sub(r"(?m)^#(?:assert_trust kernel|print axioms) orthogonalGrowthSet_bounded_proved\s*$", "", old)
    check("complete generic proof reuse " + short, norm(old) == norm(new))

# Closed scalar arithmetic. These rational margins also explain each uniform
# inequality used in the analytic proof rather than sampling it.
check("strict pivot gap", F(7, 8) - F(5, 8) == F(1, 4))
check("quotient absolute bound", F(5, 8) / F(7, 8) == F(5, 7))
check("quotient error coefficient below two", F(3, 2) / F(7, 8) == F(12, 7) < 2)
check("Schur amplification minimum slack", 4 - (1 + F(5, 7) + 2) == F(2, 7) > 0)
check("growth strict gap at g=1", 1 - F(1, 8) - F(9, 8) / 2 == F(5, 16) > 0)
check("Gaussian interval width and constant", 2 * F(1, 32) == F(1, 16))
check("Gaussian density rational margin", F(1, 8) / 3 == F(1, 24) > F(1, 32))
exp_two_upper = sum((F(2) ** j / math.factorial(j) for j in range(11)), F(0)) + \
    (F(2) ** 11 / math.factorial(11)) / (1 - F(1, 6))
check("independent rational series upper bound for exp(2)", exp_two_upper < 8,
      {"upper": str(exp_two_upper), "tail_first_index": 11, "tail_ratio_upper": "1/6"})

# Exact power budgets in modest finite dimensions. Universality follows from
# the algebraic identities read in the proof, not from these checks.
for n in range(2, 33):
    delta = F(1, 2 ** (n*n+n+1))
    B = 2 ** (n+2)
    K = n*n*(n*n+n+5)
    check(f"budget and probability exponents n={n}",
          B ** (n-1) * delta == F(1, 8) and delta <= F(1, 8)
          and (n*n+n+5)*(n*n) == K and K <= 3*n**4)
    check(f"every stage budget n={n}",
          all(B**k*delta <= F(1, 8) and 1 <= F(3, 2)**k <= 2**n for k in range(n)))


def witness(n):
    return [[F(1) if j == n-1 or i == j else F(-1, 2) if j < i else F(0)
             for j in range(n)] for i in range(n)]


def stage(n, k):
    return [[F(0) if i < k or j < k else F(3, 2)**k if j == n-1 else
             F(1) if i == j else F(-1, 2) if j < i else F(0)
             for j in range(n)] for i in range(n)]


def no_swap(A):
    n = len(A)
    result = []
    for k in range(n):
        result.append(A)
        pivot = A[k][k]
        assert pivot > 0
        assert all(abs(A[i][k]) < pivot for i in range(k+1, n))
        A = [[A[i][j] - A[i][k] / pivot * A[k][j] if i > k and j > k else F(0)
              for j in range(n)] for i in range(n)]
    return result


for n in range(2, 13):
    W = witness(n)
    states = no_swap(W)
    check(f"exact whole witness trajectories n={n}", states == [stage(n,k) for k in range(n)])
    peak = max(abs(a) for S in states for row in S for a in row)
    pivots = math.prod(states[k][k][k] for k in range(n))
    check(f"exact witness growth and pivot product n={n}", peak == F(3,2)**(n-1)
          and pivots == F(3,2)**(n-1) and max(abs(a) for row in W for a in row) == 1)

# Merely supplementary finite perturbations, explicitly not a replacement for
# the universal full-box inductive proof.
for n in range(2, 7):
    W = witness(n)
    delta = F(1, 2**(n*n+n+1))
    B = 2**(n+2)
    for pattern in range(5):
        A = [[W[i][j] + delta * (1 if ((i + 1) * (j + 2) + pattern) % 5 < pattern else -1)
              for j in range(n)] for i in range(n)]
        states = no_swap(A)
        error_ok = all(abs(states[k][i][j] - stage(n,k)[i][j]) <= B**k*delta
                       for k in range(n) for i in range(k,n) for j in range(k,n))
        input_max = max(abs(a) for row in A for a in row)
        peak = max(abs(a) for S in states for row in S for a in row)
        check(f"finite perturbation n={n} pattern={pattern}", error_ok and input_max <= F(9,8)
              and peak/input_max > F(3,2)**(n-1)/2)

# Nonintegral c1 examples are exact on square dimensions. The universal real
# result in the Lean proof uses the genuine exp/rpow asymptotic theorem.
dimensions = []
for twice_c1 in [1, 3, 5, 12]:
    for c2 in [F(1,10), F(1), F(10)]:
        for m in range(2, 65):
            n = m*m
            x = F(3,2)**(n-1)/(2*m**twice_c1)
            K = n*n*(n*n+n+5)
            if x >= 1 and K < c2*x:
                dimensions.append({"c1": str(F(twice_c1,2)), "c2": str(c2), "n": n,
                                   "x_at_least_one": True, "K_lt_c2x": True})
                break
        else:
            raise AssertionError("illustrative finite dimension search failed")
check("exact contradiction instances including nonintegral c1", len(dimensions) == 12, dimensions)

apis = {}
for rel in ["Probability/Distributions/Gaussian/Real.lean",
            "Analysis/SpecialFunctions/Pow/Asymptotics.lean",
            "Analysis/CStarAlgebra/Matrix.lean", "MeasureTheory/Constructions/Pi.lean",
            "MeasureTheory/Integral/Lebesgue/Basic.lean",
            "MeasureTheory/MeasurableSpace/Constructions.lean"]:
    b = (MATHLIB / "Mathlib" / rel).read_bytes()
    apis[rel] = sha(b)
    check("pinned primary API Git bytes " + rel,
          b == subprocess.run(["git", "show", f"0df444a360eaa60ab8c11dca51a86af692955474:Mathlib/{rel}"],
                              cwd=MATHLIB, check=True, capture_output=True).stdout)

write_json("IMPORT-CLOSURE.json", {"complete": True, "acyclic": True, "graph": graph,
                                  "Challenge_imported": False, "sources": sorted(seen)})
write_json("CONTRACTS.json", {"scope": "independent static textual comparison; not actual Comparator",
                             "frozen_targets": contracts})
write_json("API-SOURCES.json", {"mathlib_commit": "0df444a360eaa60ab8c11dca51a86af692955474",
                               "read_primary_sources": apis})
write_json("CHECKS.json", {"status": "all supplementary source and exact-rational checks passed",
                          "count": len(CHECKS), "checks": CHECKS,
                          "limitations": ["No local Lean/Lake invocation", "No actual Comparator run",
                                          "Finite checks are not a universal mathematical certificate"]})
print(json.dumps({"checks": len(CHECKS), "all_pass": True, "outputs": {
    name: sha((HERE/name).read_bytes()) for name in
    ["IMPORT-CLOSURE.json", "CONTRACTS.json", "API-SOURCES.json", "CHECKS.json"]}}, indent=2))
