"""Independent read-only literal audit; no Lean, evaluation, or source mutation.

This is supplementary Python evidence, not a proof-assistant certificate.
The restricted parser accepts only nested ![] and rational numeral literals.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import json
import re

BASE = Path(__file__).resolve().parents[2]
PROJECT = BASE / "development/PF03-agent-packaging-v1/project"
PRIMARY = BASE / "publication/PF03/references/holden-pf03-2026-09-13/data"
OUT = Path(__file__).with_name("LITERAL-CORRESPONDENCE.json")


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def parse_literal(text):
    tokens = re.findall(r"!\[|[\[\](),/]|-?\d+|\S", text)
    pos = 0

    def value():
        nonlocal pos
        t = tokens[pos]
        pos += 1
        if t == "![":
            a = [value()]
            while tokens[pos] == ",":
                pos += 1
                a.append(value())
            assert tokens[pos] == "]"
            pos += 1
            return a
        if t == "(":
            n = int(tokens[pos])
            assert tokens[pos + 1] == "/"
            d = int(tokens[pos + 2])
            assert d > 0 and tokens[pos + 3] == ")"
            pos += 4
            return F(n, d)
        assert re.fullmatch(r"-?\d+", t), t
        return F(int(t))

    out = value()
    assert pos == len(tokens), tokens[pos:pos + 5]
    return out


def definitions(path):
    text = path.read_text()
    found = list(re.finditer(r"^def (\w+)\s*:[^\n]*:=\s*", text, re.M))
    result = {}
    for i, m in enumerate(found):
        tail = text[m.end():found[i + 1].start() if i + 1 < len(found) else len(text)]
        tail = re.split(r"^end\b", tail, maxsplit=1, flags=re.M)[0].strip()
        result[m.group(1)] = parse_literal(tail)
    return result


def rationalize(x):
    return [rationalize(t) for t in x] if isinstance(x, list) else F(x)


def count(x):
    return sum(count(t) for t in x) if isinstance(x, list) else 1


a_path = PRIMARY / "exact_algebraic_certificate.json"
b_path = PRIMARY / "rational_cone_certificate.json"
raw_path = PROJECT / "NLA/PF03/RawData.lean"
cache_path = PROJECT / "NLA/PF03/QuadraticGeneratorCache.lean"
a = json.loads(a_path.read_text())
b = json.loads(b_path.read_text())
raw = definitions(raw_path)
cache = definitions(cache_path)["quadraticGeneratorCache"]

# The primary coefficient matrices themselves are stored as cubic-field triples;
# every nonconstant coefficient is zero, so these are actual rational matrices.
cm = rationalize(a["coefficient_matrices"])
assert all(v[1] == 0 and v[2] == 0 for mat in cm for row in mat for v in row)
expected = {
    "coefficientMatrices": [[[v[0] for v in row] for row in mat] for mat in cm],
    "orthogonalMatrix": rationalize(a["orthogonal_matrix"]),
    "quadraticMatrix": rationalize(a["Q"]),
    "restrictedGram": rationalize(a["restricted_gram"]),
    "triangle": rationalize(b["coefficient_triangle"]),
    "barycentricCoefficients": rationalize(b["barycentric_coefficients"]),
    "generators": rationalize(b["generators"]),
    "positiveSlice": rationalize(b["positive_slice_functional"]),
}
assert raw.keys() == expected.keys()
for k in raw:
    assert raw[k] == expected[k], k

Q, G = raw["quadraticMatrix"], raw["generators"]
assert len(cache) == 7 and all(len(row) == 21 for row in cache)
assert all(len(v) == 3 for row in cache for v in row)
for r in range(7):
    for j in range(21):
        for k in range(3):
            assert cache[r][j][k] == sum(Q[r][s][k] * G[s][j] for s in range(7))

record = {
    "scope": "Independent supplementary exact Python literal/source and QG cache correspondence; no Lean/compiler execution",
    "reviewer": "/root/recover_published_coverage (AI nonauthor proof referee; prior statement author)",
    "all_raw_literal_arrays_match_primary": True,
    "raw_array_rational_counts": {k: count(v) for k, v in raw.items()},
    "all_primary_coefficient_matrices_rational": True,
    "all_147_cubic_QG_cache_entries_match_actual_QG": True,
    "QG_rational_coefficient_equalities": 441,
    "input_sha256": {str(p.relative_to(BASE)): sha(p) for p in [a_path, b_path, raw_path, cache_path]},
    "script_sha256": sha(Path(__file__)),
    "mathematical_or_Lean_certificate": False,
}
OUT.write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
