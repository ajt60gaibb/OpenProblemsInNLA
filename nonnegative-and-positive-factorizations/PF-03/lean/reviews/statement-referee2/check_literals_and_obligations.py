"""Independent PF03 statement/data preflight; this does NOT run Lean or Comparator.

Read the actual Lean literal syntax with a restricted parser, compare it against
the primary rational data, and recompute the small finite obligations in exact
rational cubic arithmetic. No author generator is imported or executed.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import json
import re
import time

HERE = Path(__file__).resolve().parent
RECOVERY = HERE.parents[1]
CANDIDATE = RECOVERY / "development/PF03"
PRIMARY = (RECOVERY / "recovered-statements/next-statements/PF03-full-20260918"
           / "canonical/references/holden-pf03-2026-09-13/data")
EXPECTED_PRIMARY = {
    "exact_algebraic_certificate.json":
        "868486419ebe5710e0e38aafcf776ae9d22533c4adc9c7dce85e6ff99a9ead01",
    "rational_cone_certificate.json":
        "e4543a34d630be63abe8141a08976559f11fd85346c58939ab6115378040d5f9",
}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class LiteralParser:
    """Accept only nested Fin vectors, integer literals and rational fractions."""
    def __init__(self, text):
        self.text = text
        self.i = 0

    def ws(self):
        while self.i < len(self.text) and self.text[self.i].isspace():
            self.i += 1

    def take(self, token):
        self.ws()
        if self.text.startswith(token, self.i):
            self.i += len(token)
            return True
        return False

    def need(self, token):
        assert self.take(token), (token, self.text[self.i:self.i + 60])

    def integer(self):
        self.ws()
        m = re.match(r"-?\d+", self.text[self.i:])
        assert m, self.text[self.i:self.i + 60]
        self.i += len(m[0])
        return int(m[0])

    def value(self):
        if self.take("!["):
            xs = [self.value()]
            while self.take(","):
                xs.append(self.value())
            self.need("]")
            return xs
        if self.take("("):
            a = self.integer()
            if self.take("/"):
                b = self.integer()
                assert b > 0
            else:
                b = 1
            self.need(")")
            return F(a, b)
        return F(self.integer())

    def complete(self):
        v = self.value()
        self.ws()
        assert self.i == len(self.text), self.text[self.i:self.i + 60]
        return v


def fractions(x):
    return [fractions(v) for v in x] if isinstance(x, list) else F(x)


ZERO = (F(0), F(0), F(0))
ONE = (F(1), F(0), F(0))
ALPHA = (F(0), F(1), F(0))
ALPHA2 = (F(0), F(0), F(1))


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def neg(a):
    return tuple(-x for x in a)


def scale(q, a):
    return tuple(q * x for x in a)


def mul(a, b):
    # Independently use convolution and reduction by X^3-2.
    c = [F(0)] * 5
    for i in range(3):
        for j in range(3):
            c[i + j] += a[i] * b[j]
    for k in (4, 3):
        c[k - 3] += 2 * c[k]
    return tuple(c[:3])


def sumc(xs):
    out = ZERO
    for x in xs:
        out = add(out, x)
    return out


def interval_mul(a, b):
    points = [x * y for x in a for y in b]
    return min(points), max(points)


ELL = F(12599210498948731647672106072782283505702, 10 ** 40)
UPP = F(12599210498948731647672106072782283505703, 10 ** 40)


def enclosure(a):
    # Horner enclosure on the exact rational isolating interval.
    z = (a[2], a[2])
    for q in (a[1], a[0]):
        z = interval_mul(z, (ELL, UPP))
        z = (z[0] + q, z[1] + q)
    return z


def main():
    started = time.time()
    checks = {}
    source_hashes = {}
    originals = {}
    for name, digest in EXPECTED_PRIMARY.items():
        q = PRIMARY / name
        assert sha(q) == digest
        originals[name] = json.loads(q.read_text())
    raw_path = CANDIDATE / "NLA/PF03/RawData.lean"
    raw = raw_path.read_text()
    declarations = list(re.finditer(r"(?m)^def (\w+) : ([^\n]+) :=\n", raw))
    assert len(declarations) == 8
    parsed = {}
    for i, m in enumerate(declarations):
        end = declarations[i + 1].start() if i + 1 < len(declarations) else raw.index("\nend RawData")
        parsed[m[1]] = LiteralParser(raw[m.end():end].strip()).complete()
    seed = originals["exact_algebraic_certificate.json"]
    cone = originals["rational_cone_certificate.json"]
    coeff = fractions(seed["coefficient_matrices"])
    assert all(t[1:] == [0, 0] for matrix in coeff for row in matrix for t in row)
    expected = {
        "coefficientMatrices": [[[t[0] for t in row] for row in a] for a in coeff],
        "orthogonalMatrix": fractions(seed["orthogonal_matrix"]),
        "quadraticMatrix": fractions(seed["Q"]),
        "restrictedGram": fractions(seed["restricted_gram"]),
        "triangle": fractions(cone["coefficient_triangle"]),
        "barycentricCoefficients": fractions(cone["barycentric_coefficients"]),
        "generators": fractions(cone["generators"]),
        "positiveSlice": fractions(cone["positive_slice_functional"]),
    }
    assert parsed == expected
    checks["literal_arrays_independently_parsed_and_matched"] = len(parsed)
    assert 0 < ELL and ELL ** 3 < 2 < UPP ** 3
    checks["strict_rational_root_endpoint_inequalities"] = 3

    O = [[tuple(x) for x in row] for row in parsed["orthogonalMatrix"]]
    Q = [[tuple(x) for x in row] for row in parsed["quadraticMatrix"]]
    C = [[[parsed["coefficientMatrices"][k][r][i] for k in range(3)]
          for r in range(7)] for i in range(7)]
    H = [[[tuple(x) for x in row] for row in a] for a in parsed["restrictedGram"]]
    assert all(tuple(C[i][r]) == O[r][i] for i in range(7) for r in range(7))
    for i in range(7):
        for j in range(7):
            target = ONE if i == j else ZERO
            assert sumc(mul(O[i][k], O[j][k]) for k in range(7)) == target
            assert sumc(mul(O[k][i], O[k][j]) for k in range(7)) == target
    checks["orthogonal_cache_and_both_gram_orientations"] = 49 + 98
    assert all(Q[i][j] == Q[j][i] for i in range(7) for j in range(7))
    assert sumc(Q[i][i] for i in range(7)) == ZERO
    checks["quadratic_symmetry_and_trace_zero"] = True

    local_lower = []
    minors = []
    v = [ONE, ALPHA, ALPHA2]
    for i in range(7):
        for a in range(3):
            for b in range(3):
                h = sumc(scale(C[i][r][a] * C[i][s][b], Q[r][s])
                         for r in range(7) for s in range(7))
                assert h == H[i][a][b]
            assert sumc(mul(H[i][a][b], v[b]) for b in range(3)) == ZERO
        h00 = enclosure(H[i][0][0])[0]
        hdet = enclosure(add(mul(H[i][0][0], H[i][1][1]),
                            neg(mul(H[i][0][1], H[i][0][1]))))[0]
        assert h00 > 0 and hdet > 0
        minor = C[i][0][0] * C[i][1][1] - C[i][0][1] * C[i][1][0]
        assert minor != 0
        minors.append(str(minor))
        local_lower.append([str(h00), str(hdet)])
    checks["seven_restrictions_kernels_fixed_minors_and_14_signs"] = True

    a0 = F(125992104989487316477, 10 ** 20)
    b0 = F(158740105196819947475, 10 ** 20)
    delta = F(1, 10000)
    W = [[F(1)] * 3, [a0 + delta, a0, a0 - delta], [b0, b0 + delta, b0 - delta]]
    assert W == parsed["triangle"]
    dx = scale(1 / delta, add(ALPHA, (-a0, F(0), F(0))))
    dy = scale(1 / delta, add(ALPHA2, (-b0, F(0), F(0))))
    lam = [scale(F(1, 3), sumc([ONE, scale(2, dx), neg(dy)])),
           scale(F(1, 3), sumc([ONE, neg(dx), scale(2, dy)])),
           scale(F(1, 3), sumc([ONE, neg(dx), neg(dy)]))]
    assert [list(x) for x in lam] == parsed["barycentricCoefficients"]
    assert sumc(lam) == ONE
    assert all(enclosure(x)[0] > 0 for x in lam)
    assert [sumc(scale(W[r][j], lam[j]) for j in range(3)) for r in range(3)] == v
    V = [[sum(C[j // 3][r][k] * W[k][j % 3] for k in range(3))
          for j in range(21)] for r in range(7)]
    assert V == parsed["generators"]
    checks["triangle_barycentric_identity_signs_and_21_generators"] = True

    QV = [[sumc(scale(V[s][j], Q[r][s]) for s in range(7))
           for j in range(21)] for r in range(7)]
    cross = []
    for i in range(7):
        for j in range(i + 1, 7):
            for a in range(3):
                for b in range(3):
                    value = sumc(scale(V[r][3 * i + a], QV[r][3 * j + b]) for r in range(7))
                    lower = enclosure(value)[0]
                    assert lower > 0
                    cross.append(lower)
    assert len(cross) == 189
    checks["strict_cross_pairings"] = len(cross)
    h = [F(x, 10 ** 8) for x in [-71246841, -101280383, -150296097,
                                  -110993458, -39802169, -119030527, -63286873]]
    assert h == parsed["positiveSlice"]
    dots = [sum(h[r] * V[r][j] for r in range(7)) for j in range(21)]
    assert all(x > 0 for x in dots)
    checks["strict_positive_rational_slice_pairings"] = len(dots)

    ch = (CANDIDATE / "Challenge.lean").read_text()
    names = re.findall(r"(?m)^theorem (\w+)", ch)
    cfg = json.loads((CANDIDATE / "comparator.json").read_text())
    assert len(names) == 25 and ch.count("  sorry\n") == 25
    assert cfg["theorem_names"] == ["NLA.PF03." + x for x in names]
    assert cfg["definition_names"] == []
    assert set(cfg["permitted_axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
    assert not (CANDIDATE / "Solution.lean").exists()
    defs = (CANDIDATE / "NLA/PF03/Definitions.lean").read_text()
    for token in ("sorry", "axiom ", "opaque ", "native_decide", "unsafe "):
        assert token not in defs
    checks["contract_sequence_reference_holes_and_axiom_configuration"] = True
    for name in ["Challenge.lean", "NLA/PF03/Definitions.lean", "NLA/PF03/RawData.lean",
                 "NUMERICAL_TARGETS.md", "generate_raw_data.py", "comparator.json",
                 "lakefile.toml", "lake-manifest.json", "lean-toolchain"]:
        source_hashes[name] = sha(CANDIDATE / name)
    result = {
        "reviewer": "/root/recover_lean_sources",
        "independent_of_source_author": True,
        "scope": "Actual Lean literal parsing and exact rational preflight of finite statement obligations; no Lean proof",
        "checks": checks,
        "sources": source_hashes,
        "primary_sources": EXPECTED_PRIMARY,
        "fixed_minor_values": minors,
        "local_lower_endpoints": local_lower,
        "minimum_cross_lower_endpoint": str(min(cross)),
        "minimum_slice_pairing": str(min(dots)),
        "elapsed_seconds": time.time() - started,
        "Lean_Lake_Comparator_or_author_generator_executed": False,
        "verdict": "finite exact-data preflight PASS; statement approval awaits exact successful header packet",
        "count_change": 0,
    }
    out = HERE / "INDEPENDENT-PREFLIGHT.json"
    assert not out.exists(), "Use a new versioned receipt for another run"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"receipt": str(out), "sha256": sha(out), "checks": checks,
                      "elapsed_seconds": result["elapsed_seconds"],
                      "Lean_Lake_Comparator_or_author_generator_executed": False}, indent=2))


if __name__ == "__main__":
    main()
