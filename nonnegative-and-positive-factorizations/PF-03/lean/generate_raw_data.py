#!/usr/bin/env python3
"""Pure literal translation of Holden's two hash-pinned data files.

This program was authored before execution; actual runs are recorded separately.
It performs no Lean compilation,
numerical sign check, certificate validation or mathematical proof. A successful
translation is evidence only that the Lean literals encode the source values.
The root coordinator must inspect it before running --write.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
RECOVERY = HERE.parents[1]
DEFAULT_DATA = (
    RECOVERY / "recovered-statements/next-statements/PF03-full-20260918"
    / "canonical/references/holden-pf03-2026-09-13/data"
)
EXPECTED = {
    "exact_algebraic_certificate.json":
        "868486419ebe5710e0e38aafcf776ae9d22533c4adc9c7dce85e6ff99a9ead01",
    "rational_cone_certificate.json":
        "e4543a34d630be63abe8141a08976559f11fd85346c58939ab6115378040d5f9",
}


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def assert_shape(values, shape: tuple[int, ...], name: str) -> None:
    if not shape:
        if not isinstance(values, str):
            raise ValueError(f"{name}: rational entries must be literal strings")
        Fraction(values)
        return
    if not isinstance(values, list) or len(values) != shape[0]:
        raise ValueError(f"{name}: expected dimensions {shape}")
    for index, value in enumerate(values):
        assert_shape(value, shape[1:], f"{name}[{index}]")


def rat(value: str) -> str:
    q = Fraction(value)
    if q.denominator == 1:
        return str(q.numerator) if q.numerator >= 0 else f"({q.numerator})"
    return f"({q.numerator} / {q.denominator})"


def vector(values, depth: int = 0) -> str:
    if not isinstance(values, list):
        return rat(values)
    if all(not isinstance(v, list) for v in values):
        return "![" + ", ".join(rat(v) for v in values) + "]"
    separator = ",\n" + "  " * (depth + 1)
    return "![" + separator.join(vector(v, depth + 1) for v in values) + "]"


def emit(data_dir: Path) -> bytes:
    objects = {}
    for name, digest in EXPECTED.items():
        raw = (data_dir / name).read_bytes()
        if sha(raw) != digest:
            raise ValueError(f"Unexpected primary source bytes: {name}")
        objects[name] = json.loads(raw)
    seed = objects["exact_algebraic_certificate.json"]
    cone = objects["rational_cone_certificate.json"]
    assert_shape(seed["coefficient_matrices"], (3, 7, 7, 3), "coefficient_matrices")
    coefficients = []
    for matrix in seed["coefficient_matrices"]:
        rows = []
        for row in matrix:
            entries = []
            for triple in row:
                # Stripping provably literal zero coefficients is serialization,
                # not a claim about alpha or a theorem used by the formal proof.
                if any(Fraction(value) != 0 for value in triple[1:]):
                    raise ValueError("Coefficient-matrix entry is not a rational literal")
                entries.append(triple[0])
            rows.append(entries)
        coefficients.append(rows)
    declarations = [
        ("coefficientMatrices", "Fin 3 → Matrix (Fin 7) (Fin 7) ℚ",
         coefficients, (3, 7, 7)),
        ("orthogonalMatrix", "Matrix (Fin 7) (Fin 7) Cubic",
         seed["orthogonal_matrix"], (7, 7, 3)),
        ("quadraticMatrix", "Matrix (Fin 7) (Fin 7) Cubic",
         seed["Q"], (7, 7, 3)),
        ("restrictedGram", "Fin 7 → Matrix (Fin 3) (Fin 3) Cubic",
         seed["restricted_gram"], (7, 3, 3, 3)),
        ("triangle", "Matrix (Fin 3) (Fin 3) ℚ",
         cone["coefficient_triangle"], (3, 3)),
        ("barycentricCoefficients", "Fin 3 → Cubic",
         cone["barycentric_coefficients"], (3, 3)),
        ("generators", "Matrix (Fin 7) (Fin 21) ℚ",
         cone["generators"], (7, 21)),
        ("positiveSlice", "Fin 7 → ℚ",
         cone["positive_slice_functional"], (7,)),
    ]
    for name, _, values, shape in declarations:
        assert_shape(values, shape, name)
    header = """/-
PF-03 literal data translated from Sidney Holden's exact cubic-field seed.
Original mathematics and data: Sidney Holden, Center for Computational Biology,
Flatiron Institute, Simons Foundation, 13 September 2026.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, with Codex assistance.

These transparent rational arrays are proposals, not axioms or certificates.
Every equality, sign and original-target conclusion remains a proof obligation.
Source JSON SHA256s:
exact_algebraic_certificate.json:
  868486419ebe5710e0e38aafcf776ae9d22533c4adc9c7dce85e6ff99a9ead01
rational_cone_certificate.json:
  e4543a34d630be63abe8141a08976559f11fd85346c58939ab6115378040d5f9
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Defs

set_option autoImplicit false

namespace NLA.PF03

/-- Literal rational coefficients in the basis (1,alpha,alpha squared). -/
abbrev Cubic := Fin 3 → ℚ

namespace RawData

"""
    body = "\n\n".join(
        f"def {name} : {typ} :=\n  {vector(values)}"
        for name, typ, values, _ in declarations
    )
    return (header + body + "\n\nend RawData\nend NLA.PF03\n").encode()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-dir", type=Path, default=DEFAULT_DATA)
    parser.add_argument("--write", action="store_true",
                        help="Write only NLA/PF03/RawData.lean after coordinator review")
    args = parser.parse_args()
    raw = emit(args.data_dir)
    dest = HERE / "NLA/PF03/RawData.lean"
    if args.write:
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(raw)
    if not dest.exists() or dest.read_bytes() != raw:
        raise ValueError("No identical RawData.lean present; --write is required initially")
    print(json.dumps({
        "translation": "MATCH",
        "scope": "Literal source translation only; NOT Lean or mathematical verification",
        "raw_data_sha256": sha(raw),
        "raw_data_bytes": len(raw),
        "source_hashes": EXPECTED,
        "write": args.write,
    }, indent=2))


if __name__ == "__main__":
    main()
