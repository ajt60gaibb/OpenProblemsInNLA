# TR-21 independent Lean boundary review

Reviewer: `/root/fr05_review`, independent of the TR-21 Lean author.
Phase: `lean-boundary`. Verdict: **APPROVE** the exact statement boundary.
No proof of the comparison theorem or isolated Linux Comparator result is
asserted here.

## `check.py` review inputs and SHA-256

| Input | SHA-256 |
| --- | --- |
| `tensor-computations/TR-21/README.md` | `645fab1674f258c7d120c880118f296ab2066b25ddd257e55bd5b1ad2e84e764` |
| `docs/lean/statements/TR-21/ORIGINAL.md` | `645fab1674f258c7d120c880118f296ab2066b25ddd257e55bd5b1ad2e84e764` |
| `docs/lean/statements/TR-21/NUMERICAL_TARGETS.md` | `8f8266b6106deb2648aacc0ffc6f50801d49c076d5c4638897d5d6606a39f0f4` |
| `lean-statements/NLA/Statements/TR21.lean` | `644b7114867561994a952f0ad4915717642ccc49697bb1d806da6c8192c9fab6` |
| `lean-statements/Reviewed/TR21.lean` | `8b3d64c62dec8066b06256e47fbedf86bd0042bbcbd087a9e8fc75a39be0979a` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

This is the complete repository-local import closure of both modules plus
the three dependency pins required by `tools/lean_statements/check.py`.
The live and frozen files import only the local Infrastructure module;
Mathlib and LeanCert are external pinned dependencies. The toolchain is
Lean 4.33.1, with Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert commit
`621a43d7cf21f87872392a01e874f2f1dbddc926`. The frozen module is
byte-for-byte the prescribed leading comment plus namespace substitution
of the live module. The canonical README and `ORIGINAL.md` are likewise
byte-identical.

## Mathematical correspondence

`TensorIndex` and `Tensor` (live lines 19–22) cover every finite rectangular
format. The target's guards `r ≥ 3` and `n j ≥ 2` (lines 77–83) reproduce
the canonical domain; no cubic or equal-size restriction is present.
`UnitVectors`, `Contraction`, and `InjectiveNorm` (lines 24–39) use real
mode vectors of squared Euclidean norm one, multiply one coordinate from
every mode, sum the full tensor contraction, take its absolute value, and
then optimize over all such tuples. This is the canonical injective norm,
not a flattening or Frobenius norm.

`FiberNorm` uses `Function.update i j a` (lines 41–45), fixing every
coordinate except mode `j`. A full index may describe the same fiber more
than once, but duplicates do not change a supremum. `FiberMaximum`
(lines 47–50) takes the maximum over all fibers of a sample. `FiberScale`
(lines 64–69) integrates that maximum separately in each mode, then takes
the maximum of those expectations; it does not exchange the maximum and
expectation. Every supremum in the target's guarded domain is over a
nonempty bounded set and equals the finite mathematical maximum or norm
specified in the reviewed target.

`AdmissibleLaw` (lines 52–56) requires a probability measure, integrability
of the identity (finite first absolute moment), and mean zero. It adds no
variance, density, boundedness, symmetry, or moment-equivalence hypothesis.
`TensorLaw` (lines 58–62) is the finite product of that same law over all
tensor entries, so the coordinates are iid. The law is selected *after*
the format in `Target`, allowing dimension-dependent distributions.

`Target` chooses `c,C` after each order and before every format and law,
with `0 < c ≤ C`, and states both sides of the original comparison
(lines 75–83). `ManuscriptQuantitativeBound` separately records the
source's stronger lower coefficient one, with an order-only upper
constant (lines 85–93). Both match the reviewed specification and the
revised manuscript's Theorem 1.1. The zero law and heavy-tailed laws
remain in scope.

## Checks and limits

With the pinned Lean 4.33.1 binary,
`lake build NLA.Statements.TR21 Reviewed.TR21` completed successfully
(`2491 jobs`). The live and frozen files both executed `#assert_statement`
and LeanCert `#assert_trust kernel` for both targets. Each printed `Target`
axiom closure was exactly `propext`, `Classical.choice`, `Quot.sound`.
No `sorry`, new axiom, unsafe definition, or native-decision command appears
in the local closure. I found no statement mismatch or boundary blocker.
