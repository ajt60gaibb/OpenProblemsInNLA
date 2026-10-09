# MF-08 Lean statement boundary: independent review

**Verdict: APPROVE.** Reviewer: `/root/inventory_review`, 2026-10-09. This validates the exact decision-language and complexity boundary, not an NP-hardness proof.

I compared the canonical README and original problem TeX with the approved specification, both Lean boundaries, and their entire repository-local import closure. The frozen file differs from the live file only by its freeze comment and namespace. A separate `rfl` check confirmed that their `Target` propositions are definitionally equal.

`MF08Decision.Input` carries three rational matrices with actual dimensions `n×n`, `n×m`, `p×n`; `ValidInput` requires all dimensions positive. Its fixed binary encoder records the dimensions and every exact rational entry in row-major order with self-delimiting natural and normalized rational encodings. `DecisionLanguage` requires equality with the *entire* encoded word, so a malformed word or unchecked suffix is outside the language. `ClosedLoop` computes the literal finite sums for `A+BKC` with an unrestricted real `m×p` gain. `Hurwitz` quantifies over all complex eigenpairs with nonzero vectors and requires the strict negative real part, including exclusion of imaginary-axis eigenvalues.

The target is `ManyOneNPHard` of this fixed language. The shared complexity predicate quantifies over every language in `InNP` and an actual polynomial-time many-one reduction. `InNP` and the reduction use finite Turing-machine transition tables, bounded halting traces, a concrete binary pair encoder, and one polynomial bit-time bound selected before all inputs. It does not assert NP membership of MF-08, impose gain bounds, or replace the reduction with a free map or real-arithmetic cost measure. I found no semantic weakening of the original language or hardness claim.

Pinned local `lake build NLA.Statements.MF08 Reviewed.MF08` succeeded with Lean 4.33.1. Both LeanCert kernel assertions accepted the targets; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. This is separate from the Linux Comparator run.

## SHA-256 review inputs

The first thirteen paths are exactly the `tools/lean_statements/check.py` `lean-boundary` closure. The original problem TeX was additionally inspected.

| Path | SHA-256 |
| --- | --- |
| `docs/lean/statements/MF-08/NUMERICAL_TARGETS.md` | `f39c5b22ee0a6689209b898c1aca8175ad567f1b574c62d0272b07820f8b64f7` |
| `docs/lean/statements/MF-08/ORIGINAL.md` | `f1be500b7a835ccfdaf00db211fe71e27b0fed4108aaf979e4136c95fd656dfe` |
| `lean-statements/NLA/Computation/BinaryEncoding.lean` | `d494ffb15274500ea5c06c480c2b2032a48390533f7171b4ed993d947c44ee6a` |
| `lean-statements/NLA/Computation/Complexity.lean` | `0ad5ee64d5ef0b77f5531b31bb1b69a1a668c556cbd79b42fea7b6f108275c88` |
| `lean-statements/NLA/Computation/FiniteMachine.lean` | `7c8b2a8e88220b3a1a66bf9c9748ee2213b155dd239809654240095180918d9d` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/NLA/Statements/MF08.lean` | `b5cedb8aa6da2ddf57152df228f912df08f952ea0c4c11198254635c70093e49` |
| `lean-statements/NLA/Statements/Shared/MF08Decision.lean` | `f702db882cdd2c7c511bf490e55ff0e4bb3d8ab5882bc10e19c22c54cf30c1b0` |
| `lean-statements/Reviewed/MF08.lean` | `4d21f64fe8093f53b635033299d790db107bbf832e34ce66aae06254bfab648a` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `matrix-functions-and-stability/MF-08/README.md` | `f1be500b7a835ccfdaf00db211fe71e27b0fed4108aaf979e4136c95fd656dfe` |
| `matrix-functions-and-stability/MF-08/problem.tex` | `6f822d1063935bc56597b6d32ac4cca09b4c557b03dbc981763e0151186f2a56` |
