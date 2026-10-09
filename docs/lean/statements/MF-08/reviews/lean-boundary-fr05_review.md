# MF-08 independent Lean-boundary review

**Verdict: APPROVE.** I authored the MF-08 specification review, but neither the specification nor this Lean implementation. I independently checked the complete live and frozen declarations, shared decision-language definitions, imported encoding and complexity semantics, canonical README, and approved specification. This reviews the proposition boundary, not a proof of NP-hardness.

## Bound inputs

These are all paths returned by `tools/lean_statements/check.py`'s `review_inputs` for MF-08's Lean-boundary phase, including the complete repository-local import closure and dependency pins.

| Input | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-08/README.md` | `f1be500b7a835ccfdaf00db211fe71e27b0fed4108aaf979e4136c95fd656dfe` |
| `docs/lean/statements/MF-08/ORIGINAL.md` | `f1be500b7a835ccfdaf00db211fe71e27b0fed4108aaf979e4136c95fd656dfe` |
| `docs/lean/statements/MF-08/NUMERICAL_TARGETS.md` | `f39c5b22ee0a6689209b898c1aca8175ad567f1b574c62d0272b07820f8b64f7` |
| `lean-statements/NLA/Computation/BinaryEncoding.lean` | `d494ffb15274500ea5c06c480c2b2032a48390533f7171b4ed993d947c44ee6a` |
| `lean-statements/NLA/Computation/Complexity.lean` | `0ad5ee64d5ef0b77f5531b31bb1b69a1a668c556cbd79b42fea7b6f108275c88` |
| `lean-statements/NLA/Computation/FiniteMachine.lean` | `7c8b2a8e88220b3a1a66bf9c9748ee2213b155dd239809654240095180918d9d` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/NLA/Statements/MF08.lean` | `b5cedb8aa6da2ddf57152df228f912df08f952ea0c4c11198254635c70093e49` |
| `lean-statements/NLA/Statements/Shared/MF08Decision.lean` | `f702db882cdd2c7c511bf490e55ff0e4bb3d8ab5882bc10e19c22c54cf30c1b0` |
| `lean-statements/Reviewed/MF08.lean` | `4d21f64fe8093f53b635033299d790db107bbf832e34ce66aae06254bfab648a` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |

The canonical README and `ORIGINAL.md` are byte identical. The frozen file is exactly the freeze header plus a namespace substitution of the live statement module; both refer to the **same** imported shared decision language.

## Semantic audit

`Input` contains positive-dimensional rational `A : n×n`, `B : n×m`, `C : p×n` and explicit dimensions. `Encode` lists these dimensions and then every entry in row-major order using the pinned self-delimiting `encodeNat` and normalized signed `encodeRat`. `DecisionLanguage` requires equality to the **complete** encoded word and `ValidInput`; malformed encodings, zero dimensions and trailing bits cannot be accepted through an unchecked parse. This is the source's binary rational language rather than a real-arithmetic surrogate.

`ClosedLoop` has entries `Aᵢⱼ + ∑ᵤ∑ᵥ Bᵢᵤ Kᵤᵥ Cᵥⱼ`, with arbitrary **real** `K : m×p`. `Hurwitz` quantifies every complex eigenvalue via an actual nonzero complex eigenvector and requires `z.re < 0` strictly. Zero-real-part eigenvalues fail, and the matrix-vector equations use finite complex sums with no conjugation. There is no entry bound, pattern restriction, selected-pole condition, or promise on the plant.

`Target` is `NLA.Computation.Complexity.ManyOneNPHard DecisionLanguage`. In the imported implementation, `ManyOneNPHard` quantifies every concrete `InNP` language and a polynomial-time many-one reduction whose output is an actual bounded finite-transducer run on every binary word. It asserts no NP membership for the target or complexity-class separation. Thus the statement retains the exact canonical complexity quantifiers.

The pinned `lake build NLA.Statements.MF08 Reviewed.MF08` passed. Both modules' `#assert_statement` and LeanCert `#assert_trust kernel` passed with only `propext`, `Classical.choice` and `Quot.sound` in their axiom closures. I separately proved live `Target` equals frozen `Target` by `rfl`, and kernel trust accepted that identity. These controls establish statement identity and trust discipline; they do not prove NP-hardness or replace isolated Comparator verification.
