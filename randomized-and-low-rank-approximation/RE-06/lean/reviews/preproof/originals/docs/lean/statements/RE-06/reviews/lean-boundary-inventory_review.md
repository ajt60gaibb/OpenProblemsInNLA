# RE-06 Lean statement boundary: independent review

**Verdict: APPROVE.** Reviewer: `/root/inventory_review`, 2026-10-09. This is a semantic and kernel-boundary review of the proposition, not a proof of its probability estimate.

I compared the canonical README, its approved numerical specification, the source's Theorem 1.1 and algorithm, both Lean boundaries, and their entire repository-local import closure. The frozen boundary differs from the live one only by the freeze comment and namespace, and a separate `rfl` check showed their `Target` propositions are definitionally equal.

The shared query module defines an actual two-phase nonadaptive procedure. `makePlan` receives dimensions, accuracy and a Gaussian stream, with no target matrix or answers; `queryList` commits every right or left query, including the exact-recovery basis branch. `oracleAnswers` is the only operation reading `A`, through literal matrix-vector products. `postprocess` receives the plan and stored transcript, has no oracle operation, and always returns an index of the explicit injective family. The family type has exactly `m+2≥2` members. The infinite product law provides independent standard real Gaussian coordinates; disjoint stream blocks give the source's independent sketches. The full SVD relation fixes valid orthogonal factors and reconstruction, and `SVDTotal` is asserted as an affirmative conjunct rather than used as a premise.

The source widths are retained: `L=ceil(log₂(2M))`, `r=ceil(sqrt L)`, `η=ε/4`, and the exact ceiling expressions for `s,k,ℓ`. The first unscaled Gaussian block has the same warm-start minimizer as the source's normalized block. The low-rank repair uses `Y(HᵀY)†W`, equivalent to the source's orthonormal-basis formula on the full-rank Gaussian event, and remains defined on exceptional sketches. `QueryBound` counts the entire committed list for **every** random stream. `OriginalClaim` keeps one absolute `C>0` and natural `b` ahead of every dimension, family, arbitrary target and accuracy; `ExplicitClaim` additionally fixes `C=4,000,000`, `b=0`. `Successful` requires a single candidate with Frobenius error at most `(3+ε)` times the finite optimum with probability at least `99/100`. There is no average-input, additive-error, or adaptive-query substitution.

Pinned local `lake build NLA.Statements.RE06 Reviewed.RE06` succeeded with Lean 4.33.1. Both LeanCert kernel assertions accepted the targets, and `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. This does not replace the separate Linux Comparator run.

## SHA-256 review inputs

The first eleven paths are exactly the `tools/lean_statements/check.py` `lean-boundary` closure. The source TeX was additionally read for the numerical witness.

| Path | SHA-256 |
| --- | --- |
| `docs/lean/statements/RE-06/NUMERICAL_TARGETS.md` | `ed37af5809b15afd1f9b4411356eaba15fceb9d988f41b0c7a5cda9089044865` |
| `docs/lean/statements/RE-06/ORIGINAL.md` | `df967515f033afaf9db8e77f5be522daf868817d7ee2951bed5b0e757696cbcf` |
| `lean-statements/NLA/Computation/NonadaptiveMatrixQuery.lean` | `66345a3ed3274e6dd351ffaa7e1b75a0aa95afa63c3ece937d37f1efaad29b21` |
| `lean-statements/NLA/Computation/SVDMachine.lean` | `8ec5866326b5a311b334651600db5d7f3065f2059175823626319afef7cf7581` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/NLA/Statements/RE06.lean` | `847ac668ce6a7c99569bab0d1a0ca5a5bc1a471a9938a2a31d19208b9ca5aa00` |
| `lean-statements/Reviewed/RE06.lean` | `6e8b552f4f1d8b3bd330a1748b915b0ebdd5e5f15427ce59a2d7b531493d45f1` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `randomized-and-low-rank-approximation/RE-06/README.md` | `df967515f033afaf9db8e77f5be522daf868817d7ee2951bed5b0e757696cbcf` |
| `randomized-and-low-rank-approximation/RE-06/solution.tex` | `8d875d2ef00fa3c777bc1b1ed6c527465e5038480cd991ce346b1d24df89d23d` |
