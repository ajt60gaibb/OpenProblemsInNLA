# RA-06 independent Lean-boundary review

**Verdict: APPROVE.** I authored neither the specification nor the Lean module. I independently compared the live and frozen proposition with the canonical README, the approved numerical specification, and Theorem 5.1 of `references/haidary-resolutions-2026-09-30/ra06-counterexample-revised.tex`. This approves the fidelity and local elaboration of a statement, not a proof of the negative answer.

## Bound review inputs

The following are all paths in `tools/lean_statements/check.py`'s `review_inputs` for RA-06's Lean-boundary phase, including the complete repository-local import closure and dependency pins.

| Input | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-06/README.md` | `5ee10eb6d467ef6ebbd56955cdc95b2a1ff0613231d7e5ed6814679491d78f98` |
| `docs/lean/statements/RA-06/ORIGINAL.md` | `5ee10eb6d467ef6ebbd56955cdc95b2a1ff0613231d7e5ed6814679491d78f98` |
| `docs/lean/statements/RA-06/NUMERICAL_TARGETS.md` | `7036e298c8f74c4693fb638daf1aa22778756a9c26c53fbc39a9341e85f3d5e8` |
| `lean-statements/NLA/Statements/RA06.lean` | `865af15803905e04de1202266f5af75fc5486b8345fdba25a44052202742883d` |
| `lean-statements/Reviewed/RA06.lean` | `dc3ce1bc5396db1dade7fcae71c228759a768a3d0288386e0ad4b929638c64ed` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |

The canonical README and retained `ORIGINAL.md` are byte identical. The frozen module is exactly the mandated header followed by the live module with only the permanent-ID namespace changed.

## Semantic audit

The source's target assertion and negative theorem appear at source lines 61–105 and 444–447. Lean's `FullColumnRank` is the injectivity of the concrete real matrix action. `InputEnergy` is the finite sum of exact `|aᵢᵀx|^p` terms; `Sensitivity` is the ordinary supremum of the row-to-total ratio over **all** nonzero real vectors. The `p>2` and full-rank premises make that denominator positive on the quantified domain. There is no augmented sensitivity or finite test set.

`RetentionProbability` keeps both the `1/n` floor and unit cap. `OutcomeWeight` gives each Boolean retention vector its product Bernoulli weight, including possibly unequal row probabilities. `SampledEnergy` is the exact norm-power identity for retained rows rescaled by `qᵢ^(-1/p)`, so avoiding an explicit root changes no target. `Embedding` puts both weak inequalities inside one universal quantifier over all real vectors for one outcome. `SuccessProbability` sums the weights of precisely those outcomes. `ExpectedSize` is the sum of marginals, as required.

`OriginalPositiveClaim` chooses positive `C_p,c_p` before every positive `n,d`, every full-column-rank `A`, and every `ε,δ∈(0,1/2)`; it then chooses one positive `α` for **both** the exact expected-size budget and success probability at least `1−δ`. Its log argument and positive real log exponent match the source. `Target` is the complete negation for **every real** `p>2`. This preserves the published negative resolution without adding the stronger arbitrary-weight support theorem as an unnecessary assumption.

I built `NLA.Statements.RA06` and `Reviewed.RA06` with the package's pinned Lean 4.33.1 toolchain; both elaborated successfully. `#assert_statement` checks a closed, safe `Prop`, both LeanCert `#assert_trust kernel` checks pass, and both axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`. The local build does not establish the truth of `Target` or substitute for isolated Comparator verification.
