# RA-06 proof-phase statement review

**Verdict: exact statement, approved for a proof attempt.** This is an independent comparison of the frozen target with the canonical problem and its numerical quantifiers. It is not a proof of `Target`.

## Bound inputs

| Input | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-06/README.md` | `5ee10eb6d467ef6ebbd56955cdc95b2a1ff0613231d7e5ed6814679491d78f98` |
| `docs/lean/statements/RA-06/ORIGINAL.md` | `5ee10eb6d467ef6ebbd56955cdc95b2a1ff0613231d7e5ed6814679491d78f98` |
| `docs/lean/statements/RA-06/NUMERICAL_TARGETS.md` | `7036e298c8f74c4693fb638daf1aa22778756a9c26c53fbc39a9341e85f3d5e8` |
| `references/haidary-resolutions-2026-09-30/ra06-counterexample-revised.tex` | `21c5187b695e4469d803ceced320bd0314ade4702ed4567160f8ff835122cec7` |
| `lean-statements/NLA/Statements/RA06.lean` | `865af15803905e04de1202266f5af75fc5486b8345fdba25a44052202742883d` |
| `lean-statements/Reviewed/RA06.lean` | `dc3ce1bc5396db1dade7fcae71c228759a768a3d0288386e0ad4b929638c64ed` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |

## Quantifier and numerical comparison

`Target` is `∀ p : ℝ, 2 < p → ¬ OriginalPositiveClaim p`. In `OriginalPositiveClaim`, the positive real constants `C,c` precede every positive pair `n,d`, every full-column-rank real matrix, and every `ε,δ` in `(0,1/2)`. A single positive `α` must satisfy both the expected-size inequality and success probability at least `1−δ`. This is the complete negation asserted by the canonical Solved resolution and Theorem 5.1 of the cited source, not a fixed-exponent or fixed-tolerance substitute.

`FullColumnRank` is injectivity of the exact matrix action. `InputEnergy` sums real powers of absolute row values. `Sensitivity` takes the supremum of the ordinary row/whole energy ratio over every nonzero real vector; the full-rank premise and `p>2` make its denominator positive. The retention expression is exactly `min 1 (1/n+s_i/α)`, including the floor and saturated case. `OutcomeWeight` is the product Bernoulli law for possibly unequal row probabilities. Under the quantified positive conditions, each probability is positive, and `SampledEnergy` equals the norm power after scaling retained rows by `q_i^(-1/p)`. `Embedding` uses the same retained outcome for both weak inequalities and all real input vectors. `SuccessProbability` sums precisely the successful outcomes, while `ExpectedSize` sums marginals.

The budget uses `C * ε^(-2) * (S+d) * (log (2nd/(εδ)))^c`, with natural logarithm and arbitrary positive real `c`. No additional sampler, weights, or restricted test-vector set appears. The definitions are concrete rather than unconstrained parameters. The frozen namespace copy has the same mathematical content as the live statement. The statement preserves the canonical RA-06 path and original mathematical target.

No mismatch was found. This approval permits attempting a theorem whose type is the frozen `NLA.Statements.RA06.Target`. The existing `#assert_statement`, `#assert_trust`, and `#print axioms` checks only verify the statement boundary; they do not prove the negative result.
