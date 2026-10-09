# RA-06 independent Lean-boundary review

**Verdict: APPROVE.** `/root/inventory_review` authored the specification
and Lean module. I independently inspected the complete live and frozen
Lean source, local import closure, pins, canonical page, and approved
numerical specification. This approves statement fidelity and local
elaboration, not the truth of the negative sampling theorem or isolated
Linux Comparator verification.

## Bound inputs

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

These are all nine paths returned by `check.py`'s `review_inputs` for
RA-06's Lean-boundary phase. The frozen file is exactly the prescribed
header plus namespace substitution of the live module, with no other
change.

`FullColumnRank` is concrete injectivity of the real matrix action. For
every real `p>2`, `InputEnergy` is the full sum of exact real powers of
absolute row products. `Sensitivity` takes the supremum of the ordinary
row-to-whole energy ratio over every nonzero real input, with no augmented
or restricted score. `RetentionProbability` keeps the exact `1/n` floor,
`s_i/α` addition and unit cap. `OutcomeWeight` multiplies the possibly
unequal Bernoulli probabilities across all rows, retaining an independent
draw. `SampledEnergy` is exactly the rescaled retained-row norm power,
and `Embedding` quantifies every real vector under both weak bounds for
the same outcome. `SuccessProbability` sums weights of precisely those
outcomes; `ExpectedSize` is the marginal sum.

`OriginalPositiveClaim` chooses two positive constants before every
positive dimension, full-rank matrix, and `ε,δ∈(0,1/2)`, then one
positive `α` satisfying both size and success. The exact natural-log
argument and arbitrary positive real logarithmic exponent remain. `Target`
is the full negation for **all** real `p>2`, matching the source's solved
result. Conditions ensuring denominator positivity are guaranteed by the
quantified full-rank/positive-parameter premises; they are not replaced by
extra assumptions. No source mismatch was found.

The pinned `lake build NLA.Statements.RA06 Reviewed.RA06` passed locally.
Both closed Prop assertions and LeanCert kernel trust checks pass, and
both `#print axioms Target` reports list only `propext`,
`Classical.choice`, and `Quot.sound`. The local build is not a proof of
`Target` and is not an isolated Linux Comparator run.
