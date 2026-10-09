# TR-08 independent Lean boundary review

Reviewer: OpenAI Codex AI agent `/root/infrastructure`, 2026-10-09. I did not author the TR-08 specification, live Lean source, or frozen source. Phase: `lean-boundary`. Verdict: **APPROVE** for the exact statement boundary. This reviews the statement, not a proof of the sharp sparsity criterion or external human peer review.

## Exact `check.py` review inputs

| Input | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/TR-08/README.md` | `41a539dc24862be582750f249f741e4666826ac2df026596247c2a3b5ec1f047` |
| `docs/lean/statements/TR-08/ORIGINAL.md` | `41a539dc24862be582750f249f741e4666826ac2df026596247c2a3b5ec1f047` |
| `docs/lean/statements/TR-08/NUMERICAL_TARGETS.md` | `e54b57685e9b28bb9703d2195d38de6f861e288ba8762b596b1480abfd9ea84e` |
| `lean-statements/NLA/Statements/TR08.lean` | `9e4e01832690ba2c05a057f3bb433fd0666b4247fb73228bd6bdb5ab9bdd65c8` |
| `lean-statements/Reviewed/TR08.lean` | `0bd75db5ccf18cb6a1dac715a0d2d8d1b6579e42d3c0ed4114254829ac1e7cb9` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

These are every path returned by `tools/lean_statements/check.py` `review_inputs` for TR-08's `lean-boundary` phase, including the repository-local import closure and dependency pins. The canonical README and retained `ORIGINAL.md` are byte identical. The frozen source is exactly the live source with the standard header and permanent-ID namespace substitution.

## Mathematical and numerical meaning

The `Sample` finite product comprises one exact-cardinality row support for each ambient column, one independent Boolean sign at every potential position, and one independent exact-`k/100` selected-column subset. Its uniform law gives the source's independent uniform supports, fair selected signs, and independent uniform column selection; unused pre-drawn signs do not affect the matrix. `signedEntry` has exactly `±1/sqrt(s)` on selected rows and zero elsewhere. `SelectedIndex` keeps precisely the selected columns, with labels as a deterministic ordering. The finite counting ratio in `successProbability` is the exact joint-law probability, with no sampling approximation or reduction that discards `n_k`.

`leastSingular` takes the infimum of the genuine Euclidean output norm over every real unit input vector for the selected `k×(k/100)` matrix. Since admissible `k` starts at 100, the input sphere is nonempty. The event uses the weak `σ_min≥a` comparison. `rows t=100(t+1)` traverses exactly the positive multiples of 100. `Admissible` preserves fixed `c>0`, real ambient-growth bound `n_k≥k^(1+c)`, and integer `1≤s_k≤k` for arbitrary sequences. `Successful` chooses one positive real `a` after the sequences and requires the exact success probabilities to tend to one. `PositiveLowerRatio` gives an eventual strict positive lower bound on `s_k²/log k`, equivalent to the source's positive liminf and valid for oscillating sequences. `Target` is the full equivalence for every admissible pair and every `c>0`, with neither an upper distortion condition nor an exponent-only threshold. I found no changed probability law, quantifier order, singular-value definition, endpoint, or threshold.

## Kernel and frozen identity checks

With pinned Lean 4.33.1, `lake build NLA.Statements.TR08 Reviewed.TR08` passed (8710 jobs). Both files' `#assert_statement` and `#assert_trust kernel` passed, and printed axiom closure is `propext`, `Classical.choice`, `Quot.sound`. A fresh file importing both modules proved

```lean
example : NLA.Statements.TR08.Target = NLA.ReviewedStatements.TR08.Target := by rfl
```

No TR-08 Lean source was edited in this review.
