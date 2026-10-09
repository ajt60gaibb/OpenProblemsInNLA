# TR-08 independent Lean-boundary review

**Verdict: APPROVE.** Reviewer: `/root`, 2026-10-09. I did not author the TR-08 specification, live Lean source, or frozen Lean boundary. This is an exact-statement review, not a proof of the sharp threshold theorem.

I compared the canonical README, the pre-implementation numerical specification, the live Lean module, the frozen module, and their local import closure. The live proposition quantifies over every fixed positive growth exponent and every arbitrary admissible ambient/sparsity sequence. `rows t=100(t+1)` visits exactly the required positive multiples of 100; `Admissible` keeps `n_k≥k^(1+c)` and `1≤s_k≤k`.

`Sample` contains one exact-cardinality uniform support per ambient column, one independent fair sign at every coordinate (unused signs are ignored), and an independent exact-cardinality uniform selected-column set. The finite uniform count therefore represents the complete original joint law, including the column-set randomness. `signedEntry` uses exactly `±1/sqrt(s)` on selected positions and zero elsewhere. The selected matrix has the actual selected columns; their index order cannot alter singular values.

`leastSingular` takes the infimum of the actual Euclidean image norm over every real unit input vector. The success probability counts the exact event `a≤σ_min`; the threshold witness is positive and fixed before the asymptotic limit. `PositiveLowerRatio` is an eventual positive lower bound for `s_k²/log k`, correctly handling oscillating sequences. `Target` asserts both necessary and sufficient directions, with no upper-distortion surrogate or logarithmic-exponent-only gap.

I independently reran pinned `lake build NLA.Statements.TR08 Reviewed.TR08`, which passed with only `propext`, `Classical.choice`, and `Quot.sound` in the axiom closure, and a separate live-to-frozen `rfl` identity check passing. I independently checked the source-level definitions and review-input hashes below. This is local statement-boundary verification; no external proof or Linux Comparator run is claimed.

## SHA-256 review inputs

| Path | SHA-256 |
| --- | --- |
| `docs/lean/statements/TR-08/NUMERICAL_TARGETS.md` | `e54b57685e9b28bb9703d2195d38de6f861e288ba8762b596b1480abfd9ea84e` |
| `docs/lean/statements/TR-08/ORIGINAL.md` | `41a539dc24862be582750f249f741e4666826ac2df026596247c2a3b5ec1f047` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/NLA/Statements/TR08.lean` | `9e4e01832690ba2c05a057f3bb433fd0666b4247fb73228bd6bdb5ab9bdd65c8` |
| `lean-statements/Reviewed/TR08.lean` | `0bd75db5ccf18cb6a1dac715a0d2d8d1b6579e42d3c0ed4114254829ac1e7cb9` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `randomized-and-low-rank-approximation/TR-08/README.md` | `41a539dc24862be582750f249f741e4666826ac2df026596247c2a3b5ec1f047` |
