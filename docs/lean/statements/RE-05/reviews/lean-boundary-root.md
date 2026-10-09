# RE-05 independent Lean-boundary review

**Verdict: APPROVE.** Reviewer: `/root`, 2026-10-09. I authored the RE-05 pre-implementation specification but did not author its live Lean, frozen Lean, or operational query implementation. For metadata, the specification approvals must come from the other independent reviewers. This is a Lean-boundary review, not a proof of the algorithm theorem.

I compared the canonical README, approved numerical specification, the authored manuscript Theorem 2.1 and Proposition 5.1, and both Lean modules. The input family is every independent `q+1≥1` real square-matrix basis with `q+1≤n²`; `A` is arbitrary and `ε` ranges over all `0<ε<1/2`. `represent` uses every real coefficient, `optimum` is the true Frobenius infimum, and `AttainedOptimum` makes attainment an affirmative part of the target, including zero residual. `OriginalClaim` quantifies universal `C,a,b` before every input and requires the original pure `(1+ε)` norm factor with exact `99/100` probability and a worst-case query count.

The shared computation explicitly orthonormalizes the known family, forms its leverage matrix, selects the left singular directions above the source threshold, and precommits all left and independent Gaussian right queries for fifteen copies. `batchAnswers` is the only operation reading the unknown `A`; postprocessing uses stored answers and known data. The Gram and right-hand-side formulas are the exact quadratic coefficients of the source measured-left plus projected-right least-squares objective, with `1/s` scaling. The pseudoinverse gives a defined coefficient output on singular sketches. The selector takes median pairwise Frobenius distances, equivalent to Euclidean coefficient distances in the orthonormalized family, and has deterministic tie breaking.

`SourceCompanion` retains fifteen repetitions at internal squared parameter `ε/9`, source widths `L₀=16 log(20q)+160/ξ`, threshold `sqrt(q/L₀)`, `s=ceil(8 log(20q)+tL₀)`, and the stated fifteen-copy query count. The numerical guarantee is still the original `99/100`, not merely the one-copy constant success. SVD availability and least-squares attainment are asserted facts, not hidden assumptions. No additive error, conditioning promise, or bit-complexity claim is inserted.

I independently reran pinned live/frozen Lake build and `Target = Reviewed.Target := by rfl`; both passed. LeanCert kernel trust reports only standard axioms. This checks the statement boundary; no mathematical proof or Linux Comparator execution is claimed.

## SHA-256 review inputs

| Path | SHA-256 |
| --- | --- |
| `docs/lean/statements/RE-05/NUMERICAL_TARGETS.md` | `df935cbeef31796a83b9db2bc9d6f10a6a300d2d57cd3d0525d83646865d42f7` |
| `docs/lean/statements/RE-05/ORIGINAL.md` | `e8958ad5574576a781613326cdc4ba125b4ee1c2a7f41c64e6adddda3a06772b` |
| `lean-statements/NLA/Computation/LinearFamilyQuery.lean` | `9896ef3618e60d2d0949cf6b1713256e9ec3e22896620108248e72b2f3f6ae80` |
| `lean-statements/NLA/Computation/NonadaptiveMatrixQuery.lean` | `66345a3ed3274e6dd351ffaa7e1b75a0aa95afa63c3ece937d37f1efaad29b21` |
| `lean-statements/NLA/Computation/SVDMachine.lean` | `8ec5866326b5a311b334651600db5d7f3065f2059175823626319afef7cf7581` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/NLA/Statements/RE05.lean` | `aaee94feb3f85702cbfda9cad5e0a32521f0ccb26421b4e8108453fd2a32529e` |
| `lean-statements/Reviewed/RE05.lean` | `aa200e741fa811474096a72b3f45900109cce080edcc9a51d6b40166a3a9d42f` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `randomized-and-low-rank-approximation/RE-05/README.md` | `e8958ad5574576a781613326cdc4ba125b4ee1c2a7f41c64e6adddda3a06772b` |
