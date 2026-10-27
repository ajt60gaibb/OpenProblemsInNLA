# RE-05 Lean statement boundary: independent review

**Verdict: APPROVE.** Reviewer: `/root/inventory_review`, 2026-10-09. This is a review of the exact algorithmic proposition, not a proof of its random sketch estimates.

I compared the canonical README, approved numerical specification, source Theorem 2.1 and Proposition 5.1, both Lean files, and their complete repository-local import closure. The frozen file differs only by its freeze comment and namespace; an independent `rfl` check established definitional equality of the two `Target` propositions.

The shared procedure represents an explicitly supplied `q+1≥1` member real matrix basis, states literal linear independence, and forms actual linear combinations. It orthonormalizes the known family, constructs the left leverage matrix, and precommits all fifteen copies of its left singular-vector and independent right Gaussian queries before receiving answers. Every occurrence of the unknown `A` in `run` is through the responses to that single batch of literal `Av` or `Aᵀv` calls. Postprocessing builds the measured-left plus projected-right least-squares Gram matrix from known data and stored answers, uses a concrete exact SVD pseudoinverse including singular sketches, and returns all real coefficients. The fifteen-copy selector uses the median of all fifteen Frobenius distances between represented outputs, including self-distance, with deterministic tie breaking. This is the manuscript's coefficient-space median after the isometric identification with the matrix span.

`Successful` requires pure Frobenius **norm** relative error `≤(1+ε)OPT` with probability at least `99/100` for each fixed admissible input, including zero optimum. `AttainedOptimum` asserts the exact finite-dimensional minimum rather than assuming it as a premise. `OriginalClaim` keeps one positive constant and two natural exponents before all positive dimensions, `1≤q≤n²`, independent bases, arbitrary targets and `0<ε<1/2`; `QueryBound` counts the actual precommitted list for every Gaussian stream. `SourceCompanion` additionally records the source's fifteen-copy count with internal squared parameter `ε/9`, `L₀=16 ln(20q)+160/(ε/9)`, and the exact `2√(qL₀)+8 ln(20q)+1` per-copy bound. The target does not add bit complexity, an additive error, or a rank promise.

Pinned local `lake build NLA.Statements.RE05 Reviewed.RE05` succeeded with Lean 4.33.1. LeanCert kernel assertions accepted both targets; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. This is distinct from the Linux Comparator run.

## SHA-256 review inputs

The first twelve paths are exactly the `tools/lean_statements/check.py` `lean-boundary` closure. I additionally checked the source TeX.

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
| `references/colbrook-transfer-2026-09-11/manuscripts/05_linear_family_relative_sketch.tex` | `240abf9fbaa23e7847b0ed5b80bea6fafc453969d826b0e3d60f6c580e151d57` |
