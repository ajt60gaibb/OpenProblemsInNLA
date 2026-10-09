# TR-06 independent Lean-boundary review

**Verdict: APPROVE.** Reviewer: `/root`, 2026-10-09. I authored the pre-implementation specification, but not the live or frozen Lean boundary. For metadata, the pre-implementation approvals must be from other reviewers. This is an exact-statement boundary review, not a proof of integrability.

I compared the canonical README, approved specification, source manuscript §§1,3–4, and both Lean modules. `Tensor` is the real/complex Euclidean tensor product in ordinary entry coordinates. `RankOne`, `Decomposition`, and `ExactRank` enforce actual nonzero rank-one summands and minimal rank. `GenericComplexIdentifiable` requires a nonempty principal Zariski-open subset of the rank-r complex variety with unordered uniqueness; this is the source generic complex hypothesis, not merely a real uniqueness promise.

`SmoothIdentifiable` selects the regular real identifiable rank-r locus used as the full-measure manifold in source §3: exact rank, unique unordered summands, and injective derivative of the addition map. On this regular branch the differential of addition maps a tuple of rank-one tangent variations to their sum. Its injectivity makes the intrinsic quotient of the product norm after *individual* normalization by the induced tangent norm exactly `‖D(p^{×r}∘Ψ)‖`; permutations preserve that operator norm. The source permits omission of lower-dimensional exceptional points from the expectation. This interpretation relies on the standard regular-locus/full-measure geometric equivalence, which is a mathematical statement review judgment and is not separately proved in Lean.

`InducedVolume` restricts the ambient Euclidean Hausdorff measure of the correct manifold dimension `r(1+∑(n_j−1))` to that locus. This is its induced Frobenius Riemannian volume, not a law on independently chosen summands. `GaussianWeight` is exactly `exp(−‖A‖²/2)`; `Normalizer` is the actual volume integral, and `FiniteAngularMean` requires a positive finite normalizer and a finite normalized angular expectation. `Target` quantifies every order `d≥3`, every mode size `n_j≥2`, every rank `r≥3`, and every generically complex-identifiable format; it claims no format-uniform constant or ordinary condition-number bound.

I independently reran pinned live/frozen Lake build and a separate `Target = Reviewed.Target := by rfl`; both passed. LeanCert kernel trust reports only the three standard axioms. This is source-fidelity and local boundary verification, not a proof or Linux Comparator run.

## SHA-256 review inputs

| Path | SHA-256 |
| --- | --- |
| `docs/lean/statements/TR-06/NUMERICAL_TARGETS.md` | `ccc0528ad0404fcd6b5e7d3fcb31e68a65904fd631e052417fcd281480d60a16` |
| `docs/lean/statements/TR-06/ORIGINAL.md` | `f364f4b2ad51065c17d7dd08ea32e729a5d53a8333f0785a11a368165942de6b` |
| `lean-statements/NLA/Statements/Infrastructure.lean` | `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37` |
| `lean-statements/NLA/Statements/TR06.lean` | `9e4a03e91c3b095ba9c47e6532e95a51ce012db55ab0b4d8621e7c13a50e0034` |
| `lean-statements/Reviewed/TR06.lean` | `f1b6d9ed5c792a0c6527b8d64bb46fa52f2579f5c58835c35a02eb50e5bc4e47` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `tensor-computations/TR-06/README.md` | `f364f4b2ad51065c17d7dd08ea32e729a5d53a8333f0785a11a368165942de6b` |
