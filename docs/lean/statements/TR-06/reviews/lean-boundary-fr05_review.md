# TR-06 independent Lean-boundary review

**Verdict: APPROVE.** Reviewer: `/root/fr05_review`, 2026-10-09. I did not author the live/frozen Lean boundary or the approved specification. This reviews the exact statement boundary, not a proof of the expectation estimate.

I compared the canonical README, manuscript §§1 and 3–4, approved specification, and complete local Lean import closure. Ordinary entry coordinates and `Outer` represent the full tensor Frobenius space and rank-one variety. `ExactRank` rules out shorter decompositions, and `GenericComplexIdentifiable` requires unordered uniqueness on a nonempty principal Zariski-open subset of the complex rank-`r` locus. That is the source generic *complex* hypothesis.

`OuterVariation` is the product-rule derivative of the outer product. At a nonzero rank-one summand its image is the intrinsic tangent space. `RegularDecomposition` makes the derivative of the addition map injective, and `SmoothIdentifiable` combines this with exact rank and unique unordered summands. The manuscript §3 explicitly restricts to the regular identifiable branch and states that omitted algebraic/semialgebraic exceptional subsets have lower dimension and induced volume zero. Thus using this branch in the measure and integrand preserves the expectation. This full-measure geometric equivalence is a mathematical review judgment, not a Lean lemma; a proof of the target in Lean would need it if moving between definitions.

`NormalizeVariation` differentiates each `aᵢ/‖aᵢ‖` separately. The supremum of the product-normalized variation norm divided by the norm of the summed variation is the local inverse-derivative operator norm with the induced tangent metric. All ordered decompositions on this locus differ by a permutation, which leaves that norm unchanged. `InducedVolume` uses the ambient Euclidean Hausdorff measure in dimension `r(1+∑(nⱼ−1))`; for the regular embedded manifold this is its induced Riemannian volume. `GaussianWeight` and `Normalizer` give the exact volume-Gaussian law, and `FiniteAngularMean` asks for a positive finite normalizer and strict finite normalized expectation. No parameter-sampling measure, ordinary condition number, or format-uniform bound enters the statement.

I reran the pinned Lean 4.33.1 live/frozen build and an independent `Target = Reviewed.Target := by rfl` identity check. Both passed. LeanCert kernel trust reports only `propext`, `Classical.choice`, and `Quot.sound`.

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
