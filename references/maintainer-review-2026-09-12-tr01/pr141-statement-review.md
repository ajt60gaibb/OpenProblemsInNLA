# PR141: independent root statement-boundary review

Reviewed PR head: `2c7655f234bbb3b3134133ebae34eb479e9469e1`.
Immutable mathematical source: `yuningyang19/OpenProblemsInNLA_TR-01@ed21181197ac839eac95f549404f94e7e3aa6e10`.

The root reviewer independently read `lean/Problem56/Definitions.lean`, the complete `PaperV7/Expected.lean`, `Certification.lean`, and the final `Main.lean` assembly. This supplements the separate full manuscript audit and the separate formal-proof runtime audit. It does not report a kernel result by itself.

The statement primitives are the actual finite objects in the published target. `WalshIndex m` is the binary vector space of dimension m, so its cardinality ranges over every positive power of two, including one. `normalizedWalsh` has entries plus or minus 1/sqrt(n) from the binary dot product. `rerandomizedSRHT` is exactly sqrt(n/k) times D1 F D2 F S. `FixedSubset` contains all coordinate subsets of cardinality k. Its product with the two complete Boolean sign-layer types, under `uniformProbability`, gives independent uniform signs and sampling without replacement.

`OrthonormalFrame U` means U transpose times U equals the r-by-r identity. `compressedGram` is exactly U transpose times Omega times Omega transpose times U. The norm is the supremum of the Euclidean image norm on unit vectors. For r at least one these are ordinary nonempty bounded finite-dimensional norm and probability suprema. `spectralFailureSup` takes the supremum over deterministic orthonormal frames outside the probability; it does not select a subspace after observing the random map.

`certified_main` supplies one positive universal real constant, followed by all m, r and epsilon with 1 <= r <= n and 0 < epsilon < 1. Its width is min(n,ceil(C r/epsilon^2)), with failure probability at most 1/100. The explicit theorem supplies the same expression with the finite constant `200 * 2^20000 + 8196 * (576 * 4^24)`. The constant is large but independent of all target parameters. The final statement has no residual large-rank, logarithmic-width, or unsaturated-sampling hypothesis.

The assembly treats full sampling exactly; otherwise the prescribed ceiling supplies the needed lower bound. The two remaining cases r < R0 and r >= R0 cover all ranks. The small-rank second-moment bound and large-rank signed-trace/sampling bound are applied at this exact width. No monotonicity from an alternative smaller sample size is used.

For any fixed subspace V, choose an orthonormal basis matrix U. The symmetric Gram error G = U transpose Omega Omega transpose U - I has operator norm at most epsilon exactly when -epsilon times I <= G <= epsilon times I. Equivalently, all z satisfy (1-epsilon)||z||^2 <= ||Omega transpose U z||^2 <= (1+epsilon)||z||^2. Since U maps onto V isometrically, this is precisely the canonical event for all x in V. Complementing the strict failure event gives success at least 0.99. The canonical epsilon range is a subset of the proved range.

The submitted README and RESOLVED summary used V first as a subspace and then as a matrix in this Gram formula. The maintainer correction explicitly introduces U as an orthonormal basis and uses U in both formulas. The complete original Problem statement and References block remains byte-identical to published main. Earlier dated status searches were restored as history. Author attribution was read directly from the pinned manuscript.

Verdict on the mathematical statement boundary: PASS. Mathematical proof correctness, artifact QA and executed kernel verification have separate evidence records.
