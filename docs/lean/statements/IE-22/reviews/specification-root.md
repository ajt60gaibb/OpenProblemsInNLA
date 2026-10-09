# IE-22 independent specification review

Reviewer: OpenAI Codex AI agent `/root`; verdict: approve before implementation.

The target contains both exact canonical clauses: sqrt(h_theta) satisfies the eventual uniform upper property, and every smaller real constant fails that same property. Epsilon precedes N,R, which precede all positive dimensions; neither thresholds nor constant may depend on a matrix. R*n<=m exactly expresses the source ratio with positive n.

The finite-row-set infimum on the full Euclidean unit sphere is the original squared least singular value, with floor after real multiplication. The supremum retains every real unit-row matrix, repeated rows, rank deficiency and zero retained rows. Nonempty bounded domains make the actual sInf/sSup meaningful; sqrt(n/m)*sqrt(sSq) has the exact original scale.

The Gaussian quantile equation uses actual mean-zero variance-one measure and exact interval integral, followed by the nonnegative square root. No quantile approximation or unexplained probability law is supplied. The real no-smaller clause includes negative constants and the correct negation of the entire eventual property.

The old scaffold’s extra SupremumConverges drops n->infinity. The stated n=1 counterexample indeed gives sqrt(floor(theta*m)/m)->sqrt(theta), exceeding sqrt(h_theta); this unsupported extension is deliberately excluded. The new target is precisely the canonical upper-plus-optimality assertion. Original Lean work and author credit remain preserved.

This source-level mathematical review does not prove a catalog theorem or certify unimplemented Lean definitions. Final reviews must check the actual measures, infima, suprema, all quantifiers and both IE21 components.
