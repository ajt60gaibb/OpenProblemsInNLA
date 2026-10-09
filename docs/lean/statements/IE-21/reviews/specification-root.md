# IE-21 independent specification review

Reviewer: OpenAI Codex AI agent `/root`; verdict: approve before implementation.

The OriginalLimitTarget retains every fixed theta in (0,1), its exact positive Gaussian quantile, and both growth limits n->infinity and m/n->infinity. Positive-dimension tails do not change the limiting statement. The probability event uses weak epsilon exceedance for every positive epsilon and varies only the sample dimension, requiring no cross-size coupling.

Concrete infimum of full retained row energy on the Euclidean unit sphere equals the squared variational least singular value, including the empty retained set and rank deficiency. floor is applied after theta*m. The supremum of full image energy is the squared actual Euclidean norm; all target domains avoid empty/unbounded real-infimum/supremum artifacts.

Inspected the pinned HaarToSphere definition and its apply/univ/positive finite mass API. Normalizing Euclidean Haar-toSphere yields uniform surface probability, including dimension one; finite Measure.pi fixes actual independent identical row laws. It replaces the old support-only record and artificial measurable-space instance rather than importing them.

The separate quantitative answer is clearly identified as Colbrook’s supplied stronger answer to an unprescribed request, not an equivalent original numerical conjecture. Directly checked manuscript Sections 4–5: both simultaneous error bounds use the same covariance/net exception event and the exact 2*9^n*exp(-m*t^2/512)+5*(1+2/delta)^n*exp(-2*m*eta^2) failure bound. All finite-sample terms, parameter domains, strict error failures, and non-strict probability bound match.

The parameter-choice calculation correctly yields 2*(9/Q^2)^n and an upper bound 5*(2*Q^(-2047.5))^n, with errors tending to zero whenever the two original growth conditions hold. It imposes no relation between their divergence rates. Both separately named components and their combined Target must be checked, preserving the exact original limit independently.

This source-level mathematical review does not prove a catalog theorem or certify unimplemented Lean definitions. Final reviews must check the actual measures, infima, suprema, all quantifiers and both IE21 components.
