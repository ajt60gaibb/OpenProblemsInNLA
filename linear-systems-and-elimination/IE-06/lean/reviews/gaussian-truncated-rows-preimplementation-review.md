# Fixed-fiber truncated row tail: preimplementation review

Root approved this exact B1 sub-contract before coding; independently checked
by the mathematical review agent. For arbitrary finite row index iota, any
fixed T:Mat t and M:Matrix(Fin t)(Fin p) Real, x>=0, and tau>=frobeniusNorm(M)^2,
use the literal product over iota of restrictedGaussian(truncationBody T).
The probability that some row z_i satisfies
(2+4x)*tau < sum_a ((z_i vecMul M)_a)^2
is at most card(iota)*ofReal(exp(-x)). Every coordinate marginal is the actual
normalized restricted Gaussian. The body has positive mass for every T, so
there is no Good(T), nonsingularity, or measurable selector premise. Existing
F7 proves the single-row quadratic tail; finite union and exact evaluation
pushforward give this estimate. The Frobenius definitions differ only by sum
order and the projection definition only by commutativity of scalar products;
these bridges will be proved. Empty row types and empty matrix dimensions
retain literal meanings. This statement alone does not integrate a random
spectral selection or claim the complete B1/B2 bound.

Completed implementation: `NLA/IE06/GaussianTruncatedRows.lean`, SHA-256
`3ba022aeee6b700bd7a891fa386a715854a92955ca6f0366cbfe7e6eaf51ed8a`. All 7 local declarations passed their individual LeanCert
kernel-policy assertions and printed only foundational axioms (propext,
Classical.choice, Quot.sound), with no warnings. The pinned-runtime local-cache
receipt/log are in the corresponding review subdirectory. This does not claim
a fresh dependency rebuild or cached-dependency kernel replay. The coordinator
will independently review the frozen source.
