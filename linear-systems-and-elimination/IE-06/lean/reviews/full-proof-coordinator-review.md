# Independent review of the full-proof mathematical contracts

2026-10-06. Coordinator AI review of the source-analysis agent's
`full-proof-specification.md` before implementing the manuscript lemmas.

The centered Gaussian restriction is sufficient for the retained IE-06 target.
I checked the source's Section 4 estimates, Section 5 adaptive conditioning,
selected-row extension, truncated-inverse recursion, and final tail assembly.
The proposed F/A/B/C dependency contracts preserve the actual all-Schur
target, exact probability model, all-path requirement, and dimension-uniform
constant quantifiers. Source-inferred all-Schur statements are distinguished
from the literal LU-growth theorem.

The source review correctly identifies an essential formal denominator guard
in Lemma 4.6: `σ_(k-j)(BQ)>0` must be supplied where real division is used.
The later good event supplies it. Positive rank counts, valid spectral
indices, and the strict `μ < sqrt(k)` extension premise are also explicit.
These are necessary mathematical domain conditions, not optional numeric
checks. They do not alter the final target.

The scalar recursion estimates and failure-probability bookkeeping have the
correct dependence: `β=γ+2` covers fewer than `n²` pairs; the final choice
`p=γ=α+1` leaves enough slack to make the sum strictly below `n^(-α)`
eventually. Every changing-dimension or rank-dependent factor must be retained
through the recursion before it can be absorbed into a uniform constant.

Approved as exact mathematical contracts for implementation. This approval
does not supply proofs of external analytic inputs, measurable spectral
choices, conditional-law identities, or any main Gaussian estimate. Each must
be proved and independently reviewed in Lean before unconditional assembly.
Any implementation revision to these contracts reopens the relevant review.
