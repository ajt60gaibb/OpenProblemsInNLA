# Exact IE-06 targets and numerical policy

The IE-06 target specification was written and independently reviewed before
the target implementation: [statement specification](reviews/statement-specification.md),
[independent preimplementation review](reviews/independent-mathematical-review.md),
and [coordinator review](reviews/coordinator-preimplementation-review.md).

| Item | Exact scope |
| --- | --- |
| Original IE-06 | For every real `η > 0`, the probability of all-Schur partial-pivot growth exceeding `n^(1/2 + η)` tends to zero. |
| Probability law | Exactly `n²` mutually independent real `N(0,1)` entries, as a nested finite product measure. |
| Growth | Maximum absolute entry over the input and every active Schur complement, divided by the original maximum absolute entry. Exact arithmetic. |
| Ties | The bad event contains a matrix if any admissible maximum-column pivot path exceeds the threshold. Thus its complement controls every path. |
| Singular inputs | Explicitly excluded from the event; no conditional probability is used. Their Gaussian nullity is proved in `GaussianNull.lean`. |
| Small dimensions | The event is empty for dimension zero at every threshold. A nonzero one-dimensional matrix has growth exactly one. |
| Stronger source-bound statement | For every real `α > 0`, some real `C > 0` and natural `N ≥ 2` work for all `n ≥ N`, with threshold `sqrt(n) exp(C sqrt(log n))` and strict failure bound `< n^(-α)`. |
| Constants | `1/2` is an exact rational exponent. `C` and `N` depend only on `α`; the proof supplies an explicit symbolic `C` and an existential cutoff without evaluating it. |
| Asymptotic bridge | For `C ≥ 0`, `η > 0`, `n ≥ 1`, `log n ≥ (C/η)^2` gives the deterministic threshold comparison. The unconditional stronger tail discharges the premise of the proved implication. |
| Infrastructure fixture | `Real.log 2 < (7 : ℝ)/10`, with no variable domain, proved by `leancert (trust := kernel)`. It tests the numerical proof pipeline and does not bound Gaussian growth. |

No numerical sampling, interval subdivision, enormous cutoff construction,
or finite list of dimensions is needed for these statements. The asymptotic
bridge uses symbolic real inequalities and limits. Every implementation file
sets LeanCert's trust mode to `kernel`; the scalar fixture also selects that
mode at the tactic call. All concrete declarations and supporting theorems
are checked for forbidden transitive axioms.

The stronger all-Schur proposition is extracted from Section 5 of Urschel v1;
it is not a literal transcription of Theorem 1.4, whose growth uses the LU
factors. Source normalization, singularity, and tie-nullity arguments must
not be replaced by an identification of those two growth definitions.

`Challenge.lean` retains six isolated reference signatures with deliberate holes.
`Solution.lean` independently implements all six without importing Challenge.
The unconditional proof is in `Unconditional.lean`; its complete probabilistic
dependencies and verification scope are documented in `PROOF_STATUS.md`.
