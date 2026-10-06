# Independent review of conditional and semantic support

Date: 2026-10-06. Reviewer: independent mathematical-review agent.
This review follows the independent written-specification and formal-statement
reviews. It distinguishes completed supporting proofs from the still-unproved
random-matrix estimate.

## Reviewed bytes

| File, relative to `IE-06/lean` | SHA-256 |
| --- | --- |
| `NLA/IE06/Reduction.lean` | `0e2faeb5cecf638e1312f08adc777f13b32af3a348fa737c600f96ff644516ad` |
| `NLA/IE06/Semantics.lean` | `c61cd8770a62e844e678f738ef98f5de5521d8d23dcd0560f34744029d30e112` |
| `reviews/statement-specification.md` | `c58ae67bbbd2d9764c75924eec6a400e23d65e90ccbc2257ead8db01ec24592b` |

The two Lean modules import the previously reviewed concrete statement module,
not `Challenge`. They contain no `sorry`, arbitrary new axiom, or native
evaluation tactic. Every exported supporting theorem has an explicit
kernel-trust assertion and printed axiom audit. Actual execution evidence is
retained separately by the final local checker.

## Conditional analytic reduction

`subpower_threshold_le_proved` proves exactly the reviewed real inequality.
Its assumptions are `C ≥ 0`, `η > 0`, `x ≥ 1`, and
`(C / η)^2 ≤ log x`. They imply `C / η ≤ sqrt(log x)`;
multiplication by the positive `η` and nonnegative square root then bounds
`C sqrt(log x)` by `η log x`. Monotonicity of the real exponential and the
positive-base real-power identities yield the displayed threshold comparison.
No decimal approximation or finite-dimensional sampling enters this proof.

`subpower_threshold_eventually_le_proved` obtains the explicit logarithm
cutoff eventually from `log n → ∞` and the dimension condition `n ≥ 1`
eventually. It applies the preceding theorem to real natural casts. Both `C`
and `η` stay fixed across dimensions, as required by the reviewed proposition.

`squareRootUpperBound_of_schurSubpolynomialTail_proved` retains the complete
all-Schur tail proposition as its explicit argument `hsource`. It selects the
source exponent `α = 1`, then obtains the source constants before introducing
the eventual dimension. Once the source threshold is at most the original
threshold, an input with any bad admissible path for the original event has
that same path in the source event. This proves the correct containment
direction, preserving dimension, nonsingularity, path admissibility, and
strict growth. Measure monotonicity and the source bound dominate the actual
probability by `ofReal(n^(-1))`. That quantity tends to zero, so squeezing
between zero and this upper bound proves the full original `Tendsto` target.

The reduction is a genuine proof of an implication. It is not an unconditional
proof of either tail proposition, nor a proof that the manuscript's LU theorem
provides `hsource`. The all-Schur extraction and exceptional-set bridges remain
separate source formalization work. The module's comments accurately disclose
this distinction.

## Concrete semantic checks

- `gaussianMatrix_probability_proved` proves probability-measure status for
  every dimension by the nested finite-product instance for the actual Gaussian
  factors. This genuinely supplies the mathematics of the same-signature
  probability obligation, under a distinct proved helper name; `Challenge`
  remains an intentionally unfilled reference interface.
- `exceedanceEvent_zero` proves that the explicit zero-dimensional event is
  empty for every real threshold.
- `exceedanceEvent_antitone` has the correct direction: increasing the
  threshold decreases the bad event. It keeps the same witness path.
- `growth_one` proves growth one for every nonzero scalar input. Since only
  the input stage is counted at dimension one, this has no missing pivot-path
  side condition. Its result is independent of the path argument.

None of these statements claims measurability, nonsingular-path existence,
Gaussian singular-nullity, or the manuscript's probabilistic estimate. Those
remaining facts are not inferred from the four checks.

## Numerical scope and disposition

The final written specification has been rechecked. Its implementation scope
contains only the exact numerical infrastructure fixture `log 2 < 7/10`.
The earlier optional Gaussian-density certificate is explicitly omitted;
there is no obligation to add unused numerical computation. The conditional
reduction uses symbolic inequalities and exact real analysis throughout.

**Approved.** No mathematical defect or hidden extra hypothesis was found in
the seven supporting theorem statements or their source proofs. Acceptance
is specific to the hashes above and to the disclosed conditional/local scope;
it does not assert that IE-06 itself has been proved in Lean.
