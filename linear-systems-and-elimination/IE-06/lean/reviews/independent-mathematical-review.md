# IE-06 independent mathematical review before implementation

Review date: 2026-10-06. Reviewer: independent mathematical-review agent.
This review was written before examining any Lean implementation. It reviews
the mathematical specification, not the correctness of the manuscript's proof.

## Material examined and preservation

I independently compared the working canonical
`linear-systems-and-elimination/IE-06/README.md` with its `HEAD` version.
The original context, growth definition, problem statement, and express
exclusions (matching lower bound, limiting distribution, and IE-04's uniform
smoothed target) are intact. The working page adds a resolution and changes
status; those changes predate this review. The canonical ID/path and original
problem must remain intact. No new numbered problem is required.

The independent primary-source check covered Urschel,
[*On the Growth Factor of Random Matrices*, arXiv:2610.06785v1](https://arxiv.org/html/2610.06785v1),
the introduction, Theorem 1.4, Section 5.1, and the proof of Proposition 5.1.
The paper defines growth using the lower/upper triangular factors and fixes a
deterministic tie rule. Theorem 1.4 gives a square-root threshold times
`exp(Cα sqrt(log n))` and failure probability strictly below `n^(-α)`.
Section 5.1 explicitly strengthens the intermediate goal to all active Schur
complement entries; the Proposition 5.1 proof takes that union bound. Its final
normalization uses the high-probability event `‖G‖max ≥ 1`. Thus the canonical
all-Schur target requires a bridge to the paper's displayed theorem, rather
than a definitional identification of the two growth quantities.

## Exact canonical target

For each positive integer `n`, let `γn` be the product probability measure of
`n²` independent real standard Gaussians, on the space of real `n × n` matrices.
An admissible partial-pivoting path consists of exact row permutations and
elimination steps. Every chosen pivot has largest absolute value in the active
first column, with equality permitted. Each active matrix after eliminating a
pivot is the corresponding exact Schur complement, not the stored combined
LU array. Include the input as stage zero and the final `1 × 1` matrix.

For a nonsingular input `A` and an admissible path `p`, set

`ρ(A,p) = (max over active stages and entries of their absolute values) / ‖A‖max`.

A precise bad event at threshold `x` is

`B(n,x) = { A | det A ≠ 0 and there exists an admissible PP path p with ρ(A,p) > x }`.

Then the original IE-06 target is exactly the proposition

`for every real η > 0, γn(B(n, n^(1/2 + η))) tends to 0 as n tends to infinity`.

The existential path in the bad event makes its complement the desired
universal guarantee over admissible tie choices. Replacing it by one selected
path would require a separate almost-sure tie-uniqueness argument. Including
`det A ≠ 0` is an explicit convention on the null set excluded by the original
statement; do not condition the Gaussian law on success of elimination.
An equivalent implementation may totalize growth on singular matrices, but
must specify the value and eventually justify almost-sure nonsingularity.

The dimension-zero convention may be chosen for total Lean definitions, since
finitely many dimensions do not alter the limit. It must not infect the
positive-dimensional definition through empty maxima or division by zero.

## Proposed scope and classification

1. **Solved in the source; formal statement only unless actually proved:**
   the canonical limit proposition above. It remains IE-06 regardless of status.
2. **Supporting solved source statement:** the exact Theorem 1.4 tail bound for
   the paper's LU growth. Quantifiers are `∀ α > 0, ∃ Cα, ∃ nα, ∀ n ≥ nα`;
   `Cα` and `nα` cannot depend on the sampled matrix or on `n`.
3. **Separately labeled bridge/strengthening:** an all-Schur tail statement at
   the same asymptotic scale. This is extracted from the argument, not the
   literal displayed conclusion of Theorem 1.4. It must not be labeled a
   verbatim theorem statement. Quantify over every admissible path, or add a
   clearly identified almost-sure bridge from the manuscript's tie rule.
4. **Partial historical progress:** the final-pivot result and earlier
   polynomial bounds are context, not additional permanent IE-06 problems.
   Do not fabricate their constants or exact quantifiers. The primary
   versioned Trefethen arXiv abstract/HTML/PDF endpoints were unavailable through
   the browsing tool during this independent check. A subsequent check of its
   [unversioned abstract](https://arxiv.org/abs/2610.04761) confirms the final-pivot
   scope, but supplies no exact numerical theorem. No exact numerical statement
   from that source is approved here. A separately verified source statement
   can be added to the reviewed scope later.
5. **Open mathematical targets:** the retained IE-06 upper-exponent problem
   is no longer classified as mathematically open by the supplied page. No
   lower-bound, Gumbel-law, constant-limit, smoothed, or no-pivoting problem
   should be introduced to populate an artificial “open” bucket. Open
   formalization obligations can be recorded as such, separately from
   mathematical status.

## Independent derivation checks for the bridge

For positive `η` and nonnegative `C`, whenever
`log n ≥ (C / η)^2`, monotonicity of square root gives
`C sqrt(log n) ≤ η log n`. Consequently the subpower correction is eventually
at most `n^η`. If `C` is initially arbitrary, replace it by `max C 0`, which only
enlarges the upper threshold. This is an exact real-analysis statement; no
decimal search, sampled dimensions, or floating-point approximation is needed.

If a threshold bound holds outside events of probabilities `n^(-a)` and
`q^(n²)`, with `0 ≤ q < 1`, then union bounds yield their sum. To claim the
strict tail `n^(-α)` with coefficient one, use slack in the auxiliary exponent
(for example `a = α + 1`) and enlarge the dimension cutoff. Alternatively use
the sum directly to prove the canonical limit. Do not silently identify a sum
of failure probabilities with one of its summands.

For a Gaussian input, `P(‖G‖max < 1) = P(|Z| < 1)^(n²)` by independent entries.
The only qualitative fact required for the limit is `P(|Z| < 1) < 1`.
Any numerical certificate for this fact is optional and should expose its
exact interval and endpoint convention. Neither Monte Carlo nor a finite
list of dimensions proves the universal probability or asymptotic target.

## Hazards the independent code review must exclude

- An uninterpreted growth function or arbitrary probability sequence passed in
  as a parameter and then advertised as the concrete Gaussian matrix target.
- An arbitrary nonempty path subtype whose construction does not enforce row
  permutation, maximum-column pivots, nonzero pivots, and Schur recursion.
- Recording only pivot magnitudes or entries of `U` when the target requires
  every entry of every active Schur complement.
- Multiplying or dividing the threshold by an unstated norm of the input.
- Replacing the exact `1/2 + η` exponent by a fixed exponent or finite range.
- Proving a conditional implication and recording the premise itself as
  kernel-verified, or introducing the source theorem as an axiom.
- Treating an elaborated `def ... : Prop` as a theorem proof. Compiled
  statements, checked comparator proofs, and checked numerical lemmas are
  distinct accomplishments and must be reported separately.
- Unspecified measurability. A Lean measure can be applied to any set, but
  proving event measurability or deliberately documenting the outer-measure
  convention remains necessary for a full probabilistic proof.

## Preimplementation disposition

Approved mathematical direction: a faithful concrete all-Schur PP limit
statement; separately identified source-tail statement and extraction bridge;
explicit unresolved proof obligations; minimal exact scalar certificates.
This approval does not cover arbitrary changes to scope, invented partial
results, a full proof claim, or Lean definitions not yet reviewed.

## Second-stage review of the authored specification

I read `statement-specification.md` before root-agent implementation began,
and independently inspected the proposed reusable definitions in
`linear-systems-and-elimination/IE-04/lean/NLA/IE04/Definitions.lean`.
Those definitions use actual current-row swaps, a guarded active Schur update,
maximum-column pivots, all `n` active stages, and the original entry maximum as
denominator. Recording a stage maximum before its row swap is valid because
the swap only permutes active rows. The nested finite product of
`gaussianReal 0 1` specifies the intended law.

The following exact mathematical statements are approved for implementation:

- The original all-path bad-event probability converges to zero for every
  positive real upper-exponent excess, represented either by `Tendsto` in
  nonnegative extended reals or the written epsilon–cutoff form.
- The stronger all-Schur tail proposition, with `∀ α > 0`, positive `C`, a
  natural cutoff at least two, and strict failure probability below `n^(-α)`.
  It is an extracted source strengthening, not a literal transcription of the
  paper's differently defined LU theorem.
- The conditional implication from that stronger proposition to the original
  target. Taking `α = 1`, eventually comparing thresholds as above, and letting
  `1/n` tend to zero suffices. The source proposition remains an explicit
  premise unless its random-matrix proof is supplied independently.
- For every dimension the nested Gaussian measure is a probability measure;
  every concretely defined finite-path exceedance event is measurable;
  every nonsingular input has an admissible path; the singular event has
  Gaussian measure zero. These are valid separate semantic obligations,
  not assumptions to be silently substituted for proofs.
- The optional exact scalar inequality `sqrt(2 / π) < 4/5`, and the alternative
  sufficient estimate `π > 25/8`, are correct. Its connection to the Gaussian
  denominator event still requires the separately stated density argument.
  The existing shared-infrastructure control `log 2 < 7/10` is also correct
  and is not an IE-06 numerical target.

Two implementation/documentation alignment requests were sent to the author
and coordinator before this approval: explicitly preserve the specification's
empty-dimensional empty event (a `0 < n` guard suffices); and distinguish
isolated, labeled unproved `Challenge` interfaces from proof products in the
trust paragraph. A deliberate placeholder may express a requested proof
obligation but cannot be counted as a verified theorem. No `Solution` or
full-source-proof claim is approved.

Disposition: approved to implement the above mathematical statements, with
the two alignment points resolved and a subsequent independent code review.
