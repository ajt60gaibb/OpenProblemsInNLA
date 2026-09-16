# IE-04 independent complete mathematical source review

**Verdict: APPROVE the complete mathematical source, subject to the separate
mechanical gates.** No mathematical correction is requested. This is a
source-only referee report; it does not certify a successful complete Lean
build, actual Comparator acceptance, or final publication readiness.

Reviewer: `/root/next_inequalities`, an OpenAI Codex AI agent, 15 September 2026.
I did not implement these IE-04 proof modules. I previously independently
reviewed its statement boundary and the explicit product-measurable-space
repair. I formed this full-proof conclusion by reading the actual source,
canonical problem and manuscript; I did not use the other full-source referee's
conclusion as a substitute. I cover fidelity, mathematical correctness,
computation reduction, reuse/API, documentation and attribution under the
repository's scoped Tau Ceti protocol. This is not official Tau Ceti
certification or external human peer review.

## Exact reviewed inputs

`INPUTS.json` binds 27 current package files and five immutable canonical/reused
files. Its SHA-256 is
`a71e4cef672f460c2befe3bd74fba306c1acc886f8e7fec22762bb4401bb4bc8`.
The independent copies are retained in `source/` and `canonical/`. Every copy
was compared again with the current author tree; canonical copies were compared
with actual Git objects at
`8f04b905eb2e0827b6b84f37d9d080ae1f05b202`.

I read the complete IE-04 canonical README and `solution.md`, Definitions,
every one of the 21 Challenge declarations, and all 14 implementation-graph
files including Definitions and Solution. The graph includes Pivot, GEPP,
StrictPivots, Witness, Scalars, Robustness, Measurability, GaussianDensity,
GaussianBox, ProbabilityTail, Asymptotics and Final. I also read the numerical
targets, source correspondence, README, metadata, dependency pins, reuse
records and statement freeze. The current held repair hashes are:

| File | SHA-256 |
| --- | --- |
| `Robustness.lean` | `76ad88f2fe32fe9266d9638059009febc581d38ccd5dbc67fcddc66999f37e51` |
| `GaussianBox.lean` | `8dee995d61f75d0be79b425f1dcd30512f60f876c49cb065ceb608cdc61b8446` |
| `ProbabilityTail.lean` | `5124643d18caceba18c2ba5ec953a9401bda7d2ca758c18fd87c4069fd534040` |
| `Final.lean` | `2896d407818711dc8d77eacde26b2ee6520ee834121e583319a017783c0ccf72` |
| `Solution.lean` | `90e4047a7039cc49cec2dbb23f80e52ad9859bfe41e91eef875702304b7aa02c` |

The frozen boundary is unchanged:

| File | SHA-256 |
| --- | --- |
| Definitions | `22a1da11ce45d06f5dae0b14338b95f6e8d64505063ddf3638aabb374f85e762` |
| Challenge | `7a377349753ed51f8a2961158ca44a7e4a297e051bc5afdeb147bbb6f07bed84` |
| Numerical targets | `8c7d77ab3ae805cefb1ef4888f0c61b99294a855694fe8c98d616e1baea3d867` |
| Comparator configuration | `bbd679a65822269d13a007098590b1cef1ceb40683cfe952d85019ec51670ff6` |

All four frozen hashes and all three independent statement-review records
bound by `STATEMENT-FREEZE.json` match. The freeze records actual successful
statement elaboration before implementation; those deliberate Challenge holes
are not mathematical proofs. The historical draft comments in the frozen
files are preserved rather than rewritten after the freeze.

## Complete target and nonvacuity

The canonical target asks for positive universal real constants with the
displayed bound for every dimension, every real center of Euclidean operator
norm at most one, every allowed positive noise scale, every real threshold
at least one, and every admissible partial-pivoting tie choice. The formal
definition retains those quantifiers, uses real powers for the constants,
and takes a genuine nested finite product of standard Gaussian measures.
`spectralNorm` uses the pinned `Matrix.Norms.L2Operator` instance; I checked its
identification with continuous linear maps on Euclidean space in Mathlib.
It is not an entrywise or Frobenius substitute.

The final counterexample fixes only permissible witnesses: center `I`, noise
one, and a dimension and real threshold chosen after arbitrary proposed
positive `c₁,c₂`. It proves a strict probability violation for every admissible
rule in that same instance. Choosing this subfamily is sufficient to negate
the full original universal claim. No norm bound on the high-growth matrix
`W` is smuggled in as a bound on the smoothing center.

`AdmissibleRule` explicitly requires validity on all nonsingular matrices and
measurability of the induced growth function. It does not assert measurability
of the path-valued selector itself; induced-growth measurability is the exact
property needed for the probability statement. This permits a larger class
of selectors without weakening the negative conclusion. The actual ascending
first-available selector is proved valid and measurable, so this class is
not empty and the final contradiction is not vacuous.

The tail event includes `det A ≠ 0`. This is a deliberate stronger witness
requirement: it is a subset of any total-extension tail event agreeing with
GEPP on nonsingular inputs. A lower bound already violating the proposed
upper bound on this subset suffices. Neither almost-sure nonsingularity nor
almost-sure absence of ties is assumed to identify probability expressions.
All matrices in the box are proved nonsingular and have strict pivots.

## Actual elimination and full-box argument

The definitions swap current row positions only and then use the exact Schur
formula on the remaining active block. Padded zeros outside that block do not
alter its maximum. The growth numerator ranges over all `n` actual stages,
including the input and final scalar stage, and the denominator is the true
finite maximum of absolute input entries. GEPP proves entry-maximum attainment
for positive dimensions and proves its positivity before division.

The first-pivot scan is related to an actual first-occurring `List.argmax`;
it maximizes active-column magnitude and retains the least current index on
ties. Forward supported-vector injectivity supplies a nonzero active column
at every nonsingular stage. This avoids the false assertion that a padded
full-size stage matrix is nonsingular. The reverse supported-vector argument
in StrictPivots proves nonsingularity from every nonzero actual pivot, with
the terminal support condition supplying the base case. Strict maxima then
force every admissible path to agree, by induction on actual trajectories.

Witness proves the exact source stages in arbitrary dimension: nonfinal
columns retain their triangular pattern, the final column is `(3/2)^k`, and
the final pivot attains the maximum growth `(3/2)^(n−1)`. It is not a
dimension-specific evaluation.

The scalar budget identity is exact:
`(n+2)(n−1) − (n²+n+1) = −3`. Thus
`B^(n−1) δ = 1/8`, and every earlier stage budget is at most `1/8`.
For an error bound `e≤1/8`, the perturbed pivot is at least `7/8` and the
competitors have absolute value at most `5/8`; the strict gap is `1/4`.
The multiplier satisfies `|a/p|≤5/7` and
`|a/p+1/2|≤(12/7)e≤2e`, with a separately proved positive denominator.
The exact scalar update decomposition gives an error at most
`(1+5/7+2·2^n)e≤2^(n+2)e`. These estimates apply to all real permitted
operands. Robustness lifts them by symbolic induction to every matrix in
the entire closed entrywise box, not to selected perturbations.

The final pivot is at least `g−1/8`, `g=(3/2)^(n−1)≥1`, while the input
maximum is positive and at most `9/8`. The desired strict growth inequality
has a uniform positive margin: `g−1/8−(9/8)(g/2)≥5/16`.
Strictness is retained at the closed-box boundary and at the final stage.

## Genuine Gaussian measure and arbitrary real constants

Measurability proves the finite selector, selected Schur maps, trajectories,
finite NNReal maxima, determinant, smoothed input and actual tail event in
the ordinary product sigma algebra. The Gaussian measure is a probability
measure by the genuine finite-product instance. These claims are proved
rather than left as assumptions on an unspecified random input.

GaussianDensity uses LeanCert once, in kernel mode, for
`1/8 < exp(−2)`. Its result is consumed by exponential monotonicity for every
`|z|≤2`. Together with the standard positive square root and `π<4`, this gives
the actual density bound `1/32 < gaussianPDFReal 0 1 z`. Gaussian intervals
are integrated using the actual density formula, monotonicity of the
nonnegative integral and the exact Lebesgue length `2δ`. No numerical
integration, assumed Gaussian mass, or dimension-dependent interval search
is used.

GaussianBox identifies the box with an actual nested Cartesian product,
proves measurability, and applies `Measure.pi_pi` at both levels. The centers
`W−I` have absolute entries at most one. Every interval therefore contributes
at least `δ/16`; symbolic finite products give exactly
`2^(−n²(n²+n+5))`. ProbabilityTail transports the box into the actual
nonsingular high-growth event for every admissible rule and applies measure
monotonicity in the correct direction.

Asymptotics imports the genuine theorem that `exp(bx)/x^s` tends to infinity
for every real `s` and positive `b`. Taking `s=c₁+4` is valid for the entire
real quantifier, not just integer exponents. Its algebraic identity is
`(3/2)^n/n^(c₁+4)=3xₙ/n^4`, with all divisions justified for `n≥2`.
The exact quartic bound on `Kₙ` then gives both `xₙ≥1` and `Kₙ<c₂xₙ` for
some finite dimension. Final uses strict monotonicity of the real power of
two, the positive `ENNReal.ofReal` embedding, the true identity norm and the
first-available rule to contradict the full original statement.

The optional zero-center corollary and shorthand probability bound in the
manuscript are not claimed as separately exported results. They are not
needed for the canonical negative resolution. The exact radius and main
probability exponent agree with the source.

## Independent checks, reuse and trust limits

The independent `independent_checks.py` completed 359 static and exact-rational
checks in under a second without Lean, Lake, network access or dependency
downloads. It checks all input hashes, all four frozen files, all three bound
statement-review records, the complete acyclic proof import closure, and the
unique full textual type of every exported theorem against its Challenge.
All 21 targets occur in Comparator order and request kernel trust assertions
in Solution. No Challenge import, source hole, custom axiom, native decision,
unsafe implementation or tactic-time execution hook occurs in the proof graph.
Static comparison is supplementary and does not replace actual Comparator.

The same script independently rechecks all 17 generic GEPP definitions and
the complete Pivot/GEPP proof reuse against immutable IE-05 sources. Only the
documented namespace/comments and omitted unrelated IE-05 corollary differ.
It records the pinned primary Mathlib API source hashes and verifies their
bytes against the claimed Mathlib commit. The reused APIs are semantically
appropriate; no unproved external GEPP or probabilistic lemma is substituted.

Supplementary rational checks include the strict scalar margins, an independent
series upper bound `exp(2)<8`, exact witness trajectories and finite perturbed
examples, and exact illustrative contradiction dimensions with nonintegral
`c₁` on square dimensions. Their finite scope is explicit; universality rests
on the source proofs reviewed above. `CHECKS.json` has SHA-256
`28e6c5a2672a65c1993faab36dc81d34929598cf2747580e09906636e1c889e9`.
`CONTRACTS.json`, `IMPORT-CLOSURE.json` and `API-SOURCES.json` retain the
detailed independent evidence.

I inspected the available run 35029609317 IE-04 module transcript and the
three held repair diffs. That earlier run failed in Robustness and GaussianBox;
LeanCert correctly rejected their error-generated `sorryAx` dependencies.
The current repairs explicitly rewrite the selected Schur step, supply the
nested Cartesian-product membership arguments and the two product-measure
applications, and expose identity-plus-input in ProbabilityTail. They preserve
the mathematical proof path and every frozen target. This report does not
infer acceptance of those repairs or downstream modules from the earlier
partial success. It also does not independently authenticate a final runtime
receipt, because no final canonical receipt is part of this review phase.

The package preserves George Stepaniants's mathematical and formalization
credit, Department of Computing and Mathematical Sciences, California
Institute of Technology, and the source conjecture's historical attribution.
No email is published. Substantial AI assistance, reused IE-05 authorship and
licenses, Schiffer/Forsythe workflow references, and the present verification
limits are disclosed. Exact scalar reductions keep computation modest.

Before this result is described or counted as Lean verified, the complete
current graph must compile on the authorized Linux runner; the actual
canonical Comparator, default-kernel replay, transitive axiom audit and
negative controls must pass on source-matched bytes; and both independent
referees must reconcile the accepted final source and actual evidence. Any
subsequent source change requires an explicit reviewed addendum.
