# Second-eye semantic review: MI-06 and MI-07

**Verdict: PASS for both original targets.** No semantic mismatch, hidden analytic premise, or weakened unitary quantifier was found.

Reviewer: `/root/audit_tr07`, 12 September 2026. Read-only review of PR #167 at `cdf6e1c75c29363bd04f1b13beaa6ba679a698bb` and PR #166 at `1dff432524c4dfb4ccd272c906ab7c701855a420`.

This bounded second review covers both canonical statements, both Definitions/Challenge/Solution modules, both complete analytic Proof modules, and MI-07 FunctionalCalculus. I independently checked the argument from those sources. The coordinator separately authenticates the Linux receipts, input hashes, declaration/axiom coverage and rejection controls; I did not rerun Lean or claim to repeat that operational verification. Both canonical Problem statement sections remain byte-identical to origin/main.

## MI-06

`matrixModulus` is genuine CFC.abs, with its equality to CFC.sqrt of `X* X` and positivity proved for every complex matrix. `symmetricModulus` takes the ordinary arithmetic average of the two positive polar factors. `unitaryConjugate` uses actual members of the complex matrix unitary group. Scoped MatrixOrder is explicitly linked in the proof to positivity of right minus left through `Matrix.le_iff`, so the displayed order is Loewner order. The final negation quantifies over every positive dimension and every complex pair; a fixed dimension-three witness correctly refutes it.

All six proposed square-root tables are proved positive semidefinite and to square to the corresponding Gram matrices. CFC square-root uniqueness identifies them, rather than assuming them. I checked the resulting averages and the decompositions `S(A)=I/8+aa*/10-E_A/8`, `S(B)=I/8+bb*/10-E_B/8`, with `a=(3,1,0)` and `b=(3,0,1)`. The missing-coordinate matrices are PSD.

For every complex unitary pair, the map `w -> (<Ua,w>,<Vb,w>)` is complex linear from dimension three to dimension two. The rank argument proves a nonzero kernel vector, without requiring independence of the two directions. `squaredLength` is the sum of complex norm squares, and its strict positivity is proved from nonzeroness. Taking the real part of the quadratic form loses no order information needed here: PSD differences give nonnegative real quadratic forms. Each conjugated rank-one term vanishes on this common vector; subtracting a PSD term leaves each right summand at most `||w||²/8`. The actual left average is `diag(3/4,3/8,3/8)`, hence at least `3||w||²/8`. The certified scalar comparison gives `sqrt(2)/4 < 3/8`, establishing the strict contradiction with the original factor sqrt(2).

No assumption in `witness_quadratic_bounds` or `counterexample` postulates these inequalities. Their only parameters are the arbitrary genuine unitaries. The stronger assertion that no finite constant works is correctly stated to lie outside these formal exports; this does not limit resolution of the original factor-sqrt(2) target.

## MI-07

The root sequence uses all positive integer exponents via `r+1`, actual matrix ring powers inside, and the positive real CFC power outside. The one-index shift does not alter the canonical limit. `spectralNorm` explicitly scopes the Euclidean operator norm, and the exported convergence equivalence uses that norm rather than a default entrywise norm.

`maximalModulus` uses `limUnder`, which is totalized when convergence is absent. This is not a counterexample loophole: actual convergence is proved unconditionally at A, B, and A+B, and each modulus identity consumes the corresponding Tendsto proof. A counterexample at these three convergent arguments suffices to refute the original universal assertion regardless of how the definition is extended elsewhere. Generic convergence or a generic Olson-order theorem is unnecessary for this negative resolution.

The exact polar factors are established by PSD square-root uniqueness. A is the first coordinate projection; the sum's right projection is onto `(12/13,5/13)`. The sum of these two projections is positive definite: it is PSD and has nonzero determinant `25/169`. The CFC helper for positive projection powers explicitly requires a positive exponent and preserves the zero eigenspace. It does not replace the limit of powers of a singular projection by its totalized exponent-zero value. Continuity at exponent zero is invoked only for the positive definite sum, whose eigenvalues are strictly positive.

The actual root sequences therefore have limits A, `(5/12)I`, and `(13/12)I`. For A the scalar factor is `2^(1/(r+1))`; for B the sequence is already constant; for A+B it is `(13/12)` times the positive definite projection sum raised to `1/(r+1)`. These are the stated canonical finite-dimensional limits. Trace invariance holds for every complex unitary, not only real or specially chosen matrices. It gives right trace `11/6`, left trace `13/6`, and right-minus-left trace `-1/3`. PSD domination would force this difference trace nonnegative, producing the contradiction. No assumed eigenvalues, assumed limits, or external convergence premise supports the counterexample.

## Disposition

The six MI-06 and seven MI-07 Challenge statements correspond to the original targets, and the Solution modules restate them without adding premises. Their proof imports do not include Challenge. Source scans found no `sorry`, custom axiom, unsafe/native shortcut, or replacement order/norm instance in the completed modules; Challenge's intentional placeholders are outside those proof imports. With the coordinator's authenticated kernel/comparator evidence and final integration checks, **Lean verified** is justified for both original conjectures. No source edit is needed from this second review.
