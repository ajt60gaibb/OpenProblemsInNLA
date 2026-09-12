# MI-29 independent statement referee 1

Date: 2026-09-12. Reviewer: OpenAI Codex AI agent `/root`, who did not author
these definitions or statements. **Verdict: approve this frozen boundary for
proof implementation after the second independent statement approval.**
This is a statement review, not a proof or human peer review.

I read the complete canonical README, `solution.tex` and `solution.md`, the
complete Definitions, Challenge and numerical plan. The three informal inputs
were compared byte-for-byte with upstream revision
`e7252e5307781a7c897bca6cb124f6ab838f6809`; their hashes are retained in
[the source identity record](statement-referee-1-evidence/sources.json).

## Full original target

The universal definition preserves every positive dimension, square complex
matrices, positive definite `A`, invertible Hermitian `B`, and every pair of
nonnegative **real** exponents. It does not require `B` positive definite,
commutation, integer exponents, a supplied spectral decomposition or extra
determinant hypotheses. `IsUnit B` expresses genuine invertibility in the
matrix ring. The inequality direction is the original right determinant at
most the left determinant.

The canonical target is the positive-definite/invertible formulation. The
source's separately mentioned semidefinite extension, the established `k=2`
case and the variant `B>0` are not substituted for it. The last selected
declaration negates the full canonical assertion itself. An admissible
`n=3,k=6,p=8` witness with a strict opposite inequality suffices to settle that
universal assertion negatively.

## Actual library semantics and analytic bridges

I inspected the pinned Mathlib definitions of positive semidefiniteness and
positive definiteness as Hermitian quadratic-form conditions, the scoped
matrix order `A≤B ↔ (B−A).PosSemidef`, and the scoped complex scalar order
`z≤w ↔ z.re≤w.re ∧ z.im=w.im`. Strict complex order similarly requires equal
imaginary parts. Thus scalar comparisons in the target are genuine real
comparisons once reality is proved, not consequences of incomparability.

The explicit call to `CFC.rpow` avoids the matrix representation's competing
pointwise real-power instance. Its actual definition is the **unital**
continuous functional calculus applied to the nonnegative-real power
function. The inspected `rpow_zero` and `rpow_natCast` APIs have exactly the
positive-semidefinite premise needed for identity at exponent zero and
agreement with matrix-ring natural powers. The actual matrix calculus is
constructed through the Hermitian spectral theorem; it is not a new formal
symbol with assumed properties.

`CFC.abs X` actually means `CFC.sqrt (star X * X)`, and matrix star is conjugate
transpose. The library's square-root and modulus-square identities act on
the true positive Gram matrix. The selected generic modulus theorem requires
both positivity and the eighth-power reduction to be proved for every `X`.
It does not supply them as assumptions to the counterexample.

The generic `comparison_positive_real` declaration requires the actual two
determinants to have zero imaginary parts and strictly positive real parts
under the original assumptions, including exponent-zero endpoints. Its
conclusions cannot narrow the universal target or silently become premises.
The natural-power agreement and modulus bridge are likewise explicit proof
obligations. The five selected signatures contain no hidden analytic axiom,
replaceable definition, assumed numeric output, or proof-dependent meaning.

## Exact numerical obligations

The diagonal `A` and scaled symmetric `B` exactly match Colbrook's witness.
The determinant `−1/125` proves the intended invertibility once connected to
the matrix-ring criterion. The negative diagonal of `B` and negative diagonal
of `−B` justify the additionally requested failures of semidefiniteness;
these are proved witness properties, not assumptions of the universal claim.

The Gram products retain the correct order: `|AB|⁸=(BA²B)⁴`, while
`|BA|⁸=(AB²A)⁴`. Both must follow from the actual Hermitian identities and CFC
bridge before algebraic evaluation. Interchanging these noncommuting products
would invalidate the result, and the selected statements do not do so.

I independently reconstructed both matrices and determinants using Python
`Fraction`, generic matrix multiplication, natural powers and the signed
six-permutation determinant formula. This yielded exactly:

- `det B = −1/125`;
- left determinant `136990346414301954149/61035156250000000000`;
- right determinant `4537743716162890657/1907348632812500000`;
- positive right-minus-left gap `21036678407451/156250000000000`.

[The numerical record](statement-referee-1-evidence/numerics.json) retains the
actual intermediate matrices, method and input hashes. This is an independent
statement precheck and supplies no Lean assumption. The optional polynomial
gap certificate is correctly an implementation aid rather than a required
replacement target. Exact algebra followed by one explicit kernel LeanCert
point check avoids interval subdivision and numerical spectral computation.

## Typechecking, trust and frozen bytes

An independent `lake build Challenge` exited zero, reporting 2710 jobs and
only the five deliberate isolated Challenge placeholders. The [command and
raw log](statement-referee-1-evidence/build.json) record this actual run.
No Proof or Solution implementation existed during this statement review.
The solution must never import Challenge, and all five exports must ultimately
pass kernel LeanCert trust assertions and Comparator with only the standard
three axioms. Final independent proof review and Linux verification remain
required even after this statement approval.

| Input | SHA256 |
|---|---|
| `NLA/MI29/Definitions.lean` | `c73bfb1856b3e1059ce2ef1e35f8314cb339edcc38b89d28780d38b122ce1a16` |
| `Challenge.lean` | `7ac10b3c284dc5f86dbbb90ef999d5b210540dd0fbdc0bfc60ee9621d25da3cf` |
| `NUMERICAL_TARGETS.md` | `892449f4f9107661242eca72c50d4f35652a4475ea94573daf2ad865c44e5af2` |

Any mathematical change to this boundary reopens review. The present source
retains Colbrook's mathematical authorship and credits George Stepaniants for
formalization with the approved Caltech department and university affiliation.
It discloses AI assistance without adding George's email or implying human
endorsement. No statement correction is requested.
