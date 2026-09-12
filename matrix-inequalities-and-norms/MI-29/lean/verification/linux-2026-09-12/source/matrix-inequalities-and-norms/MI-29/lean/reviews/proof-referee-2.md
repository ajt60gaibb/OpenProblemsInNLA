# MI-29 independent final proof referee 2

**Verdict: PASS for the completed mathematical proof at the hashes below.** The five selected exports prove the genuine CFC bridges, positive-real determinant interpretation, admissible strict counterexample, and negation of the complete original all-real-exponent conjecture. No mathematical correction is requested. Final publication metadata and authoritative Linux Comparator verification remain separate pending gates; this report alone does not promote the catalog status.

Reviewer: Codex AI agent `/root/formal_review_standards`, 12 September 2026. The reviewer independently approved the frozen statements before implementation and did not author or modify the mathematical proof. This is independent agent review, not external human peer review or an official Tau Ceti service verdict.

## Bound sources and independent checks

I reviewed the complete canonical README, Colbrook standalone proof and submission note, both statement reports, Definitions, Challenge, numerical plan, the full Proof and Solution, and the implementer's completion record. The three canonical informal files remain byte-identical to upstream revision `e7252e5307781a7c897bca6cb124f6ab838f6809`. The definitions, Challenge, and numerical obligations remain byte-identical to the boundary approved before implementation.

| Mathematical input | SHA-256 |
| --- | --- |
| `NLA/MI29/Definitions.lean` | `c73bfb1856b3e1059ce2ef1e35f8314cb339edcc38b89d28780d38b122ce1a16` |
| `Challenge.lean` | `7ac10b3c284dc5f86dbbb90ef999d5b210540dd0fbdc0bfc60ee9621d25da3cf` |
| `NUMERICAL_TARGETS.md` | `892449f4f9107661242eca72c50d4f35652a4475ea94573daf2ad865c44e5af2` |
| `NLA/MI29/Proof.lean` | `b683a2c0faebd595f7d9f2b0973a9955cf39443c924f7dfd05b3b60e16bdadf5` |
| `Solution.lean` | `0cb66f4fc4d379f1f91699ba16b6feda93710798fe414fa09b242cd12076ce11` |
| Canonical README | `8eca6404040fe727741f760e37adb89eab281bde1f5e9acba7d4ee6efb84db65` |
| Full informal `solution.tex` | `0c3c86150c042a4111812d95eca8dc38d53015c124e69777398ddd833dc8551f` |

The [complete input record](../verification/referee-2/inputs.sha256.json) additionally binds package files, prior reviews, and author build evidence. All five public Solution signatures match the frozen Challenge signatures literally after whitespace normalization; see [statement identity](../verification/referee-2/statement-identity.json). This source-level check supplements the still-required isolated Comparator run.

The reviewer independently ran `lake build Solution`, then directly re-elaborated `NLA/MI29/Definitions.lean`, `NLA/MI29/Proof.lean`, and `Solution.lean`. All exited zero, with no warnings. The build graph had 3147 jobs with existing dependency artifacts reused. Direct Definitions, Proof, and Solution re-elaboration took approximately 11.3, 17.3, and 6.9 seconds respectively. The [command record](../verification/referee-2/checks.json) and raw [Definitions](../verification/referee-2/reelaborate-definitions.log), [Proof](../verification/referee-2/reelaborate-proof.log), and [Solution](../verification/referee-2/reelaborate-solution.log) logs retain the actual results. This was Lean 4.33.1 on macOS arm64; it is not a fresh Linux dependency rebuild or Comparator result.

## Original target and analytic correctness

The universal definition retains every positive dimension, complex square matrices, positive definite `A`, invertible Hermitian `B`, and arbitrary **real** nonnegative `k,p`. It does not add commutation, positivity of `B`, a supplied spectral decomposition, integer-exponent restrictions, or numerical certificates. The final theorem negates that definition itself. A valid witness at `n=3,k=6,p=8` therefore resolves the complete canonical question negatively.

The actual CFC/matrix/order instances were inspected during statement review and their bytes are unchanged. The implementation uses the corresponding proved library APIs correctly:

1. `spectralPower_natCast_proved` applies `CFC.rpow_natCast` to `hA.nonneg`. This proves agreement of the explicit **unital** spectral power with actual matrix-ring powers for every PSD matrix and natural exponent, including zero. It is not pointwise exponentiation.
2. `modulus_power_eight_proved` unfolds the actual modulus as the CFC square root of `XᴴX`, proves its PSD property using `CFC.abs_nonneg`, and applies `CFC.abs_sq`. Natural-power agreement and `pow_mul` then give `|X|⁸=(XᴴX)^4`. These are proved generic conclusions for arbitrary square complex `X`, not analytic assumptions inserted into the counterexample.
3. `spectralPower_posDef` uses `IsStrictlyPositive.rpow` together with Mathlib's equivalence between strict positivity and matrix positive definiteness. Adding the proved PSD modulus-power term gives positive definite left and right matrices. `Matrix.PosDef.det_pos` and the actual `Complex.pos_iff` yield zero determinant imaginary parts and strictly positive real parts.

The generic positivity implementation does not need several of the public hypotheses because CFC's totalized power is always nonnegative and a real spectral power of a positive definite matrix is positive definite. This proves a stronger auxiliary positivity fact; it does not weaken the conjecture or supply a fallback interpretation for its witness. Under the canonical hypotheses the powers have their intended spectral meaning, and at the witness all required CFC-to-ring identities are proved explicitly. The public positivity export preserves the frozen original hypotheses, including exponent-zero endpoints.

`witnessA_posDef` proves actual complex positive definiteness of `diag(2,1,1/2)`, not entrywise nonnegativity of a general matrix. `witnessB_hermitian` checks its conjugate-transpose equality; `witnessB_det` proves `det B=-1/125`, and the genuine matrix determinant/unit criterion yields `IsUnit B`. Negative diagonal entries of `B` and `-B` contradict their respective quadratic-form PSD predicates. Thus the allowed indefinite factor is proved admissible without assuming an inverse or changing the problem to a positive-`B` version.

The Gram identities retain the essential order: `(AB)ᴴ(AB)=BA²B`, whereas `(BA)ᴴ(BA)=AB²A`. They follow from actual Hermitian conjugation and associativity, and the two spectral eighth-power witness reductions apply them in the correct locations.

## Exact certificates and complete negative conclusion

The private matrices are verified intermediates, not assumed certificates. `Matrix.diagonal_pow` establishes `A⁶`. Each Gram matrix is checked entrywise against its actual product, then squared; the verified square is squared again to obtain the fourth power. The two resulting sums are checked entrywise against `leftMatrix` and `rightMatrix`, which still contain the original spectral definitions. Only after these connections are proved does `Matrix.det_fin_three` evaluate the determinants.

I independently recomputed the matrix operations with exact Python `Fraction` arithmetic, parsed all six new private matrix literals from Proof, and compared every entry to its reconstructed value. The diagonal sixth power also matches. The [certificate reconstruction](../verification/referee-2/exact-certificate-reconstruction.json) confirms:

- left determinant `136990346414301954149 / 61035156250000000000`;
- right determinant `4537743716162890657 / 1907348632812500000`;
- right minus left `21036678407451 / 156250000000000 > 0`.

This is an auxiliary audit, not a premise or substitute for the Lean matrix equalities. The earlier independent statement precheck also verifies the optional source polynomial, but the implementation appropriately avoids proving it redundantly.

`witness_strict_violation` transports the positive real gap through its exact complex value, including imaginary part zero, and applies `sub_pos`. It therefore proves a strict comparison in the genuine complex partial order, not an incomparability artifact. `counterexample_proved` assembles every admissibility condition and analytic/numerical identity as a conclusion. `not_modulusDeterminantConjecture_proved` instantiates every original quantifier at the witness and contradicts the resulting weak inequality. No additional premise is introduced. The established `k=2` case, positive-`B` variants, and separate singular-input discussion remain outside the claimed formalization.

## LeanCert and transitive trust

The minimal import is the pinned `LeanCert.Tactic.IntervalAuto.PointIneq`; no LeanCert or mathlib dependency source was modified. All ten checked-out dependency commits match `lake-manifest.json`, with no tracked source changes. The [dependency record](../verification/referee-2/dependencies.json) binds the inspected CFC/order files and LeanCert point-tactic/trust implementation.

The source sets global kernel trust and explicitly calls `interval_decide (trust := kernel)` for `scalar_gap_positive`. Inspection of the pinned verification router confirms that explicit kernel mode calls kernel certificate closure and does not fall back to native execution. Its `#assert_trust kernel` command collects transitive axioms and rejects sorry, native-compiler, and custom axioms.

I also independently printed the actual scalar proof and its consumer. The [inspection log](../verification/referee-2/inspection.log) shows the retained `LeanCert.Validity.verify_strict_upper_bound_dyadic_checked` certificate for the constant zero on the point interval `[0,0]`, with rational bound equal to the positive gap and precision `-53`. It is an actual LeanCert certificate, not a bypassed or unused demonstration. `witness_strict_violation` visibly depends on `scalar_gap_positive`, and the full conjecture negation depends on that strict violation.

All ten audited internal declarations and all five public exports passed their source `#assert_trust kernel` commands during independent re-elaboration. Every corresponding `#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Proof and Solution contain no sorry, admit, custom axiom, native tactic, unsafe declaration, external implementation, custom elaborator, or local instance override. Their import chain excludes Challenge and its five deliberate placeholders.

## Scoped referee conclusion

The applicable [Tau Ceti review rubrics](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics) were applied to correctness, fidelity, reuse, API, proof quality, documentation, scope, and attribution. The proof reuses Mathlib's actual CFC, positivity, determinant, and matrix-power interfaces; verified intermediate squares avoid large repeated expansions. One scalar point certificate suffices. No interval subdivision, parameter search, numerical eigenvalue calculation, or approximate matrix square root is needed.

The files preserve Matthew J. Colbrook's mathematical authorship and George Stepaniants's formalization authorship, with the Department of Computing and Mathematical Sciences, California Institute of Technology affiliation and no George Stepaniants email. Independent agent assistance and review are disclosed without implying human endorsement. Wrapper theorems preserve the deliberately frozen Comparator API rather than adding a competing target.

**No blocking mathematical or trust finding remains on these exact files.** Final publication metadata, a second final proof approval, and the actual Linux Comparator run with all five exports, no definition holes, and only the standard three axioms remain required before catalog promotion. Any mathematical source or definition change reopens the relevant review gates.
