# MI-23 independent statement referee 2 — PASS

Date: 12 September 2026. Reviewer: OpenAI Codex agent `/root`, independent of statement author `/root/formal_review_standards`. **Approve the frozen eight-export boundary for implementation. No statement correction is required.** This is statement and numerical-specification review, not a completed proof or Linux verification.

I independently read the complete canonical target, Colbrook's complete source TeX, every definition and Challenge signature, and the full numerical plan. I inspected the relevant actual Mathlib CFC, characteristic-polynomial, spectral-list and Euclidean operator-norm APIs, performed fresh statement elaboration, and reconstructed the rational witness independently. All 17 frozen project inputs and the three original source files remain unchanged, and no Proof or Solution implementation exists. My mathematical conclusions were reached independently of referee 1's final report.

## Complete target and spectral semantics

The conjecture retains every positive dimension, arbitrary complex positive definite A and B, all real r,s,p,t with p≥1 and t∈[0,1], and both original regions: r,s≥1 or r,s≤0. In particular, neither exponent is restricted to a natural or rational value, and t=0,1 and zero/negative r,s remain included. The factor order and both occurrences of A^(−1/2) in the generalized mean match the source. The right exponent is exactly p(r+s−1). The fixed witness is used to negate this complete assertion; it does not replace the quantified target.

All real powers are genuine `CFC.rpow` in the complex matrix algebra with actual PSD matrix order. I checked its unital CFC definition and the relevant composition, natural-power and inverse-power identities in the pinned library. The generic positive-powers-and-means export requires positive definiteness for every real exponent, including negative and zero exponents. Thus the products used in the full conjecture meet the intended positive-definite factor hypotheses throughout its entire parameter domain.

The eigenvalue list is made from every actual complex characteristic-polynomial root, with algebraic multiplicity, mapped to its real part and sorted decreasingly. This representation is legitimate on the intended products only with the generic semantic theorem required by the second export. That theorem proves an explicit invertible similarity to S=Y^(1/2) X Y^(1/2), S positive definite, both inverse identities, characteristic-polynomial equality and all list properties. The required reverse multiset equality between the original complex roots and the complex embedding of the sorted real list prevents the real-part map from discarding nonreal components or multiplicities. Exact length n, strict positivity, decreasing order and product equal to the genuine determinant are conclusions, not assumptions.

I inspected Mathlib's actual sorted-root/eigenvalue theorem: it identifies this precise decreasing root list with the Hermitian spectral theorem's eigenvalues, retaining all multiplicities. The genuine characteristic-polynomial conjugation/commutation identities support transport through the similarity. No fallback Hermitian matrix, supplied eigenvalue table or assumed spectral decomposition replaces the original product.

`LogMajorized` requires equal list lengths, every nonempty proper prefix-product inequality and equality of the full products. Together with the generic spectral semantics this is exactly the canonical positive decreasing vector relation. It is not merely weak log-majorization or its first inequality. The largest-eigenvalue helper uses the first element of that actual list. Its zero default must be excluded using positive dimension and the proved list length before any norm bridge or contradiction relies on it. The n=1 full-product condition is retained, even though the chosen counterexample is three-dimensional.

## Generic analytic bridges and exact witness

The third export requires, for every positive-dimensional positive-definite X,Y, the actual identity

largestEigenvalue(X²Y²) = operatorNorm(XY)².

Its justification is the invertible similarity of X²Y² to YX²Y=(XY)*(XY), followed by the genuine spectral theorem for a positive Gram matrix. The matrix product may be non-Hermitian, so this bridge must operate through characteristic polynomials and the actual sorted list; simply applying a Hermitian API to X²Y² would be invalid. The theorem is correctly stated as a conclusion rather than a hypothesis or custom eigenvalue definition.

The operator norm explicitly uses `Matrix.toEuclideanCLM` on complex Euclidean space. Fresh elaboration confirms `ContinuousLinearMap.hasOpNorm` on that space. The fourth export requires the generic squared-entry lower bound and complete Frobenius upper bound. Frobenius squared is the sum of `Complex.normSq` over every matrix entry. No default entrywise matrix norm or one-row surrogate is substituted. I checked the actual star-algebra equivalence to Euclidean continuous linear maps and the library's L2 operator-norm Gram identity; any proof using the latter must retain its correct norm instance.

The rational inputs are D=diag(16,1/12,1), T=[[2,1,2],[1,25,−10],[2,−10,10]], A=D² and B=DT⁸D. My independent exact reconstruction verifies T=L diag(2,49/2,150/49)L* with the specified unit lower-triangular L. Positive pivots and invertibility give a convenient exact definiteness route. All six named matrices must be proved positive definite in Lean; finite arithmetic checks are not the definiteness theorem.

The witness-data export also requires all actual CFC identities: A^(1/2)=D, A^(−1/2)=Dinv, the normalized matrix T⁸, and generalized means G=DTD and H=DT⁷D at 1/8 and 7/8. Positive-definite CFC power composition and natural-power identities can remove all fractional-power computations. The two original target products are then G²H² and A²B². None of these identifications is an assumed witness table.

My independent rational multiplication by repeated squaring agrees with the source's exact entry

(GH)[0,2] = 1260589125202/9,

and the sum of all nine squared entries of AB is

2009446159144992718181231562721/107495424.

Their exact squared difference is

99434824489435745411095588895/107495424 > 0.

The source's paper entry (1,3) correctly becomes Lean entry (0,2). The planned single explicit kernel-mode LeanCert point certificate proves the positive difference, which must be consumed by the final strict norm comparison. No numerical eigenvalues, approximate roots, interval subdivision or searches over parameter boxes are needed.

The generic norm bounds give operatorNorm(AB)² < operatorNorm(GH)². Applying the genuine squared-product eigenvalue bridge reverses the proposed first eigenvalue inequality at n=3. Since k=1 is a proper nonempty prefix there, that alone excludes the entire log-majorization relation. The admissible parameters r=s=1,p=2,t=1/8 then negate the complete original universal conjecture without extra assumptions. This is outside the narrower proven t interval described in the source and does not contradict that restricted result.

## Independent checks and remaining gates

Fresh Definitions, Challenge and explicit elaboration-inspection commands all exited zero. Definitions and inspection produced no warnings; Challenge emitted exactly eight deliberate placeholder warnings. The actual dependency Git HEADs match all ten locked revisions and have clean tracked source. The eight selected Comparator names match the eight Challenge declarations, with no replaceable definition names and only `propext`, `Classical.choice` and `Quot.sound` permitted.

The inspection log SHA256 is `19239297d5cd35d617c22f9dec7d195dfa4786bb9d1bb17ee8ba5ff55ead64cf`. Relevant actual instance checks, fresh command receipts, the complete raw elaboration, immutable source identities, library hashes and independent rational reconstruction are retained in [statement-referee-2-root-evidence](statement-referee-2-root-evidence/). Its manifest SHA256 is `6f43de615e39c282c3a562e21a98bd3949f58fec272277c74b0c82341eb07758`. These local macOS checks reused pinned dependency artifacts; they are neither Linux Comparator execution nor a fresh source build of Mathlib. The finite reconstruction establishes no CFC, norm or eigenvalue theorem.

I applied the relevant Tau Ceti faithfulness/correctness, scope, computation, reuse and attribution rubrics at `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`, within this permanent NLA target. The explicit semantic bridges and exact integer-power construction reduce numerical work while preserving the complete mathematical statement. Schiffer/Forsythe structure and actual pinned Mathlib APIs are appropriate reuse; no literature assertion may be imported as a custom axiom. This is independent AI-agent review, not official Tau Ceti endorsement or human peer review.

Mathematical counterexample credit remains Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Formalization credit is George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI assistance and without his email.

Implementation may start after both written statement approvals. Two independent final proof reviews, truthful metadata, real Linux Comparator matching, default-kernel replay and standard-three-only transitive trust remain later publication gates. No canonical promotion, commit or publication was performed by this review. A substantive statement change reopens the affected reviews.

| Frozen file | SHA256 |
| --- | --- |
| `NLA/MI23/Definitions.lean` | `1ca2386528fc7ff944f84088842f62c5f33a38f14cde7ee8127972be29696def` |
| `Challenge.lean` | `283bca1ced50d7953f9946629c24e99f944d81095f9c822fbb3b58a44e01e189` |
| `NUMERICAL_TARGETS.md` | `2f8e41d440d3e24732a1c2b70c0710ad0d88367c2aac7979141959a8d8df25ee` |
