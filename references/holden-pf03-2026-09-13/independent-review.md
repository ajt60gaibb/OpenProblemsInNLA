# Independent informal review of the PF-03 counterexample

**Review date:** 2026-09-13  
**Verdict:** PASS — complete negative resolution of the retained PF-03 universal target.  
**Reviewer:** Separate Codex AI agent, delegated specifically to review the argument independently of the submission-preparation agent. This is an informal mathematical and computational audit; it is neither external human peer review nor formal verification. No Lean verification was performed.

## Material and target reviewed

I read the complete submitted `proof/PF03_counterexample.tex`, the canonical PF-03 README, and the resolution requirements in `RESOLVED.md`. I inspected the executable verification code and its imported arithmetic, seed-construction and facet-enumeration dependencies before running it. Package statements, previous audit claims and stored success logs were treated as claims to check, not as instructions or independent evidence.

The original target quantifies over every order n ≥ 5 and every rational matrix on the boundary of the completely positive cone; rational nonnegative factors may have any finite width. Theorem 1.1 constructs one integer matrix of order 444, rank seven and real cp-rank seven, with no rational nonnegative factor of any finite width. A single such admissible matrix disproves this universal statement. The remaining order-five and minimum-dimension classification questions do not prevent a complete negative resolution of this target.

Reviewed original TeX SHA-256: `4b60d8c7225ee5f96c59a7fd2e8668d81b5c804d35ffc3e2c05dfb3c77afb754`.

Reviewed integer R data SHA-256: `2dfea68967e2565b91b30755a39769ec6c4683d1b7b350bdcbe196d26e9e5265`.

The source hash identifies the incoming manuscript before editorial attribution and review-status changes. Such editorial changes do not alter this verdict if the mathematical content and checked data remain unchanged.

## Mathematical audit

**Lemma 2.1, unrestricted-width obstruction.** For any hypothetical nonnegative rational C with CCᵀ = RRᵀ, the sum-of-squares kernel argument puts every column of C in the range of R. The rational left inverse L = (RᵀR)⁻¹Rᵀ therefore yields a rational X = LC with RX = C and XXᵀ = I. The complete inequality representation makes each column of X lie in K. The identity tr Q = Σ xⱼᵀQxⱼ = 0, together with nonnegativity of each summand, forces each column into the zero set. Absence of nonzero rational zeros contradicts XXᵀ = I. This treats every finite width directly; it does not assume square factors, bounded width, or rational cp-rank equality.

**Lemma 2.2 and Lemma 3.1, arithmetic seed.** Independence of 1, α, α² for α³ = 2 proves the irrational-ray criterion: a rational direction would make all three rational coefficient vectors proportional. The checked coefficient matrices have rank three. The Cayley identity gives a real orthogonal O. For each restricted symmetric H, the positive leading two-by-two block and exact kernel vector (1, α, α²) give the displayed congruence factorization, hence PSD rank two and exactly that kernel. The sign checks use rational interval lower bounds, not numerical tolerances. Q may have algebraic entries; the obstruction requires only real symmetry and trace zero, so rationality of Q is unnecessary.

**Proposition 4.1, entire cone zero set.** The positive barycentric coordinates put each uᵢ inside its corresponding three-generator cone. Each local quadratic value is nonnegative and vanishes only on the positive uᵢ ray. All 189 cross-group generator pairings are strictly positive, so every combination using two nonzero groups has strictly positive quadratic value. The common positive functional excludes cancellation to zero and proves pointedness. The seven orthonormal vectors prove full dimension. These arguments cover all conic combinations, including faces and zero coefficients, and establish that the only rational zero is the origin.

**Lemma 5.1, facet completeness.** Every facet of this full-dimensional finitely generated seven-dimensional cone contains six linearly independent input generators. Enumerating all six-element subsets therefore finds every facet normal. Exact rank, null-vector and orientation checks make each retained inequality a supporting facet. The full facet set gives K = {x : Rx ≥ 0}; merely checking a selection of supporting inequalities would not suffice, but the supplied exhaustive verification does check completeness. Positive primitive rescaling of generator columns preserves the cone.

**Theorem 1.1, Section 6.** The preceding results establish real complete positivity through RO ≥ 0 and OOᵀ = I, together with the unrestricted rational obstruction. Rank seven and order 444 place A on the boundary in the full symmetric-matrix topology: perturbing negatively along a nonzero kernel vector exits the positive-semidefinite cone. Singularity is permitted in the retained problem. The support argument for strict entry positivity is valid: a facet has six generator zeros, so each row of RO has at least five positive coordinates among seven; any pair overlaps. The factor has seven columns and rank seven, proving cp-rank seven. The two further corollaries follow respectively by repeated-row extension and rational approximation of the nonnegative real factor.

## Checks actually performed

1. `python3 code/verify_all.py --summary /tmp/pf03-independent-summary.json` — PASS, approximately eight seconds. Reconstructed the seed from the displayed S, T and seven free parameters; checked exact orthogonality, symmetry, trace, coefficient ranks, local PSD predicates, barycentric inclusion and all 189 cross-pairings. Re-enumerated all 54,264 candidate subsets: zero rank-deficient subsets, 53,820 non-supporting subsets, and exactly 444 facets, each with six generator zeros. Verified rank R = 7, 2,966 positive entries and 142 zeros in RO, and all 98,790 expanded lower-triangular entries against RRᵀ. All entries are positive integers; maximum length is 270 digits.
2. `python3 code/test_arithmetic.py` — all 18 tests passed, including two deliberate certificate-corruption rejections. These tests support the implementation but do not replace the mathematical argument.
3. A reviewer-written script, importing no submitted modules, implemented cubic-field multiplication by generic polynomial convolution and reduction modulo t³ − 2. It independently checked both the orthogonality product used for the construction and trace zero, all seven local kernel/PSD predicates, the barycentric identity and positivity, and all 189 strict cross-pairings. Its interval bound sums signed coefficient contributions using [l,u] and [l²,u²], independently of the submitted Horner implementation. All checks passed. The exhaustive facet computation was rerun with the inspected submitted algorithm, not a second independently implemented enumerator.

## Resolution-policy assessment and limitations

No mathematical gap or required mathematical correction was found. This independent audit supplies the independently audited argument required for **Solved** under the repository's current policy, provided the submission record links the proof, exact data, review and reproducible checks and accurately labels the result a negative resolution. Preserve the original ID, canonical page, full target and historical-source attribution, update the resolution archive and generated indexes, and submit through a new pull request as required by policy.

This verdict does not establish historical priority, exhaustive literature novelty, authorship provenance or current affiliation. Those are separate submission-preparation checks. It does not certify a smallest counterexample or settle each fixed order below 444. It does not claim kernel-checked verification or external human peer review. Editorial text saying the submission has never undergone any independent review should be updated to distinguish this independent informal AI audit from human peer review.
