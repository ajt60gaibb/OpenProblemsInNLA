# MI-18 independent fidelity and scope audit

Date: 2026-10-06. Reviewer: Codex AI agent `statement_audit`, independently assigned to statement fidelity and mathematical scope. This is an AI-agent review, not external human peer review.

**Verdict: approve the correspondence and complete mathematical scope of the order-144 disproof.** The unconditional external theorem `Bapat.exists_decreasing_pair` contradicts the exact canonical MI-18 question. Promotion to `Lean verified` additionally requires the mechanical verification/evidence review specified in CONTRIBUTING; this report is not itself a local Lean rerun.

## Reviewed versions

- Canonical repository base: `412489c6c52f49653bf069ac2f85e92034cdbfa5`, including the 2026-09-17 order-four result. Canonical `matrix-inequalities-and-norms/MI-18/README.md` SHA-256: `76ab00935ba495e883ab6dcc55f2c18ac105d1b74aa418467ba35b0cdde15d28`.
- External proof: `KitaKen1/bapat-lal-q-permanent-lean` at immutable commit `4200da4fc1a132d69c23fb877795b5b72089544b`. Files were fetched from GitHub at that commit and subsequently checked against the temporary checkout at the same commit.
- Pinned Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`; fetched `Mathlib/LinearAlgebra/Matrix/PosDef.lean` and `Mathlib/LinearAlgebra/Matrix/IsDiag.lean` at that exact revision.
- Repository policy read: `CONTRIBUTING.md` SHA-256 `df81332de8240a0daa8576b5eccc8fcce7dde88204355342b3a8890b95d67db3` and `docs/lean/REVIEW.md` SHA-256 `d967ddce620d4e754e2f9c25548f30cb537f76f4ddcf8ecf2574945bcd332553`.

The final theorem declarations reviewed were `BapatLal.qPermanentMonotonicity` in `lean/Bapat/Main.lean`, `Bapat.exists_decreasing_pair`, `Bapat.exists_positive_definite_counterexample`, `Bapat.not_bapatMonotonicity`, and `Bapat.gramWitness_endpoint_negative` in `lean/Bapat/Counterexample.lean`. The source path from these declarations was followed through the definition, reality, Gram-witness, endpoint-minor, complementary-permanent, ordered-wedge, and polynomial-certificate modules. Representative SHA-256 values verified from the checkout are recorded below.

## Correspondence to the unchanged target

1. **Permutation and order.** `Equiv.Perm.inversionCount` in `Statement.lean` and `Bapat.inversions` in `Basic.lean` both count exactly the pairs `i < j` with `σ j < σ i`. Indexing by `Fin n` changes the printed labels from 1 through n to 0 through n−1 without changing their order. No row sorting or order-insensitive surrogate is substituted.
2. **Polynomial.** `Matrix.qPermanent` is the sum over every permutation of `q^inversionCount * ∏ i, A i (σ i)`. Real q is coerced to the complex field. Natural-number exponentiation gives `0^0 = 1`, agreeing with the catalog. `Bapat.qPermanent` is its real part, not a different statistic: `BapatLal.qPermanent_re` proves their equality.
3. **Complex reality.** `PermutationReality.lean` proves `inversions_symm`, `star_complexTerm`, and `complexQPermanent_eq_real`. The conjugate monomial is reindexed by the inverse permutation, which has the same inversion number. Consequently every q-permanent value of a Hermitian matrix is real, including negative q and both interval endpoints. Taking the real part loses no information relevant to the catalog inequality.
4. **Matrix assumptions.** Pinned Mathlib defines `Matrix.PosDef` to include `IsHermitian` and positivity of the quadratic form on nonzero vectors. Its proved `PosDef.posSemidef` and `PosDef.diag_pos` imply the catalog's PSD and strictly positive diagonal requirements. `Matrix.IsDiag` means every off-diagonal entry is zero; its negation is the catalog's non-diagonal condition.
5. **Dimension.** `gramFactor` has type `Matrix (Fin 144) (Fin 2) ℂ`, and `gramWitness = gramFactor * gramFactor.conjTranspose` has size 144. This satisfies n ≥ 2. `Certificate.rows_length` proves that all 144 ordered rows are present; the default value used by `List.getD` is therefore never used for a valid row.
6. **Actual violation.** `Bapat.exists_decreasing_pair` has no external premises. It asserts that some ε > 0 gives a positive-definite, non-diagonal matrix H+εI and q₁,q₂ in the closed interval [−1,1] with q₁ < q₂ and P(q₂) < P(q₁). This is a strict decrease, stronger than merely failure of strict increase. It directly disproves the universal canonical PSD assertion. No reliance on a converse equivalence between the PSD and PD formulations is necessary.

## Mathematical path and possible gaps checked

- `Witness.lean` proves H is PSD as VV*, and proves H[0,1] = 9795 − 1288i. Adding εI leaves that off-diagonal entry unchanged. The perturbation is therefore non-diagonal, and positivity of ε makes it positive definite.
- `PairMinorIdentity.lean` derives the endpoint identity by pairing each permutation with its composition with a row transposition. For a fixed i<j, the ascending-image sum minus the descending-image sum is the 2×2-minor contribution. Summing gives `2 D = binom(n,2) P₁ − Re(pairMinorSum)`. The factor 2 and the sign agree with this combinatorial derivation; `rowPairs_144_card` yields 10296 = 144·143/2.
- `RankTwoPermanent.lean` establishes the Gram permanent coefficient formula, with weight k!(n−k)!. `ComplementPermanent.lean` performs the same calculation on the n−2 complementary rows and columns, summing over all ordered row and column pairs. The resulting `pairMinorGram_norm` is the norm of the sum of wedge polynomials, not the sum of the separate squared norms; the cross terms are retained.
- `PairPolynomial.lean` shows that a pair's wedge term is T_j−T_i, so its total coefficient is 2i+1−n. This is the negative of the certificate weight n−1−2i. `pairPolynomial_gramFactor` and `WedgePolynomial.lean` therefore identify F = −g with the correct sign. The sign disappears only after taking the squared norm.
- `PolynomialCertificate.lean` connects the Gaussian-integer recurrence to the intended product and weighted polynomials. The computation of S takes only 143 coefficients, but this is not an unchecked truncation: `Certificate.coefficient_shape` in `Shape.lean` proves the discarded degree-143 coefficient is exactly zero, and `certificate_weighted_truncation` proves equality of the truncated and full polynomial.
- `Counterexample.lean` supplies the permanent and minor-norm identities unconditionally. Earlier modules have explicitly conditional reduction lemmas, but no unresolved identity premise survives in `gramWitness_endpoint_negative`, `not_bapatMonotonicity`, or `exists_decreasing_pair`.
- `Basic.lean` proves that the endpoint derivative is continuous under εI perturbations, obtains a positive ε with negative derivative, and uses the nonnegative one-sided endpoint derivative of a monotone function to contradict monotonicity. Since the q-permanent is a polynomial, differentiability is proved by termwise differentiation of a finite sum. A derivative at the right endpoint is sufficient: for q<1 sufficiently close to 1, a negative derivative gives P(q)>P(1).

No mathematical or statement-fidelity defect was found in these steps.

## Verification evidence actually inspected

I inspected the pinned public `lean/evidence/build.log` and `build_results.json`, including the dated 2026-10-05 record, successful main build, and transitive axiom output for `BapatLal.qPermanentMonotonicity`, `Bapat.exists_decreasing_pair`, and `Bapat.complexQPermanent_eq_real`. Those outputs list only `propext`, `Classical.choice`, and `Quot.sound`. This audit did not execute Lean or independently recompute the 768/772-digit integers.

`FClikelean/QPermanentMonotonicity.lean` deliberately contains `sorry` as an external-proof registration candidate. It is not the complete proof and is not imported by `lean/Bapat/Main.lean`. The complete proof imports definitions from `Bapat.Statement` and the unconditional counterexample; public axiom reports distinguish that proof from the registration stub. The presence of the registration candidate should be explained if a repository-wide text scan is reported.

## Required scope and presentation qualifications

- The proof settles the original universal complex Hermitian problem negatively. Preserve MI-18's ID, canonical path, and displayed question. The existing verified order-four result remains a valid special case and should be retained as historical/local scope; its present statement that the arbitrary-order conjecture remains open needs updating.
- The ε and the two comparison points are existential. The external project separately proves positive definiteness of 10^70 H+I, but does not formally establish the claimed decrease for that particular matrix at q = 1−10^−70. Do not promote that explicit numeric comparison to a verified claim.
- The proof does not give the least counterexample dimension or resolve a restriction to real symmetric matrices. These are limitations of what was proved, not remaining cases needed to disprove the canonical universal statement.
- A manuscript written in conventional mathematical prose may be prepared from the argument, with full source attribution and AI-assistance disclosure. Do not label an AI-authored manuscript as human-authored or as externally peer reviewed.
- An immutable link to the external source, its pinned toolchain/dependencies, the exact theorem names, and honest evidence provenance suffice for the catalog's external-proof procedure; vendoring the external repository is unnecessary.

## Selected reviewed source hashes (SHA-256)

| Path in external repository | SHA-256 |
| --- | --- |
| `lean/Bapat/Basic.lean` | `57d7250d53fa219c03c4e2ca331fef9cb865f4f1932266869df929903df54459` |
| `lean/Bapat/Statement.lean` | `8839e77178fe173b98fbcb9b7b55fac7a4ca7f6bfde53b206f9cf3b5174ce932` |
| `lean/Bapat/Main.lean` | `2b27b0b6e2f612bba072eac8f510e07f2aff933c99cce2bca44486b4e0c0cd38` |
| `lean/Bapat/Counterexample.lean` | `c94ef38633630a0ba6dd10c36f80a923ef9ecc8d57cddfd5807a028b868cfafd` |
| `lean/Bapat/PermutationReality.lean` | `01164fa991069393134fdc0576539b6f0ef353964a0a092d4c9556e2401446e3` |
| `lean/Bapat/Witness.lean` | `5c6111c3618998e002aed81340b7378fd05ccb548b82e101d8fe476268127101` |
| `lean/Bapat/PairMinorIdentity.lean` | `d70bf1fbb749c6b71466140d1aa4f82d053f549ad59cb088b2c238ec5658bef4` |
| `lean/Bapat/ComplementPermanent.lean` | `e5206b82133021070e501082bafff006e66924568957eb797472b9b8ca281fbe` |
| `lean/Bapat/PairPolynomial.lean` | `8c6571f563d0c233aa4443c5d72c3a7c4d94aa5dbb3bcecf91350655d9fd8295` |
| `lean/Bapat/Certificate.lean` | `388c39bb5d65c7ab17e81ea5a203300b49213a2f3f3ed217c1ae90efc64d2ea6` |

All conclusions and approval are specific to the versions above. Source review and successful formal compilation are complementary evidence; neither is being silently substituted for the other.
