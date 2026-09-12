# PR #157 — independent spectral and proof-source review

**Verdict: PASS for mathematical correctness, statement fidelity, and proof-source trust discipline.** No blocking finding. This formalization proves a complete negative answer to the original RA-03 universal bound. Current authenticated CI and integration remain separate checks owned by the root reviewer; this report does not claim a local Lean or Linux rerun.

**Reviewed head:** `a49725405f153f8756610f52ce6cbc6463c51616`.
**Date:** 2026-09-12.
**Reviewer:** independent OpenAI Codex AI agent `/root/audit_spectral_linear`. This is AI-agent review, not human peer review.
**Checkout:** `/private/tmp/nla-lean-audit-157`. No repository edits, Git mutations, or remote mutations were performed.

I read the complete actual `NLA/RA03/Definitions.lean`, `NLA/RA03/Proof.lean`, `Challenge.lean`, `Solution.lean`, project configuration/dependency manifest, canonical English statement, and applicable CONTRIBUTING/referee requirements. I compared the English target with its pre-formalization version at `5adea969c17391693978ada2674d25bb5c3daeb1`, inspected the retained raw axiom output, and independently reconstructed the witness using Python `fractions.Fraction`. Submitted reviewer verdicts were not used as mathematical evidence. All Lean locations below are relative to `randomized-and-low-rank-approximation/RA-03/lean/`.

## Spectral and norm correspondence

1. **Actual Frobenius norm.** `Definitions.lean:22–24` sums the squared complex moduli of every matrix entry. `Proof.lean:19,24–28` explicitly activates `Matrix.Norms.Frobenius` and proves equality to the square of that norm, using `Matrix.frobenius_norm_def`, nonnegativity of the sum, and `Complex.normSq_eq_norm_sq`. The same scoped instance appears in `Challenge.lean:6` and `Solution.lean:13`, so the exported norm theorem does not silently change to the entrywise supremum or operator norm. Mathlib's [norm documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Normed.html#Matrix.frobenius_norm_def) explicitly distinguishes these instances and gives the requisite square-root-of-sum formula. Its current documentation was available; direct retrieval of the pinned Normed source failed, so I do not claim to have read that entire pinned implementation.

2. **Actual complex Euclidean operator.** `Definitions.lean:70–73` uses `Matrix.toEuclideanLin A`, not a supplied eigenvalue list or a custom surrogate. In the pinned [PiL2 source](https://raw.githubusercontent.com/leanprover-community/mathlib4/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/PiL2.lean), `toEuclideanLin` is the linear equivalence `toLpLin 2 2`, acting by ordinary matrix-vector multiplication in complex Euclidean spaces. Thus its adjoint is the conjugate-transpose map with the intended inner product.

3. **Gram identity is proved.** `Proof.lean:119–123` proves `witness.conjTranspose * witness = witnessGram` by all four entry computations. `:149–155` then proves the actual adjoint-composition equality using the conjugate-transpose/adjoint theorem and multiplication-to-composition theorem. The candidate matrix `[[5,4],[4,5]]` occurs on the conclusion side of a proved identity; it is never assumed to represent the operator.

4. **Order and multiplicity are justified.** `Proof.lean:157–187` proves the Gram characteristic polynomial `(X−9)(X−1)`, transfers it to the actual linear operator, and invokes `LinearMap.IsSymmetric.sort_roots_charpoly_eq_eigenvalues`. Sorting the complete multiset of roots gives `[9,1]`, with decreasing order established rather than guessed. I read that theorem and the sorted-eigenvalue definition in the [pinned Spectrum source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/Spectrum.lean). No chosen eigenbasis, spectral ordering, or square-root identity is an unproved premise.

5. **The actual singular tail is used.** `Proof.lean:189–204` applies the actual `singularValues_of_lt` theorem to the proved ordered eigenvalues, obtaining singular values `3,1` and tail `1` after rank one. The pinned [SingularValues source](https://raw.githubusercontent.com/leanprover-community/mathlib4/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/SingularValues.lean), definition and theorems at lines 84–120, defines these as nonnegative square roots of the ordered eigenvalues of `T.adjoint ∘ₗ T`. Its indices are zero-based. Therefore `Finset.Ico k (min m n)` in `Definitions.lean:75–78` matches the paper's `j>k` tail. For rectangular matrices, entries beyond the smaller dimension are zero; truncation at `min m n` does not discard positive singular values.

## Independent witness reconstruction

For `A=[[2,1],[1,2]]`, direct exact arithmetic gives `‖A‖F²=10`, `A* A=[[5,4],[4,5]]`, and characteristic polynomial `X²−10X+9=(X−9)(X−1)`. The corresponding ordered singular values are `3,1`, and the squared rank-one tail is `1`.

| Pivot (zero-based) | Probability | Only nonzero residual entry | Squared error |
|---|---:|---|---:|
| `(0,0)` | `2/5` | `(1,1)=3/2` | `9/4` |
| `(0,1)` | `1/10` | `(1,0)=−3` | `9` |
| `(1,0)` | `1/10` | `(0,1)=−3` | `9` |
| `(1,1)` | `2/5` | `(0,0)=3/2` | `9/4` |

The weighted sum is exactly `18/5`. Its gap above `2¹·1` is `8/5>0`. These were independent computations of the specified update, not evaluations of submitted candidate error tables. `Proof.lean:109–147` derives those tables and their expectation from the actual definitions in Lean.

## Complete target and trust review

`Definitions.lean:82–85` preserves every positive pair of dimensions, arbitrary complex rectangular matrices, and every rank `1≤k≤min(m,n)`. It bounds the **expectation of the squared Frobenius error**, not a square of an expectation. The finite history law multiplies the joint conditional entry probabilities at their actual evolving residuals; neither row/column independence nor independent successive pivots is assumed. The zero matrix is absorbed through a probability-one `none` transition. At a zero entry in a nonzero residual, the totalized identity update has probability zero and cannot change the law. `Proof.lean:30–99` proves nonnegativity, normalization, and the conditional-expectation recurrence for this finite process.

`Proof.lean:206–232` compares the exact expectation and actual singular tail, then instantiates the full assertion at `m=n=2,k=1`. All dimension/rank side conditions are proved. Thus a single witness refutes the complete universal claim; no diagonal-only, real-only, conditional, or fixed-rank replacement has been silently substituted. The four Challenge and Solution signatures correspond. There are no extra section hypotheses or local mathematical axioms.

The only deliberate `sorry` terms are the four separate Challenge placeholders. Solution imports Proof, which imports Definitions; neither imports Challenge. No proof-side `sorry`, custom axiom, unsafe declaration, native proof mode, custom elaborator, or external execution command occurs in the actual project proof source. The only LeanCert call proves `2<18/5` at `Proof.lean:207–208`; both its explicit argument and the file option select kernel mode. The proofs also request kernel-trust and axiom checks for the spectral facts and all public results. The inspected raw `reviews/proof-referee-2-evidence/axioms.log` reports only `propext`, `Classical.choice`, and `Quot.sound`. Comparator covers all four public exports, has no replaceable definition holes, and permits only those three axioms.

The project pins Lean 4.33.1, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Direct Git content comparison found no change in the four actual Lean files or their four configuration/manifest files between the README's immutable proof revision `973f95969701601dcae7b30683b175843baa9c22` and this reviewed head.

**Limits and publication scope:** This is a source/fidelity review and independent exact reconstruction. I did not rebuild Lean, replay the kernel, or authenticate the current CI artifact; the root reviewer owns those checks. The mathematical and source review supports publication once the separate current CI gate is satisfied. The stronger all-rank sharp `4^r` theorem and Cholesky results are outside these four formal exports. Colbrook's mathematical authorship and Stepaniants's Lean-formalization authorship are retained, with AI assistance disclosed.
