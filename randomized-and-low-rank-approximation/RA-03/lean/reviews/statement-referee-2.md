# RA-03 independent statement referee 2

**Verdict: approve the frozen statements for proof implementation.**

Reviewer: `/root/leancert_examples`, an independent AI agent that did not write the RA-03 definitions, numerical draft, or Challenge. This is a pre-proof semantic review, not an external human review, a proof certificate, or a successful Comparator result. No RA-03 proof was written in this review.

## Frozen statement boundary

Canonical base: `e7252e5307781a7c897bca6cb124f6ab838f6809`.

| File | SHA-256 |
| --- | --- |
| `NLA/RA03/Definitions.lean` | `de6509ef6b4a41db3e01fce7b77af4c7c338dbd61f8f135e956602d3b8b0980f` |
| `Challenge.lean` | `74a7c727e8cf2fa1ee26e78cfab812626b265abe8211e09f144a3c78fca5345e` |
| `NUMERICAL_TARGETS.md` | `91618c7848ad46931a8f59bad6ff2900bf53b1e1dde22f31383c4a3941eb4a94` |

I independently hashed these bytes and the canonical sources against `reviews/statement-freeze.json` after completing the checks. Any change to a mathematical definition or selected statement requires renewed review before implementation continues; even nonmathematical edits require updated evidence binding.

The full canonical `randomized-and-low-rank-approximation/RA-03/README.md` has SHA-256 `6432d9aad9409c52d72c8c20eb8d03fff8b84cee5383ecc37908ee5d0f5201f0`. I read the complete 637-line Colbrook source `references/colbrook-random-pivoting-2026-09-11/manuscripts/sharp_random_pivoting.tex`, SHA-256 `6ea9223d7411994923a0f27d4c9b3ae44fee8c19ca82c5f16f42b722ee589880`, and identified Section 2 as the counterexample being formalized. The later all-rank sharpness, correlation-matrix result, and RA-02 Cholesky results are outside these selected claims.

## Standards and independent elaboration

I applied the semantic faithfulness, nonvacuity, edge-case, and coherent-scope checks from [Tau Ceti correctness](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics/correctness.md) and [scope](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics/scope.md), adapted to the user's NLA project rather than Tau Ceti's separate roadmap. I also applied the statement-alignment and effective-domain checks in [Palomar's statement review](https://github.com/PalomarRegistry/PalomarPolicy/blob/e9c8c238f5695b10f75db7175648a1d0195352c1/prompts/02-statement-alignment.md) and [definition review](https://github.com/PalomarRegistry/PalomarPolicy/blob/e9c8c238f5695b10f75db7175648a1d0195352c1/prompts/03-definition-fidelity.md). This is a scoped manual agent review, not a claim that either service's review pipeline has run.

I ran `lake build NLA.RA03.Definitions Challenge` independently: **exit 0, 2723 jobs**, with the four intentional Challenge placeholders at lines 11, 15, 22, 33. I also ran a separate Lean inspection module: **exit 0**. It prints the elaborated norm statement with all instances visible and confirms `Matrix.frobeniusNormedAddCommGroup`, not a default coordinatewise or operator norm. The toolchain reports Lean 4.33.1, arm64 Apple Darwin, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

Raw commands, return codes, exact numerical reconstruction, and elaborated declarations are retained in `reviews/statement-referee-2-evidence/`. The inspection module imports Challenge only to inspect its declarations; it is review evidence and must not be imported by the final solution. Its displayed `sorryAx` belongs to the deliberate Challenge placeholders, whose proofs are not certified at this gate. Definitions imports only pinned mathlib modules and has no local theorem, solution, axiom, or placeholder.

## Alignment and definition fidelity

The original RPLU rank-one update, joint entry-squared sampling law, and proposed replacement of `4^k` by `2^k` were independently checked in [Gilles–Wilber, version 1](https://arxiv.org/html/2601.22344v1), equations (1), (3), Algorithm 1, Theorem 3, and the following conjecture. The canonical README fixes the requested all-positive-dimension, all-admissible-rank formulation and zero-residual convention. The following findings come from direct inspection of the local Lean definitions and that complete target.

- **Original quantifiers preserved:** `Definitions.lean:82–85` quantifies over all positive `m,n`, every `Matrix (Fin m) (Fin n) ℂ`, and every `k` with `1 ≤ k ≤ min m n`. There is no real-only, square, Hermitian, positive-definite, nonsingular, nonzero-entry, or spectral-separation premise. The factor is literally `(2 : ℝ)^k` and both sides concern squared error. The final selected declaration negates this full universal proposition.
- **Correct LU algorithm:** `pivotMass` at lines 32–34 samples one jointly indexed entry with squared complex modulus divided by the whole squared Frobenius norm. It does not separately normalize a row or a column and does not restrict to diagonal pivots. `pivotResidual` at lines 38–41 uses the full cross product `S[a,j] S[i,b] / S[i,j]`, with no inappropriate conjugation or Cholesky replacement.
- **Correct effective domain:** For nonzero `S`, the finite sum of nonnegative squared complex moduli is strictly positive, so the probability denominator is nonzero. A selected zero entry has probability zero; its identity update is a harmless totalization. For `none` at a nonzero state, the probability is zero, so its artificial zero output cannot affect expectations. At a zero state, `none` has probability one and leaves the matrix zero; all entry labels have mass zero and their totalized updates also leave zero. Degenerate zero-dimensional matrices are automatically zero and still have the normalized `none` law, while the conjecture only covers positive dimensions.
- **Correct histories and expectation:** `historyResidual` consumes `h 0` before its tail and updates the actual current residual. `historyMass` recomputes the next conditional probabilities from that updated residual, then multiplies them. It therefore describes the appropriate finite sequential law, without assuming independence of successive pivots. Any invalid zero-probability label gives the complete history mass zero. At fixed finite `m,n,k`, the history set is finite, every terminal error is a finite real number, and a nonnegative normalized mass function makes the weighted sum in `expectedError` precisely a standard finite expectation. No measure-theoretic integration theorem is necessary to give that sum its mathematical meaning.
- **Generic probability obligations are sufficient and remain obligations:** `Challenge.lean:15–19` requires nonnegativity and total mass one for every pivot and every full history, with arbitrary dimensions, input, and step count. These properties are not hypotheses of the conjecture or witness theorem. Their proof must establish the stated probability interpretation generally. The definitions fix every conditional transition, so normalization is not being imposed on an unrelated or arbitrary law.
- **True Frobenius norm:** `frobeniusSq` is the sum of `Complex.normSq`, which is squared complex modulus. The generic bridge at `Challenge.lean:11–12` uses the explicit Frobenius scope; elaborated inspection confirms the intended instance. The definition contains no default matrix norm ambiguity.
- **Actual singular values and correct indexing:** `singularValue` calls `LinearMap.singularValues` on `Matrix.toEuclideanLin A`, whose definition is the usual matrix action between complex Euclidean spaces. I inspected pinned mathlib `SingularValues.lean` and `PiL2.lean`: the sequence is decreasing, nonnegative, multiplicity-preserving, derived from the adjoint-composition spectrum, and zero-indexed. The finite range `Ico k (min m n)` therefore represents the full canonical tail. No supplied eigenvalue list, Gram spectrum assumption, or claimed best approximation substitutes for actual singular values.
- **Scope and attribution:** A single `2 × 2`, one-pivot counterexample suffices to refute the original universal bound. The larger manuscript's sharper asymptotic theorems are accurately excluded. Colbrook retains credit for the informal counterexample; George Stepaniants is credited for the formalization, with his Caltech department and no email address.

## Independent exact reconstruction

I wrote a fresh Python `Fraction` calculation that directly applies each rank-one update; it does not consume the supplied tables or the manuscript's determinant/history cancellation formulas. It independently returns the following four positive-mass outcomes for `A=[[2,1],[1,2]]`.

| Pivot | Mass | Residual | Squared error | Weighted contribution |
| --- | --- | --- | --- | --- |
| `(0,0)` | `2/5` | `[[0,0],[0,3/2]]` | `9/4` | `9/10` |
| `(0,1)` | `1/10` | `[[0,0],[-3,0]]` | `9` | `9/10` |
| `(1,0)` | `1/10` | `[[0,-3],[0,0]]` | `9` | `9/10` |
| `(1,1)` | `2/5` | `[[3/2,0],[0,0]]` | `9/4` | `9/10` |

The `none` outcome has mass zero. Total mass is one and total error is `18/5`. The independently multiplied Gram matrix is `[[5,4],[4,5]]`; its eigenvectors `(1,1)` and `(1,-1)` have eigenvalues `9` and `1` and span the two-dimensional space. The ordered nonnegative singular values are therefore `3` and `1`, giving tail `1`, proposed bound `2`, and strict gap `8/5`.

As an additional finite semantic check, direct enumeration of all histories of lengths 0, 1, 2, and 3 gives total mass one at each length and expected squared errors `10`, `18/5`, `0`, `0`. This exercises absorption and the zero-probability paths; it is not a substitute for the general probability proof or the Lean spectral proof.

## Selected declaration decisions

All four selected exports are approved as statements:

1. `NLA.RA03.frobeniusSq_eq_norm_sq`: genuine generic norm bridge.
2. `NLA.RA03.process_isProbability`: genuine generic probability normalization and positivity obligations.
3. `NLA.RA03.counterexample`: exact actual matrix, actual singular values, actual pivot masses/residual errors, actual history expectation, and strict reverse inequality; none is assumed.
4. `NLA.RA03.not_squaredErrorConjecture`: full original universal negation, with no strengthened admissibility premise.

**No blocking semantic finding remains.** This approval permits implementation only after the other independent statement approval is also present. The completed proof must still pass kernel-trust checks for its entire selected closure, independent final proof review, Linux Comparator, and the project's metadata/reproducibility checks. The current statement build establishes elaboration, not any of those later claims.
