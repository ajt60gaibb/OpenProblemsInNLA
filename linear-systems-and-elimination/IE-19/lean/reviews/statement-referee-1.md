# IE-19 independent statement referee 1

**Verdict: approve.** The reviewed definitions and three target declarations faithfully express a counterexample to the canonical IE-19 inequality and the negation of its full equality-characterized conjecture. No statement change is requested. This approval is for the statement boundary before proof implementation; it is not an approval of a Lean proof or a completed formalization.

Reviewer: independent Codex agent `/root/leancert_examples`. Date: 12 September 2026. The reviewer did not author the proposed definitions or target statements and wrote no proof code. This is agent review, not external human peer review or an official Tau Ceti service verdict.

## Exact reviewed artifacts

All paths in this table are relative to this Lean project. Approval applies only to these bytes; changing a statement or definition requires renewed review.

| File | Bytes | SHA-256 |
|---|---:|---|
| `NUMERICAL_TARGETS.md` | 3893 | `71bab6295627b5d68e63a41bfae8a5e82ce11900d334846636f85cf454814c24` |
| `Challenge.lean` | 669 | `c79e602bde37c5395eda1376635054776c72c1d803737e1dbfe0a963899627bb` |
| `NLA/IE19/Definitions.lean` | 3019 | `32dc631cd600154948963a875559cd610d974764fc77f13ab242a573c6dd22b3` |

Read the canonical `linear-systems-and-elimination/IE-19/README.md` and the complete Colbrook `references/colbrook-recovered-2026-09-11/manuscripts/IE-19.tex` directly with `git show` at upstream commit `5adea969c17391693978ada2674d25bb5c3daeb1`. Their SHA-256 values are respectively `eea3c53d86f17e4e41a9d1ebcf62454ebd1ac0c296b9305137e44a47bf283488` and `4c50113b3ca261779be36a0058e6b79cb594225098268cd8cc815e6b87b905a4`. The worktree canonical README matches the pinned bytes. Section 1 is the formalized mathematical source; Section 2's sharper infimum is outside this project's declared scope.

The implementation agent reported successful statement-only elaboration with `lake build NLA.IE19.Definitions Challenge` (2380 jobs), with only the three deliberate Challenge placeholders warned about. I independently observed the resulting Definitions and Challenge `.olean` files and re-read the final source after the import-path correction, `open scoped NNReal`, and `noncomputable section` additions. Those changes resolve notation/computability and do not alter mathematical bodies or signatures. I did not independently repeat the build or inspect a new proof.

## Correctness and definition fidelity

The review applied the semantic correctness, non-vacuity, effective-domain, and scope checks from [Tau Ceti correctness](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics/correctness.md), [Tau Ceti scope](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics/scope.md), and [Palomar definition fidelity](https://github.com/PalomarRegistry/PalomarPolicy/blob/e9c8c238f5695b10f75db7175648a1d0195352c1/prompts/03-definition-fidelity.md). Tau Ceti's own roadmap membership is not imposed on this independent NLA project.

- `comparisonMatrix` is exactly `α I + m 11ᵀ`: diagonal `α+m`, off-diagonal `m`. Every call uses argument order `(α,m)`. Although the chosen witness has both parameters equal to one, I also inspected the general formulas so this equality cannot conceal swapped parameters.
- `rowSumNorm` is the finite supremum in `ℝ≥0` of the sums of the scalar nonnegative norms, followed by coercion to `ℝ`. For a real scalar the norm is its absolute value; the coercion preserves finite sums and order. Since `Fin n` is finite and nonempty under `3 ≤ n`, this supremum is precisely `max_i ∑_j |M_ij|`. It is neither an entrywise supremum nor the default matrix/function norm. The empty-matrix value zero is unreachable in the conjecture's effective domain.
- `Admissible` uses real square matrices, equality with the transpose, positivity and entrywise upper bounds for every entry, and the sum over `Finset.univ.erase i` for each off-diagonal row sum. Diagonal dominance is weak (`≤`), as in the source. The definition adds no strict-dominance, Loewner-order, inverse-existence, or dominance-margin upper-bound premise.
- `comparisonBound` has precisely numerator `α+2m(n−1)` and denominator `α(α+mn)`. The dimension is cast to `ℝ` before subtraction. With `n ≥ 3` this agrees with the source's integer dimension expressions; there is no truncated-natural subtraction. The conditions imply `α ≥ m > 0`, so the scalar denominator cannot vanish.
- `LowerBoundConjecture` and `SharpConjecture` retain the universal dimension, both real parameters, their full allowed range, and every real admissible matrix. `SharpConjecture` asserts the lower bound and the biconditional identifying equality with `J=S`, not just one implication. Neither predicate assumes a conclusion or inserts a hidden witness property.
- Matrix inversion is the actual Mathlib nonsingular inverse, supplied by the explicitly imported `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`, not entrywise inversion or an arbitrarily chosen inverse. I inspected its `Matrix.inv`, `Matrix.inv_def`, `Matrix.nonsing_inv_apply_not_isUnit`, and `Matrix.mul_nonsing_inv` definitions/theorems at the pinned Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`.
- Mathlib sets the matrix inverse to zero if the determinant is not a unit. The `counterexample` target explicitly requires `IsUnit` of both actual determinants as conclusions to be proved, so that totalized case cannot account for the numerical violation. In the general source class, symmetry, positive off-diagonal entries, weak dominance, and `n≥3` imply positive definiteness: the quadratic form is a sum of nonnegative row-margin terms and positive multiples of `(x_i+x_j)^2`; vanishing on three different indices forces all coordinates to vanish. Thus the absence of an extra nonsingularity premise preserves the source rather than manufacturing a singular counterexample.
- `witnessInverse` and `comparisonInverse` are labeled candidate matrices. The target's norm assertions concern `witness⁻¹` and the actual `comparisonMatrix⁻¹`, so proving a norm of the candidate alone cannot satisfy the selected result. Connecting the candidates to genuine inverses remains an explicit proof obligation.

All nine definitions were inspected: `comparisonMatrix`, `rowSumNorm`, `Admissible`, `comparisonBound`, `LowerBoundConjecture`, `SharpConjecture`, `witness`, `witnessInverse`, and `comparisonInverse`. All three selected declarations were inspected: `counterexample`, `not_lowerBoundConjecture`, and `not_sharpConjecture`.

## Independent exact reconstruction

I reconstructed both matrices from Section 1 and recomputed their inverses by exact rational Gauss–Jordan elimination, using Python's `fractions.Fraction`, without importing submitted code. I computed determinants independently by the signed permutation expansion and checked every entry of each matrix–inverse product against the identity.

| Quantity | Witness `J` | Comparison `S` |
|---|---:|---:|
| Diagonal entry | `2` | `2` |
| Off-diagonal entry | `1/2` | `1` |
| Each dominance margin | `1` | `0` |
| Determinant | `27/4` | `4` |
| Inverse diagonal | `5/9` | `3/4` |
| Inverse off-diagonal | `−1/9` | `−1/4` |
| Every inverse absolute row sum | `7/9` | `5/4` |

At `n=3, α=m=1`, the parameter restriction is met at its boundary `α=(n−2)m`. Every entry of `J` is positive and bounded by the corresponding entry of `S`. The exact comparison formula is `(1+2·1·2)/(1·(1+1·3))=5/4`; its gap above `7/9` is `17/36>0`. This independently confirms every stated numerical value. The finite rational calculation checks the proposed mathematical statements; it is not a Lean proof or a universal certificate.

## Scope and disposition

An admissible strictly dominant witness is a legitimate member of the original weakly dominant class. It need not represent all members of the class to refute a universal claim. The strict failure of the inequality proves the negation of that entire universal inequality and therefore the negation of its stronger equality-characterized version. This is a complete negative answer to the original yes/no question, not a merely numerical special-case verification passed off as a positive universal theorem.

The separate sharp-infimum value `1/(α+m)` and its nonattainment are expressly excluded from this formalization's current claims. Neither the selected statements nor their numerical-target document claim that additional theorem. They preserve Colbrook's mathematical attribution and identify Stepaniants as formalization author.

No vacuous strengthened premise, field change, weakened domain, norm mismatch, inverted inequality, or assumed proof content was found. Proof implementation may begin on these frozen statements. Any later statement/definition changes, and the completed proof with its axiom closure and Comparator result, require their own current review.
