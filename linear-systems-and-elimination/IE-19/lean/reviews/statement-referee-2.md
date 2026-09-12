# Independent statement referee 2 — IE-19

**Verdict: PASS for the mathematical statement boundary and numerical obligation list at the exact hashes below.** This is independent AI-agent review, not a proof audit, human peer review, or an assertion that Lean has accepted the later implementation. The reviewer did not edit proof code or repository status.

Reviewed on 2026-09-12T14:40:11+00:00. Reviewer: Codex agent `/root/solved_statement_inventory`, assigned separately from the statement/implementation author.

Canonical source revision: `5adea969c17391693978ada2674d25bb5c3daeb1`. The original target was read from its git object rather than inferred from the current Solved label. The accompanying source manuscript, Section 1, was also read directly.

## Inputs

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `linear-systems-and-elimination/IE-19/README.md` | 4817 | `eea3c53d86f17e4e41a9d1ebcf62454ebd1ac0c296b9305137e44a47bf283488` |
| `references/colbrook-recovered-2026-09-11/manuscripts/IE-19.tex` | 5489 | `4c50113b3ca261779be36a0058e6b79cb594225098268cd8cc815e6b87b905a4` |
| `NUMERICAL_TARGETS.md` | 3893 | `71bab6295627b5d68e63a41bfae8a5e82ce11900d334846636f85cf454814c24` |
| `Challenge.lean` | 669 | `c79e602bde37c5395eda1376635054776c72c1d803737e1dbfe0a963899627bb` |
| `NLA/IE19/Definitions.lean` | 2968 | `d75e8e1b3993e535b8f6e009af3b46d6e8a7af96c278d7d29e47e2106b5a1eb5` |

## Correspondence to the original target

1. **Quantifiers and dimensions.** Both conjecture predicates quantify over every natural dimension n with 3≤n, every real α,m satisfying 0<m and (n−2)m≤α, and every real n×n matrix J. Exchanging the syntactic order of the two universally quantified scalar parameters does not alter the proposition. The cast `(n : ℝ) - 2` is the intended real arithmetic; under n≥3 it also agrees with any natural-subtraction presentation of the source range.

2. **Comparison matrix and entry order.** `comparisonMatrix α m` has entries `(if i=j then α else 0)+m`, exactly αI+m11ᵀ. `Admissible` requires transpose symmetry, strict positivity and the entrywise upper bound for all entries, then the off-diagonal row sum ≤ the diagonal. The erased finite index is exactly j≠i. There is no Loewner-order replacement, no absolute value inserted on entries, no strict-dominance restriction, and no extra invertibility assumption in the universal conjectures.

3. **Norm.** For a real scalar x, its nonnegative norm coerces to |x|. Consequently each summand in `rowSumNorm` is exactly the canonical absolute entry. The finite supremum in ℝ≥0 is a maximum of the row sums; n≥3 makes the row index set nonempty, so the bottom value for an empty supremum is irrelevant. This definition represents max_i ∑_j |M_ij|, not the default entrywise matrix norm. The implementation must prove/evaluate all three row sums and the finite maximum, as the target list requires.

4. **Inverse and denominator semantics.** The source uses the ordinary inverse; Lean's matrix inverse is totalized. The concrete export requires `IsUnit witness.det` and `IsUnit comparison.det`, in addition to norm equalities involving the actual inverse notation. Proving the explicit candidate multiplication identities and deriving actual inverse equalities, as required by numerical obligations 3–4, prevents a singular/zero-inverse artifact. The universal predicates insert no new invertibility assumptions. This negative resolution does not need a general theorem that every admissible J is nonsingular: its one witness must be nonsingular, which is explicitly exported. Under the canonical scalar assumptions α is positive, so the proposed bound has its intended nonzero denominator; at the witness it is exactly 4.

5. **Inequality and equality orientation.** `comparisonBound n α m` is precisely (α+2m(n−1))/(α(α+mn)). `LowerBoundConjecture` asserts that value ≤ the inverse norm. `SharpConjecture` conjoins the same bound with equality iff J is the comparison matrix. No inequality direction or iff direction was reversed.

6. **Witness and numerical obligations.** The three matrices reproduce Colbrook's exact Section 1 witness: J has diagonal 2/off-diagonal 1/2; its candidate inverse has diagonal 5/9/off-diagonal −1/9; the comparison inverse has diagonal 3/4/off-diagonal −1/4. At n=3, α=m=1 all scalar restrictions hold. The strict entry conditions and weak dominance hold (indeed each diagonal 2 exceeds its two off-diagonal entries' sum 1). The absolute inverse row sums are 7/9 and 5/4. The listed exact checks are sufficient and do not involve floating-point tolerances or interval coverage.

7. **Full-target negation.** From the exported admissibility and strict inequality `rowSumNorm witness⁻¹ < comparisonBound 3 1 1`, specializing `LowerBoundConjecture` at n=3, α=m=1, J=witness gives its contradictory reverse weak inequality. The same specialization contradicts the first conjunct of `SharpConjecture`. Thus proving the three Challenge declarations settles the original universal yes/no claim completely and negatively. The counterexample need not disprove a sharp infimum replacement, establish its nonattainment, or show failure at every parameter value. Those additional manuscript results are explicitly excluded from formalized scope.

## Trust and implementation handoff

`Definitions.lean` imports only the named mathlib modules and supplies definitions, not unproved local theorem assumptions. `Challenge.lean` deliberately contains placeholders for the expected declarations. This is acceptable only as an isolated statement-comparison environment: the solution must never import Challenge, and no final export may transitively depend on these `sorry` declarations. Comparator should check the actual elaborated declaration types and dependencies against this reviewed boundary.

The scalar LeanCert task is just `(7 : ℝ)/9 < 5/4` after exact matrix and finite-sum proofs. Use the explicitly requested kernel mode, and inspect the transitive axioms afterward. A successful scalar LeanCert proof alone does not prove either inverse identity, admissibility, the norm semantics, or the conjecture negations.

The only permitted final axiom dependencies are a subset of `propext`, `Classical.choice`, and `Quot.sound`. This statement review has not run `#print axioms`, compiled proof implementation, or verified Comparator output. Those are later gates. It also does not override any typechecking errors; the root agent is checking elaboration separately.

No signature changes are requested. Freeze these hashes for proof development. If definitions, Challenge declarations, or the numerical obligation list change, re-review the changed boundary before relying on this verdict.

## Import-only typecheck correction

The root agent corrected the matrix-notation import to the installed mathlib 4.33.1 path, `Mathlib.LinearAlgebra.Matrix.Notation`, replacing `Mathlib.Data.Matrix.Notation`. I reconstructed the originally reviewed file by reversing precisely that one byte-string substitution and obtained the original SHA-256 `d75e8e1b3993e535b8f6e009af3b46d6e8a7af96c278d7d29e47e2106b5a1eb5`; this confirms there were no definition, signature, or other text changes.

The corrected `NLA/IE19/Definitions.lean` is 2977 bytes with SHA-256 `2bc79751307af120def2c4f78c0fc280957555a040e87c2e117955cbadc2003b`. The PASS verdict is rebound to this corrected file. The old hash in the initial input table is retained as review history. Challenge and numerical-target hashes remain unchanged. Root typechecking is pending; no proof audit is implied.

## Final elaboration corrections and independently repeated build

The root added `open scoped NNReal` to make the intended `ℝ≥0` notation available, and `noncomputable section` for real-number definitions involving division. Removing exactly these two declarations and their separating blank line recovers the preceding reviewed hash `2bc79751307af120def2c4f78c0fc280957555a040e87c2e117955cbadc2003b`. No definition body or theorem signature changed. These are elaboration/compiler annotations, not additional mathematical assumptions.

The final reviewed and successfully elaborated `NLA/IE19/Definitions.lean` has **3019 bytes**, SHA-256 **`32dc631cd600154948963a875559cd610d974764fc77f13ab242a573c6dd22b3`**. The previous two hashes above remain as history. Challenge and numerical-target hashes are unchanged. The PASS verdict is rebound to these final bytes.

I independently reran `lake build NLA.IE19.Definitions Challenge` in the IE-19 Lean directory on 2026-09-12T14:43:56+00:00. It exited 0 and reported `Build completed successfully (2380 jobs).` Its only warnings were the three deliberate Challenge declarations using `sorry` at lines 8, 17, and 20. No solution theorem has been proved or audited by this statement-only build.
