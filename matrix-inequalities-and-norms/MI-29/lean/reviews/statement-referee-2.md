# MI-29 independent statement referee 2

**Verdict: PASS for the frozen statement boundary below.** This is the second independent AI-agent statement review, dated 12 September 2026. The reviewer did not author these definitions or statements and did not implement their proofs. This approval permits proof implementation once the other independent statement approval is present. It is not a proof review, human peer review, or completed Lean verification.

## Reviewed inputs and exact boundary

I read the complete canonical [README](../../README.md), [standalone informal proof](../../solution.tex), [submission note](../../solution.md), and all of [Definitions](../NLA/MI29/Definitions.lean), [Challenge](../Challenge.lean), and [numerical obligations](../NUMERICAL_TARGETS.md). The three canonical source files match their bytes at upstream revision `e7252e5307781a7c897bca6cb124f6ab838f6809`, independently checked using `git show`. The full informal proof is Matthew J. Colbrook's Theorem 1.1, including its hypothesis-distinction remark.

| Input | SHA-256 |
| --- | --- |
| `NLA/MI29/Definitions.lean` | `c73bfb1856b3e1059ce2ef1e35f8314cb339edcc38b89d28780d38b122ce1a16` |
| `Challenge.lean` | `7ac10b3c284dc5f86dbbb90ef999d5b210540dd0fbdc0bfc60ee9621d25da3cf` |
| `NUMERICAL_TARGETS.md` | `892449f4f9107661242eca72c50d4f35652a4475ea94573daf2ad865c44e5af2` |
| Canonical `README.md` | `8eca6404040fe727741f760e37adb89eab281bde1f5e9acba7d4ee6efb84db65` |
| Full `solution.tex` | `0c3c86150c042a4111812d95eca8dc38d53015c124e69777398ddd833dc8551f` |
| `solution.md` | `82c3ee3add53d7b1925ba6fa00efebb81989390adff9c105d4b4192bf174eceb` |

The [input record](statement-referee-2-evidence/inputs.sha256.json) also binds the package files and the author's freeze evidence. Any later change to the mathematical boundary requires renewed review.

## Original-target fidelity and nonvacuity

`ModulusDeterminantConjecture` preserves every canonical quantifier: all natural dimensions with `1 ≤ n`, all square **complex** matrices, positive definite `A`, invertible Hermitian `B`, and **real** `k,p ≥ 0`. The conclusion `rightDet ≤ leftDet` has the same orientation as the original `det(A^k + |AB|^p) ≥ det(A^k + |BA|^p)`. There is no commutation, positive-semidefiniteness of `B`, rational-input restriction, fixed dimension, supplied determinant identity, or spectral certificate among its premises.

The actual final export is `¬ ModulusDeterminantConjecture`, not the negation of an integer-exponent surrogate. The fixed witness `n=3, k=6, p=8` is sufficient to contradict the original universal assertion. All witness admissibility assertions are conclusions in `counterexample`. In particular, `A.PosDef` is stronger than semidefiniteness and includes Hermitian symmetry; `IsUnit B` is actual invertibility for matrix multiplication. The simultaneous conclusions `¬B.PosSemidef` and `¬(-B).PosSemidef` correctly record an indefinite Hermitian factor. They are not additional conjecture assumptions. The canonical positive-definite/invertible formulation is retained; this project makes no separate claim to formalize the source's singular-input discussion, the known `k=2` theorem, or a `B>0` variant.

## Semantic inspection of powers, modulus, order, and determinants

I inspected the pinned mathlib implementations, not just the wrapper names. `CFC.rpow` is the **unital** calculus `cfc (fun x : ℝ≥0 => x ^ r) A`. Its `rpow_zero` and `rpow_natCast` apply to nonnegative matrices, including exponent zero. The matrix instance of continuous functional calculus is built from the Hermitian spectral theorem and conjugation of the diagonal function values by the eigenvector unitary. It therefore has the intended spectral meaning. `CFC.abs X` is defined as `CFC.sqrt (star X * X)`, with `abs_nonneg` and `abs_sq` establishing its genuine positive-modulus properties.

The fully elaborated inspection confirms that these wrappers use `Matrix.instRing`, the matrix star instance, and `Matrix.instPartialOrder`. It also confirms that natural powers in the bridge use `Matrix.semiring`, not pointwise multiplication. Explicit `CFC.rpow` avoids the real-power instance ambiguity of a matrix represented as a function. The selected matrix order is the Loewner order `(B-A).PosSemidef`, and `0 ≤ A` is equivalent to Mathlib's actual quadratic-form `PosSemidef`. This is not entrywise nonnegativity. `Matrix.isStrictlyPositive_iff_posDef` connects the CFC positivity API to positive definiteness.

The scalar comparison uses `Complex.partialOrder`: equal imaginary parts and ordered real parts. The required **generic** export `comparison_positive_real` separately concludes that both actual determinants have imaginary part zero and real part strictly positive under the original assumptions. Thus no interpretation as merely comparing real parts of potentially nonreal determinants is being substituted. `Matrix.PosDef.det_pos` and the spectral-positivity APIs have the needed semantics; the promised future proof must actually establish the relevant matrix positivity before using them. The wrapper determinants themselves are the ordinary matrix `.det` of the displayed sums.

The primary definitions inspected are pinned at mathlib `0df444a360eaa60ab8c11dca51a86af692955474`: [matrix order](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Matrix/Order.lean), [Hermitian functional calculus](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean), [real powers](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean), [modulus](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Abs.lean), [complex order](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Complex/Order.lean), and both linear-algebra and analysis positive-definiteness files. Their independently checked source hashes are in [dependencies.json](statement-referee-2-evidence/dependencies.json).

## Five selected exports

| Export in `NLA.MI29` | Required meaning and review |
| --- | --- |
| `spectralPower_natCast` | Generic agreement with actual ring powers for every PSD matrix and natural exponent, including zero. Correct and not assumed by the conjecture. |
| `modulus_power_eight` | For every complex square `X`, proves the actual modulus definition, PSD property, and `spectralPower |X| 8 = (XᴴX)^4`. The analytic bridge is a conclusion. |
| `comparison_positive_real` | Generic reality and strict positivity of the two original determinants, with exactly the canonical hypotheses. |
| `counterexample` | Proves admissibility, indefiniteness, natural-power reductions, the two actual determinant values, their difference, and strict reversal. No certificate is supplied as a premise. |
| `not_modulusDeterminantConjecture` | Negates the full original all-dimension, all-real-exponent target. |

The product positions are correct: `|AB|² = BA²B` and `|BA|² = AB²A` for the actual Hermitian matrices. The statement does not swap those Gram matrices or replace the determinants with named rational constants by definition.

## Independent exact numerical precheck

I wrote a separate [Fraction checker](statement-referee-2-evidence/rational_precheck.py), without reusing the author's computation, using explicit matrix multiplication, repeated natural powers, a six-permutation determinant, and polynomial convolution. Its [raw result](statement-referee-2-evidence/rational-precheck.json) confirms:

- `A = diag(2,1,1/2)` has positive diagonal entries. The displayed `B` is symmetric with `det B = -1/125`. Its diagonal entries `-1/5` and `1/5` give the two required failures of semidefiniteness.
- The exact left determinant is `136990346414301954149 / 61035156250000000000`.
- The exact right determinant is `4537743716162890657 / 1907348632812500000`.
- Right minus left is `21036678407451 / 156250000000000 > 0`.
- The optional source polynomial has coefficients `[0, 2089017/16, -31188746592549/1024, 0]`. Evaluation at `z=1/390625` gives that same gap, and the two fourth-power matrices have equal determinant `1`.

This check approves the exact numerical statements; it is not a Lean certificate and does not prove the CFC reductions. The minimization plan is appropriate: reuse existing CFC/matrix theorems, compute just the exact rational witness, and use LeanCert **kernel mode** for one positive rational scalar. No interval subdivision, numerical eigenvalue calculation, or approximate square root is required. The optional polynomial identity need not be formalized redundantly if direct point certificates are smaller.

## Independent executable checks and trust scope

On macOS arm64 with Lean `4.33.1`, I separately ran:

```text
lake build NLA.MI29.Definitions Challenge
lake env lean NLA/MI29/Definitions.lean
lake env lean Challenge.lean
lake env lean reviews/statement-referee-2-evidence/Inspect.lean
python3 reviews/statement-referee-2-evidence/rational_precheck.py
```

All exited zero. The build covered a 2710-job graph using existing dependency artifacts; the separate source commands re-elaborated both current statement files. Definitions produced no warnings. Challenge produced exactly its five intentional `sorry` warnings. The [command record](statement-referee-2-evidence/checks.json), [build log](statement-referee-2-evidence/build.log), [Definitions re-elaboration log](statement-referee-2-evidence/definitions-elaboration.log), [Challenge re-elaboration log](statement-referee-2-evidence/challenge-elaboration.log), and [full elaborated inspection](statement-referee-2-evidence/inspection.log) retain the evidence. This is not a fresh dependency rebuild or Linux Comparator run.

All ten dependency source revisions independently match `lake-manifest.json`, with no tracked source modifications. `#print axioms` on `spectralPower`, `matrixModulus`, and `ModulusDeterminantConjecture` reports only `propext`, `Classical.choice`, and `Quot.sound`. The five Challenge placeholders intentionally are not completed proofs or axiom-clean theorem certificates. Definitions has no local theorem assertion, custom axiom, proof placeholder, or Solution import. No proof implementation was present for this review.

## Scoped referee assessment and remaining gates

The applicable Tau Ceti review angles pass at the statement stage: faithful original quantifiers, nonvacuous admissibility, no hidden certificate premise, actual imported mathematical meanings, correct order and exponent semantics, exact numerical reconstruction, reusable APIs, and restrained computational scope. The boundary documents correctly preserve Colbrook's mathematical attribution and George Stepaniants's formalization attribution and Caltech Computing and Mathematical Sciences affiliation; they add no email or human-review claim. The reviewed schema/configuration and proof identity gates are future work for this project.

There are **no blocking statement findings**. Proof implementation, completed-export `#assert_trust kernel` and transitive axiom checks, two independent final proof reviews, actual fresh Linux Comparator replay with the standard-three whitelist and no definition holes, and accurate publication metadata remain required. This approval alone does not justify changing the catalog from `Solved` to `Lean verified`.
