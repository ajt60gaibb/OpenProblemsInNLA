# RA-03 independent final proof referee 2

**Verdict: approve the completed Lean proof at the hashes below. No blocking mathematical or trust finding remains.**

Reviewer: `/root/leancert_examples`, an independent AI agent. I did not author RA-03's statements or proof. I previously performed its second statement review, and have now read every line of the actual `Definitions.lean`, `Proof.lean`, and `Solution.lean`, rechecked the approved Challenge and numerical obligations, inspected the relevant pinned mathlib definitions/theorems, and independently recompiled all three project modules into a separate review output directory. This is agent review, not external human peer review or a substitute for Linux Comparator.

## Immutable review boundary

Canonical base: `e7252e5307781a7c897bca6cb124f6ab838f6809`.

| Source | SHA-256 |
| --- | --- |
| `NLA/RA03/Definitions.lean` | `de6509ef6b4a41db3e01fce7b77af4c7c338dbd61f8f135e956602d3b8b0980f` |
| `Challenge.lean` | `74a7c727e8cf2fa1ee26e78cfab812626b265abe8211e09f144a3c78fca5345e` |
| `NUMERICAL_TARGETS.md` | `91618c7848ad46931a8f59bad6ff2900bf53b1e1dde22f31383c4a3941eb4a94` |
| `NLA/RA03/Proof.lean` | `b98c702906e163805ae83809cf750eca650f365a815034a665e2ebd7bd96746a` |
| `Solution.lean` | `08e83996051e2c443a6a5153e8fb6e30ebf69bd4f44f86cddda837bbc0baf86e` |

The statement files remain byte-identical to the independently approved pre-proof boundary. I verified all five hashes before and after the fresh compilation. The complete canonical README and complete 637-line Colbrook manuscript were read in the prior statement pass and remain unchanged: SHA-256 `6432d9aad9409c52d72c8c20eb8d03fff8b84cee5383ecc37908ee5d0f5201f0` and `6ea9223d7411994923a0f27d4c9b3ae44fee8c19ca82c5f16f42b722ee589880`. Their Section 2 one-pivot counterexample is the exact source scope of this result; the later all-rank sharpness and RA-02 Cholesky results are not being claimed here.

## Independent source and trust verification

Evidence is retained under `reviews/proof-referee-2-evidence/`.

I separately compiled `NLA/RA03/Definitions.lean`, `NLA/RA03/Proof.lean`, and `Solution.lean` from their actual source into `recompiled/`. For Proof and Solution, that fresh output directory was placed first in `LEAN_PATH`, so the exports use the freshly compiled project modules. A subsequent inspection module imported that fresh Solution and checked its four public exports again. **All four final commands returned exit 0.** The first preliminary separate-output attempt needed Definitions in the same NLA package directory; after compiling all three modules into that directory the checks passed, with both preliminary and final logs retained. No mathematical source was changed.

The fresh source runs execute the original eight internal and four public `#assert_trust kernel` checks. The final inspection executes four further public checks. Every one passed; all 16 printed axiom records contain **exactly `propext`, `Classical.choice`, and `Quot.sound`**. None contains `sorryAx`, a custom axiom, or a native execution axiom. The source uses `set_option leancert.trust "kernel"` and the explicit retained tactic `leancert (trust := kernel)` at `strict_scalar_gap`.

A source scan of Definitions, Proof, and Solution found no `sorry`, `admit`, custom axiom declaration, `native_decide`, native trust selector, `unsafe`, `implemented_by`, external declaration, extra resource-limit override, or Challenge import. Solution imports only Proof; Proof imports the shared definitions, mathlib, and LeanCert. The four deliberate Challenge placeholders remain outside the solution closure.

The checked compiler is Lean 4.33.1, arm64 Apple Darwin, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The imported dependencies were checked at the exact clean pins: mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. This independent compilation reuses those pinned imported dependency artifacts; it is not a fresh Linux dependency build or Comparator execution.

Evidence hashes:

- `execution.json`: `18617883829e73975c9fe5be7bf65c039d001d9bc99a8c9c8a3cf95e42167dbc`.
- `axioms.log`: `bdf0f1b4a539cba1c194033245ad1ad02ce3728f4f839c753848ff40b1a8f9f6`.
- `review-source-manifest.json`: `43b1cdd1d31e60220dc9fefddf604aec755e3013103db44b6a1e501ed3ba74e3`.

The manifest also binds the canonical sources, inspected mathlib files, actual commands/logs, selected sources, and independent numerical reconstruction from the statement pass.

## Mathematical proof audit

**True norm and legitimate denominators (`Proof.lean:24–57`).** The generic norm bridge unfolds mathlib's explicitly scoped Frobenius norm into the square root of a sum of squared entry norms, establishes that sum is nonnegative, and uses `Complex.normSq_eq_norm_sq`. It therefore proves the actual squared Frobenius identity. Its derived zero-characterization gives `frobeniusSq A=0 ↔ A=0`, so division by the pivot normalizer is justified whenever the residual is nonzero. The normalization proof does not apply `div_self` at zero: it handles the zero matrix separately with the absorbing `none` label.

**Full finite probability law (`Proof.lean:39–99`).** Transition masses are proved nonnegative and sum to one for arbitrary rectangular complex inputs. Both history proofs induct on the number of steps while generalizing the current matrix. `Fin.consEquiv` separates the first transition from its full remaining history, so the induction hypothesis applies to the actual next residual and its recomputed conditional law. No independence of row and column choices or of successive states is assumed. The separate expected-error recurrence is proved directly from the same weighted history sum. The public `process_isProbability` therefore discharges the general probability obligations from the statement gate, rather than simply certifying the witness's four weights.

**Actual updates and expectation (`Proof.lean:103–147`).** All four witness entries are proved nonzero, and the actual `pivotResidual` branch is fixed with those facts before finite evaluation. The four residual errors and pivot masses are thus consequences of the specified update and mass functions. The one-step expectation first invokes the actual conditional-expectation recurrence, drops the proved zero-mass `none` contribution, and sums all four jointly sampled entry outcomes. It is not an unrelated table or an assumed stochastic estimate. The result is exactly `18/5`.

**Actual singular spectrum (`Proof.lean:150–204`).** The proof first establishes `T.adjoint ∘ₗ T = Matrix.toEuclideanLin witnessGram` for the actual Euclidean matrix map `T`. I inspected mathlib's `Matrix.toEuclideanLin_conjTranspose_eq_adjoint` and `toLpLin_mul_same`; these preserve the correct complex adjoint and genuine matrix multiplication. The explicit Gram multiplication is `[[5,4],[4,5]]`. Its characteristic polynomial is proved to equal `(X−9)(X−1)`, and `Matrix.charpoly_toLin` transfers that identity to the actual operator defining the singular values.

The proof then uses `LinearMap.IsSymmetric.sort_roots_charpoly_eq_eigenvalues`, whose inspected statement gives the complete actual eigenvalue list, with multiplicity, sorted in decreasing order. Nonzero polynomial factors justify the root-product formula, and the two actual roots sort to `[9,1]`. This is stronger than merely checking that 9 and 1 are possible eigenvalues. Finally, the inspected `singularValues_of_lt` definition/API takes their nonnegative real square roots at the two valid zero-based indices. It proves the actual ordered singular values are `3` and `1`; the actual `Ico 1 2` tail is therefore `1`.

**Full negative result (`Proof.lean:207–232`, `Solution.lean:17–40`).** The retained LeanCert scalar certificate proves `2 < 18/5`, after the actual expectation and singular-value tail have been identified. The final contradiction instantiates the full original proposition with `m=n=2`, the concrete complex matrix, and `k=1`, explicitly discharging all positive-dimension and rank bounds. There is no strengthened hypothesis, restricted substitute conjecture, spectral assumption, or probability-law premise in the exported negative theorem. The four Solution signatures match the approved Challenge text on inspection; actual separate-environment Comparator matching remains the infrastructure gate.

## Independent numerical and effective-domain cross-checks

My independent statement-pass `Fraction` script directly reconstructs all four cross updates and gives masses `2/5,1/10,1/10,2/5`, squared errors `9/4,9,9,9/4`, and four equal contributions `9/10`. Its total is `18/5`; independent Gram eigenvectors `(1,1)` and `(1,-1)` give eigenvalues 9 and 1. The canonical right side is `2`, leaving strict gap `8/5`. The Lean source now proves every required connection that the numerical script alone could not certify.

Zero entry updates carry zero conditional mass. The `none` transition has positive mass only at zero and remains at zero. The history definitions and induction retain these cases for every step count, including dimension-zero extension and `k=0`, without introducing them into the positive-dimensional conjecture. The independent finite history reconstruction also checked normalization and absorption through three steps; this is supplementary evidence, not the basis of the universal normalization proof.

## Standards, quality, and limits

The review applies Tau Ceti correctness/scope/proof-quality criteria and Palomar statement/definition-fidelity criteria to this NLA project. The proof is a single coherent formalization with short named lemmas, exact finite algebra, generic induction instead of history enumeration, and one small kernel numerical certificate. The two `change` steps expose the documented mathlib abbreviation `toEuclideanLin = toLpLin 2 2` to use the corresponding algebraic APIs; I checked that this changes neither the norm nor the operator. There is no accidental definitional identification being used to replace the intended mathematical object.

Colbrook's mathematical attribution and George Stepaniants's formalization credit with the Caltech Computing and Mathematical Sciences department are preserved. No George email appears in these new sources.

**Approval covers the mathematical proof, its unchanged statement boundary, and the independently observed local kernel-trust results at these hashes.** Independent referee 1, Linux Comparator, final metadata validation, and publication/status handling remain separate. No claimed all-rank sharp constant or other problem resolution should be inferred from these four exports. I made no mathematical edits, commits, pushes, or status changes during this review.

## Publication packaging addendum — APPROVE

Independently read the full current README, formalization metadata and Comparator configuration after the proof review above. These files accurately advertise the complete negative answer to the canonical randomized LU factor-`2^k` conjecture, backed by the normalized generic history law and the actual one-step witness. They explicitly exclude the manuscript’s stronger all-rank sharp-`4^r` result and Cholesky results. The four exported names match the reviewed Challenge and Solution, no definition replacement is permitted, and the allowed axioms are exactly the standard three. The original mathematical authorship is attributed to Matthew J. Colbrook; George Stepaniants is credited for formalization with his full Caltech department affiliation, without an email address. All statements about authoritative Linux Comparator remain correctly pending, and no catalog promotion is claimed. The cited manuscript title is “Sharp worst-case factors for randomly pivoted Cholesky and LU.”

This packaging approval is bound to these SHA-256 values:

- `README.md` (4145 bytes): `d9359b6df43e6b96567b159e04b61104df65ee3156454b8fd19794aeb13f7b4e`.
- `formalization.yaml` (6949 bytes): `2630d1bd3513f1a9a78886d826aad73b692cff94bdf7517d5fb12f8164b8153b`.
- `comparator.json` (358 bytes): `230d3e2d92277a192b6a845793c3c6035e1cab3b28c83c6dd44324a7ed5dc21f`.
