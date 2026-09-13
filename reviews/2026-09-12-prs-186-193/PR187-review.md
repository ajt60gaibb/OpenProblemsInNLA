# PR 187 / MI-03 independent mathematical and formal-target review

**Verdict: PASS for mathematical correctness, original-target fidelity, and source-level proof closure. No mathematical blocker found.** This verdict does not authenticate a Linux run; the coordinating reviewer is independently authenticating upstream execution and its binding to this exact source. No local Lean execution, new kernel replay, or human peer review is claimed here.

Reviewed head: `94e8ae24e4c10e79d8b3502101ee4a0287506f81`. Published comparison base: `5830ed4fb06da0659414a3deb2a40ad327aca052`. Canonical path remains `matrix-inequalities-and-norms/MI-03/README.md`. The whole `## Problem statement` section and `problem_ids.json` are byte-identical to that base. The proof retains Colbrook's mathematical authorship, Stepaniants's formalization attribution and Bourin–Lee's original conjecture/prior-bound credit. I read the original manuscript's reviewed theorem, upper-bound proof, root-of-unity witness, and positive-decomposition remark directly.

## Complete proof closure reviewed

Read `Definitions.lean`, `Modulus.lean`, `UpperBound.lean`, `Roots.lean`, `Witness.lean`, `Sharpness.lean`, `Proof.lean`, and `Solution.lean` in full, together with all eight declarations in `Challenge.lean`. The Solution imports Proof, which imports Sharpness and the LeanCert trust inspection module; the mathematical chain terminates in Definitions and pinned Mathlib. Challenge is not in that import chain. I also inspected the comparator configuration, Lake project, manifest and toolchain. All eight Challenge/Solution theorem statements are identical after whitespace normalization. There are no definition exceptions in the comparator configuration; only `propext`, `Classical.choice`, and `Quot.sound` are permitted axioms.

A comment-stripped lexical scan of all project mathematical modules and Solution found no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `run_tac`, custom `elab`, `macro`, or `syntax`. The eight intended Challenge placeholders are separate. This source inspection complements, but cannot replace, the authenticated transitive-axiom/default-kernel checks.

## Original statement and genuine semantic bridges

`Mat n` is the full complex `n × n` matrix type. `matrixModulus A` is `CFC.sqrt (A.conjTranspose * A)`; `operatorNorm A` is the norm of the actual continuous linear map on `EuclideanSpace ℂ (Fin n)`. `AdmissibleConstant` requires `c ≥ 0` and quantifies every natural dimension `n ≥ 1`, every tuple `Fin k → Mat n`, and only the original operator-norm contraction hypothesis. `errorGap` is the stated PSD difference. `sharpConstant` is the real `sInf` of that full admissible set, not a proposed formula. The odd conjecture quantifies every `k ≥ 3` with `Odd k`.

I independently retrieved official source files at Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`; all URLs and hashes are in `/private/tmp/nla-audit-187-192-mathlib/sources.json`. Particularly:

- `Analysis/Matrix/Order.lean` defines the scoped matrix order by PSD differences and proves `nonneg_iff_posSemidef`; `LinearAlgebra/Matrix/PosDef.lean` identifies finite PSD matrices with Hermitian matrices whose quadratic forms are nonnegative on **all** vectors.
- `Analysis/CStarAlgebra/Matrix.lean` defines `toEuclideanCLM` from the orthonormal Euclidean basis, proves that it acts by actual matrix-vector multiplication, and makes the scoped L2 matrix norm its genuine operator norm. `l2_opNorm_toEuclideanCLM` is the exact bridge used here. The CStar instance used by norm identities is that L2 instance, not the default function norm.
- `Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Abs.lean` defines absolute value as the CFC square root of `star A * A` and supplies unconditional positivity, square, and CStar norm identities. `Rpow/Basic.lean` defines the nonnegative CFC square root and proves `sqrt_unique` from a candidate's square and positivity. Thus the explicit rank-one modulus is identified with the principal PSD square root, not merely any square root.
- `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean` proves `‖a‖ ≤ 1 ↔ a ≤ 1` for positive elements, with the needed positivity proved in this project. No unproved literature bound is supplied as a premise.

## Upper bound and all-k sharpness

For `R = |Σ A_j|` and `T = Σ |A_j|`, the project proves

`k(T + (k/4)I - R) = k Σ_j (|A_j| - |A_j|²) + (1/2)Σ_iΣ_j (A_i-A_j)* (A_i-A_j) + (R-(k/2)I)²`.

I checked the expansion: the double Gram sum is `k Σ_j A_j* A_j - (Σ A_j)*(Σ A_j)`, so the terms cancel exactly using `R² = (Σ A_j)*(Σ A_j)` and `|A_j|² = A_j* A_j`. The ordered-pair factor is correct, including zero diagonal terms. Positivity of the first sum comes from `0 ≤ |A_j| ≤ I` and the commuting factors `|A_j|`, `I-|A_j|`; positivity of the second is Gram positivity; positivity of the final ordinary matrix square follows from an explicitly proved Hermitian identity. Scaling back by the positive inverse of `k` establishes admissibility for every `k ≥ 2`, dimension and complex contraction tuple, including singular/zero matrices.

The witness uses the actual symbolic primitive root `exp(2πi/k)` and vectors `(1/2, (√3/2)ω^j)`. The pinned source `RootsOfUnity/Complex.lean` proves `Complex.isPrimitiveRoot_exp` for every nonzero `k`; `PrimitiveRoots.lean` proves the geometric sum vanishes for `1 < k`. Both hypotheses follow from `k ≥ 2`; there is no finite search, phase approximation, odd-only restriction, or missing large-k case.

The witness proof establishes unit Euclidean vector norms, exact Gram matrices and idempotent PSD rank-one projectors, then uses `CFC.sqrt_unique` to derive their genuine moduli. The operator norm is proved equal to one via the reverse Gram `A_j A_j* = e₁e₁*` and the genuine CStar norm identity. Symbolic sums yield `Σ A_j = diag(k/2,0)`, `Σ |A_j| = diag(k/4,3k/4)`, and modulus difference `diag(k/4,-3k/4)`. I independently checked these formulas from the displayed outer products and vanishing root sums. The sum is PSD, so its modulus equals itself.

For any admissible `c`, the theorem specializes its **universal** dimension quantifier to two, applies the proved contractions, and reads diagonal entry zero of the PSD error gap to force `c ≥ k/4`. It then constructs an actual `IsLeast` member before applying `IsLeast.csInf_eq`; empty-set or unbounded-infimum conventions are not used. The original odd conjecture follows from the stronger all-`k ≥ 2` theorem. Unused `Odd k` in that last corollary is deliberate strength, not a weakened target.

## Scope and limits

The current English claim accurately says that the original odd-summand question is completely solved, with the stronger `k ≥ 2` conclusion and genuine CFC/operator norms. It explicitly excludes the manuscript's extra three-dimensional Hermitian extremizers and rank classification from these exports. No extra certificate, normality, commutativity between distinct summands, invertibility, or dimension restriction is hidden in the public statements.

The independent source/identity checks and SHA-256 hashes of every reviewed project input are saved in `/private/tmp/nla-187-192-source-checks.json`. Public primary-source API links are retained in the separate Mathlib source manifest. Final publication acceptance remains contingent on the coordinator's independent CI provenance, exact-input binding and kernel/axiom audit; submitted PASS prose and bundled operational receipts were not treated as self-authenticating.
