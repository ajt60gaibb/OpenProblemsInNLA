# IE-14 independent preliminary scope/API review

**Disposition: no draft-boundary change requested. This is not final exact-byte statement approval.** The contributor dossier and final ten-file seal are still pending. No proof implementation has been reviewed or written.

Reviewer: OpenAI GPT-6 Codex `/root/reference_api_review`, independent non-implementing AI. Date: 2026-09-15. Read the full canonical README, complete `references/colbrook-recovered-2026-09-11/manuscripts/IE-14.tex` including historical qualifications, original independent review, all draft Definitions and seven Challenge signatures, and relevant pinned Mathlib APIs.

## Scope and semantics

The draft retains every original dimension n≥4, nonsingular complex matrices with exactly the permitted cyclic tridiagonal sparsity and both actual nonzero cyclic corners, fixed original column ordering, all maximum-modulus pivot ties, and growth over every entry of every active matrix. The natural inequalities in `CyclicPosition` are exactly the zero-based tridiagonal band. For n≥4 the universally quantified corner condition is not vacuous: first and last `Fin n` indices exist and are distinct.

`trajectory A path 0 = A` prevents a preliminary permutation. `rowSwap` uses the actual current row transposition. Admissibility requires the chosen row at or below the current pivot row, nonzero pivot, and maximal modulus against every active row. `schurStep` gives the literal complex trailing Schur update; zeros outside that block are padding only. Growth includes stages 0 through n−1, so the input and final scalar both count. It excludes the all-zero padded stage after the final elimination, as required. Finite NNReal suprema and coercion to real are actual entrywise magnitude maxima; no operator matrix norm is substituted.

`all_active_entries_bound` quantifies every admissible path and every active i,j at each k. `witness_data` and `witness_attainment` require the actual displayed rational construction to be nonsingular, satisfy both corners, normalize maximum modulus to one, follow literal legal swaps and attain the bound. `IsGreatest (cyclicGrowthSet n)` provides nonemptiness, attainment and the universal bound, while the explicit `sSup` equality fixes the original extremum. A union over A and its allowed paths has the same supremum as the original nested suprema; existence of paths for every nonsingular A is separately exported.

The witness's `factorIndex` is the inverse of factor-row labels (1,n,2,…,n−1). This defines the original input matrix. `witnessPath` keeps the first row and then selects the **current** last row. Tracking actual swaps gives precisely that original-label sequence, with no prior row/column permutation.

The numerical conjunction 0<1/2 and 1/2≤1 is exact. Future proofs must consume its two components in the half pivot's nonvanishing and input-entry bound, respectively, with explicit LeanCert kernel trust. No numerical certificate or completed proof is claimed at this stage.

## Source mathematics and implementation obligations

The source's two-old-row/fresh-row argument uses only triangle inequalities and multiplier modulus ≤1. Its zero-fresh update (a,b)↦(a+b,a) gives the Fibonacci envelopes. Last-column, next-to-last-column and ordinary-column histories are separate and cover every active stage, including the smallest order n=4; this separation must survive implementation. In the source, a “zero-valued pivot” in the front estimate means zero in the **target** column, not a forbidden zero elimination pivot.

The factor construction has lower unit triangular L, nonzero upper diagonal (including 1/2 and the final Fibonacci bound), normalized cyclic input, and both corners ±1. Every desired pivot is tied for a maximum because its active pivot column is L's relevant column times the corresponding nonzero diagonal of U. Exact original-label tracking is essential for all-tie upper bounds and witness legality.

After stage zero the full padded `trajectory` has zero rows/columns and determinant zero. Therefore the admissible-path existence proof must maintain nonsingularity of the **actual active submatrix**, or an equivalent row-operation invariant, rather than mistakenly using nonsingularity of the full padded matrix. n=0 in the general path-existence helper has an empty path and det(empty)=1; this harmless stronger helper does not change the n≥4 canonical domain. Empty finite maxima and zero-denominator totalization must not be used in place of proving entryMax positive for actual cyclic inputs.

## Independently executed checks

A fresh source snapshot, with pinned dependency cache but no reused project build, compiles Challenge successfully: **3008 jobs, seven expected specification holes**. The separate no-proof `BoundaryAudit.lean` prints the actual definitions and all seven types and successfully checks the following pinned infrastructure:

- `Finset.le_sup`, `Finset.sup_le`, `Finset.exists_mem_eq_sup` for finite NNReal maxima.
- `IsGreatest.isLUB`, `IsLUB.csSup_eq` for the attained sharp supremum.
- `Matrix.det_mul`, `Matrix.det_permute`, `Matrix.det_eq_zero_of_column_eq_zero`, `Matrix.det_updateRow_add_smul_self`, and the actual block Schur determinant formulas.
- `Nat.fib_add_two`, `Nat.fib_le_fib_succ`; complex `norm_div`, `norm_mul`, `norm_sub_le`.

An independent search of pinned Mathlib matrix files found the reusable Schur-complement and determinant APIs, but no existing complete GEPP/front-growth theorem to presume as implemented infrastructure.

My independently authored exact Fraction/Gaussian-rational diagnostics pass **1,652 checks**:

- Reconstruct L,U and the literal input for every n=4,…,30; check all forbidden zeros, both corners, normalized entry maximum, triangular factors and nonzero diagonals.
- Execute the literal current-last swap path; check every maximal-modulus pivot, factor-column identity, entire chosen U row, original-label sequence, all active entries and final exact growth.
- Complex row/column phase transformations and nonreal scaling in n=4,…,9 preserve the exact squared growth and verify genuinely complex arithmetic.
- Enumerate every admissible tie branch for 40 fixed small complex samples, yielding 125 complete paths and no violation of the proposed bound.
- Confirm initial values 6,9,14,22.

These bounded diagnostics are neither an exhaustive search over inputs nor a universal upper-bound proof. They do not import or execute the contributor checker. Scripts, exact JSON, compiler logs and snapshot hashes are retained in this directory for later inclusion in the final statement-review evidence.

## Primary source precheck

I independently opened Higham's complete book PDF and consulted printed pp. 193 and 173. [Problem 9.15(b), PDF page 222](https://pages.stat.wisc.edu/~bwu62/771/hingham2002.pdf#page=222) asks for sharp GEPP growth for the tridiagonal pattern with both nonzero corners. It does not specify the field there. [Theorem 9.11, PDF page 202](https://pages.stat.wisc.edu/~bwu62/771/hingham2002.pdf#page=202) explicitly covers complex banded matrices and gives the ordinary tridiagonal comparison. This supports the canonical scope; it is not a new literature-completeness or priority search.

**Pending:** full contributor dossier/diagnostic inspection, exact ten-input freeze, final source-preservation/pin hash audit and final independent statement report. No final approval, mathematical Lean proof, axiom closure, Comparator success or Linux verification is asserted here.
