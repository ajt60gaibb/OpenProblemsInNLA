# TR-07 independent statement review 1

Phase: before mathematical proofs.
Reviewer: OpenAI Codex AI agent `/root/choose_algebra`.
Independence: I did not author or edit the definitions, Challenge, numerical-target document, or any proposed TR-07 proof. I independently read the actual files and the complete source proof. This is an AI-agent review, not human peer review or source-author endorsement.
Verdict: **APPROVE the statement boundary at the hashes below.** This is not approval of a proof or a Lean-verification claim.

## Reviewed revision and bytes

The worktree HEAD and canonical source base are both
`80c0e3e638b2f26dcb3a00353651fc3d2215dd65`. The new Lean directory was uncommitted when reviewed. Paths below are relative to the repository root unless prefixed `lean/`, which means this problem's Lean project.

| File | SHA256 |
| --- | --- |
| `docs/lean/REVIEW.md` | `d967ddce620d4e754e2f9c25548f30cb537f76f4ddcf8ecf2574945bcd332553` |
| `randomized-and-low-rank-approximation/TR-07/README.md` | `1f2b4c9bfd606f49d2c522483a7375cff104744e7a540db1613bb01f91a281d0` |
| `randomized-and-low-rank-approximation/TR-07/solution.tex` | `207eb87c6b47d3a3a1a529c49b7c5a4dcaf099a942d60fdc1b9b5e3285aae7a0` |
| `randomized-and-low-rank-approximation/TR-07/solution.md` | `307e8b419a4eb453e789120d86e1344b2aecaf8a8ce759f87d9585a470496fee` |
| `lean/NLA/TR07/Definitions.lean` | `d80638b68ed9fc06f3013edfefb743965de664c4bab312d03e239ee25fc80233` |
| `lean/Challenge.lean` | `0371225eaf7dfcf5691590cfcdd8bacbece0ceddb8716b04c01cd365ee3202cc` |
| `lean/NUMERICAL_TARGETS.md` | `4780404e41c13668ee57f7c4cff51a4bc9a09fbe1f7ea1f30b6fa936fd7c7a08` |
| `lean/comparator.json` | `019d6a019798a06088b14ddf2a2a7dc0e64b90d03b7d4afbf3062f04da6825b7` |
| `lean/lakefile.toml` | `96cc638603378e99856c50d6ee493e0ef6032a556613a80e2bf2a2b8777bd78e` |
| `lean/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean/lake-manifest.json` | `b1c95fe3e2259153b5659f36de95b6508c973d39ccc23124772a334650c3a19c` |

I read all of `solution.tex`, including its finite theorem, canonical asymptotic corollary, reconstruction, first-hit domination, coupling and concentration arguments; `solution.md` alone is only a pointer. The three canonical source hashes agree with `NUMERICAL_TARGETS.md`.

## Fidelity, quantifiers and nonvacuity

`random_column_subsets` states `SolvesTR07` without extra theorem hypotheses. Expanding that definition gives the full canonical asymptotic problem: every fixed natural `s >= 2`, every finite real `C >= 1`, every pair of natural sequences with `r k <= k`, the stated real-valued aspect-ratio limits, every deterministic signed sparse matrix sequence, and every fixed positive real threshold. The conclusion is the probability limit zero, not a conditional reduction or a selected family of matrices. There is no bound on support intersections, restriction on signs, exclusion of repeated columns, or distributional assumption on the deterministic matrices.

`SignedSparse` literally imposes entries in `{-1,0,1}` and exactly `s` nonzero row indices in each column. Requiring it eventually instead of at every initial index broadens the theorem, so the canonical all-index assumption implies the formal assumption immediately. This also avoids accidental impossibility from dimensions below `s`. It does not alter the eventual target.

The additional explicit `r k <= n k` is the well-definedness condition already implicit in a uniform `r k`-element subset of `n k` indices. It is not an extra geometric or probabilistic restriction. Global `0 < r k` was correctly avoided, since `r 0 <= 0`. The hypotheses are nonvacuous: for example, `C = 1`, `r k = k`, `n k = k^2`, and columns equal to the vector with its first `s` entries one for `k >= s` satisfy them; take arbitrary zero matrices at smaller dimensions. In this example the aspect ratios tend to one and infinity as required.

For general permitted sequences, convergence of `k/r k` to `C >= 1` implies that ratio is positive eventually; under real division's zero convention this excludes `r k = 0` eventually. An eventual finite upper bound on `k/r k`, together with positive `r k`, forces `r k` to infinity as `k` does. Thus empty samples occur only in an irrelevant finite prefix. These consequences are not inserted as unproved assumptions; the final proof must derive what it uses.

## Norm, infimum and sampling semantics

`Vec` and the selected coefficient space are `EuclideanSpace` over the reals. I inspected pinned Mathlib's `EuclideanSpace` abbreviation as `PiLp 2`, `EuclideanSpace.norm_eq` and `EuclideanSpace.real_norm_sq_eq`. The norm is the Euclidean norm, not the default sup norm on functions. `selectedAction` computes the finite sum of matrix entries times coefficient coordinates, with output explicitly wrapped into that Euclidean space. The domain is indexed by every member of the selected index set, so its dimension is the selected cardinality and no selected column is discarded.

`smallestSingular` is exactly the real infimum of all image norms of domain vectors of norm one. It does not substitute a positive singular-value enumeration, suppress a kernel, or require full column rank. For nonempty selected sets, a coordinate unit vector makes the infimum set nonempty and zero is a lower bound by norm nonnegativity. Thus the real conditional-infimum semantics are appropriate. For an empty selected set its Euclidean space has only zero and the unit sphere is empty; I checked the imported `Real.sInf_empty = 0` convention. This finite-prefix convention is explicitly documented and cannot affect the limit under the hypotheses above. The event is the required strict inequality `eta < smallestSingular`.

`subsetTail` filters `(Finset.univ : Finset (Fin n)).powersetCard r`, then divides the good cardinality, coerced to the reals, by the full cardinality. I inspected `Finset.mem_powersetCard`, `Finset.card_powersetCard` and `Finset.powersetCard_nonempty`: the space contains exactly all subsets of column indices of size `r`, its size is `n.choose r`, and it is nonempty under `r <= n`. Consequently the denominator is positive even when `r = 0`, where there is one empty subset. No zero-denominator convention is being used to obtain the conclusion. Distinct indices with equal column values remain different possible choices. This is precisely uniform sampling without replacement, with column ordering immaterial to the Euclidean-infimum definition.

The inspected Mathlib commit is `0df444a360eaa60ab8c11dca51a86af692955474`. Relevant actual imported source hashes are:

| Mathlib file | SHA256 |
| --- | --- |
| `Mathlib/Analysis/InnerProductSpace/PiL2.lean` | `1f9827b2db67213c725a2dcc3fec52a87772966d1fbd3fc6857a019dbd7a6053` |
| `Mathlib/Data/Finset/Powerset.lean` | `ffe38ab68a55fd3c24524e502afab8dad28588fb899157deae3976f24ff16b27` |
| `Mathlib/Algebra/Order/Archimedean/Real/Basic.lean` | `ba51e7d1078ee669a1b5e95968163937113d8ba729e9f2fb7e6ed0ebd66acfd0` |

## Numerical target and proof-scope audit

The source's Corollary 1.2 is the entire retained original target. Its stronger exponential finite estimate and positive fraction of small singular values are not part of that target. A proved finite estimate of the documented form `4/(rho^2*r) + (r-1)/(rho*n)`, with a positive constant fixed before dimensions, would suffice because `r -> infinity` and `r/n -> 0`. Declining to export the stronger source estimate therefore does not leave the original theorem partial. The documentation accurately discloses this choice.

The proposed deletion-number, finite trajectory and second-moment route is supporting proof architecture, not a premise hidden in `SolvesTR07`. The boundary imports no local proof module and assumes no reconstruction certificate, probabilistic oracle, concentration theorem specialized to the desired conclusion, or unproved matrix estimate. The final review must still check the entire route, particularly the nonempty/ bounded-below infimum uses, shared-reservoir simultaneous witnesses, signed transition means, unnormalized first-hit domination rather than false conditioning, and the equal-fiber bridge from ordered injective draws to this exact subset ratio. This statement review does not certify those future proofs.

Before approval I reread the revised planned route, which replaces the source's pruning with `D_i = p_i + 1/k` and an absorbing zero state. The definitions and Challenge did not change. The stated elementary bounds are consistent: the regularized trace is `s+1`; the conjugate covariance remains between zero and `s I`; the filter error bound becomes `s*(s+1)/(2*L+1)`. For `ell <= k`, the displayed chunk-hit lower bound follows by comparing denominators `1+ell*p <= 1+k*p`. The proposed `a = beta/(16*J+beta)` is at most `ell/(2*k)` under the displayed lower bound on `ell`, and at most one half, so it is consistent with domination of both nonzero and zero transition outcomes. The larger `L` and unchanged averaging bound give the documented squared-error budget. These are checks of the proposed numerical route, not substitutes for proving its kernels, expectation identities or final probability estimate in Lean.

## Type-check evidence and remaining gates

I independently ran `lake build Challenge` with Lean `4.33.1` on the reviewed files. It exited successfully with 2381 jobs; the only reported warning was the intentional `sorry` in `Challenge.lean`. The log I generated and inspected is `verification/statement-referee-1-build.log`, SHA256 `a72ea9ad68157a2cf5e54aba9deedad966790aa12a55717d7d7d731f9fa558a2`. This cached local macOS type-check is not a fresh Linux verification and proves no mathematical conclusion from the placeholder.

`comparator.json` names the single intended theorem, has no replaceable definition holes, and permits only `propext`, `Classical.choice` and `Quot.sound`. No Comparator run, completed proof axiom audit, or final proof approval is claimed here. Those remain separate gates, together with the second independent statement review and the final independent reviews required by `docs/lean/REVIEW.md`.

One nonblocking packaging defect was reported and resolved during review: `lake-manifest.json` initially retained the copied top-level package name `NLAKE03`. The final manifest hash in the table has the corrected name `NLATR07`, matching `lakefile.toml`; pinned dependencies and statement bytes are unchanged. There is no remaining statement-review correction request.
