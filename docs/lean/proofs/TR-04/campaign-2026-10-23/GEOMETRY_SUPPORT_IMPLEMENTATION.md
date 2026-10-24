# TR-04 unfolding, feasibility and actual optimum supports — 23 October 2026

Author: `/root/recover_geometry`. These are supporting results for the unchanged TR-04 target, not a complete program or a proof of that target. The two renewed statement/proof-route approvals preceded this implementation. The canonical Solution, original scaffold, mathematical boundary, status and permanent ID registry were not edited by this contribution.

## Frozen mathematical interfaces

All declarations below are in `NLA.Proofs.TR04` and use the actual immutable definitions in `NLA.Computation.TensorTrainApproximation`.

- `Reshape.lean`: `joinEquiv S j` is a bijection from the actual row/column index product to the original tensor index. `unfoldLinearEquiv S j` and `unfoldContinuousLinearEquiv S j` use the literal `Unfold` operation. Restricting an original index is their explicit inverse. `continuous_unfold`, `unfold_injective`, and zero/addition/scalar identities follow for the actual operation.
- `ReshapeFrobenius.lean`: `sum_unfold_indices S j f` proves exact finite-sum preservation. `frobeniusSq_eq_unfold_sum S j A Y` identifies the literal tensor squared error with the complete squared matrix-entry error at every cut.
- `Feasible.lean`: `feasible_zero S r`, `feasible_nonempty S r`, `isClosed_matrix_rank_le r`, and `isClosed_feasible S r`. The matrix theorem covers any finite real row and column types, including empty types. Tensor feasibility holds and is closed for every natural rank tuple, including zeros or bounds exceeding a matrix dimension.
- `Optimum.lean`: `continuous_frobeniusSq`, `frobeniusSq_nonneg`, `frobeniusSq_coordinate_le`, `frobeniusSq_self`, and `frobeniusSq_eq_zero_iff` prove the actual error properties. `exists_feasible_minimizer S r A` supplies a feasible tensor of no greater error than any other feasible tensor. `exists_optimum S r A` proves `∃ X, Feasible S r X ∧ Optimum S r A = FrobeniusSq S A X` for the original `sInf`. `optimum_nonneg`, `optimum_le_of_feasible`, and `optimum_eq_zero_iff_feasible` follow without auxiliary hypotheses.

## Mathematical proof route

Each row/column coordinate is a restriction to one side of the prescribed cut; every original coordinate falls in exactly one side. This proves the reshaping inverse identities, and finite-dimensional linearity gives continuity.

Matrix rank constraints are closed because cardinal rank at least `r+1` is open on continuous linear maps. The proof pulls that open set back along the genuine finite-dimensional matrix-to-continuous-linear-map linear equivalence, translates cardinal rank to the actual natural matrix rank, and takes complements. Intersecting its unfolding preimages proves closed tensor feasibility. No rank closedness or optimizer premise is introduced.

The sublevel set of feasible tensors with squared error at most the error of the zero tensor contains zero and is closed. Every squared coordinate error is at most that finite error. The elementary bounds `−(e+1) ≤ A(a)−Y(a) ≤ e+1` place the entire sublevel set in a compact coordinate box. The extreme value theorem produces a minimizer on this sublevel set. All other feasible tensors have larger error than zero, so this is a global feasible minimizer. Its value is the actual `sInf` by the least-element theorem. Nonnegativity and zero-error tensor equality then prove the exact zero-optimum equivalence.

## Execution evidence and reproducibility

`geometry-support-source-lock.json` freezes the four sources, immutable live/reviewed targets and tensor/machine models, and runtime/package pins. Each exported supporting result has an explicit LeanCert kernel assertion. Important endpoints print only `propext`, `Classical.choice`, and `Quot.sound`.

`author-fresh-geometry/result.json` records a successful fresh **author** replay: all six project modules (the four supports and two unchanged model dependencies) rebuilt with no project object reuse; a separately generated consumer checked the actual attained-optimum and zero-optimum signatures. Read-only pinned Mathlib/LeanCert dependency objects were reused explicitly. Source and consumer invocations both exited zero with Lean 4.33.1, compiler `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The frozen source bytes were checked before and after the build. Source/consumer logs and their hashes are retained beside the receipt.

Reproduce with `python3 docs/lean/proofs/TR-04/campaign-2026-10-23/replay-geometry-support.py --output /absolute/fresh/output`. The default tooling directory is the sibling persistent campaign `tooling` directory; set `NLA_CAMPAIGN_TOOLING` to an equivalent pinned tooling directory if relocated. The script refuses an existing project-object directory.

This result does not claim independent proof review, CI, Comparator acceptance, SVD totality, TT-SVD quasioptimality or an executable polynomial-time algorithm. Those remaining obligations belong to the wider TR-04 campaign. Author compile diagnostics preceding the frozen replay are retained separately and are not acceptance evidence.
