# MD-03 independent proof review

**Reviewer:** Codex agent `/root/md03_independent_audit` (independent of the implementing agent)<br>
**Date:** 16 October 2026<br>
**Verdict:** PASS for the exact original target and the proof bridge. This is an AI source review, not external human peer review or a separate reproof of the imported Komlós library.

## Exact target

The permanent ID `MD-03` still points to `matrix-discrepancy-and-optimization/MD-03/README.md`. The original question asks for one finite positive constant working for every pair of positive dimensions and every real matrix whose columns have squared Euclidean norm at most one. It requires one sign in `{−1,1}` for every column and an absolute row-sum bound for every row. It makes no algorithmic demand and does not prescribe the sharpest constant.

`NLA.Statements.MD03.Target` has exactly those quantifiers and conditions. Its statement and the frozen `NLA.ReviewedStatements.MD03.Target` are definitionally equal in `Identity.lean`. The live and reviewed copies match the previously reviewed shared statement sources byte for byte. The proof supplies `C = 36`, which is positive and satisfies the original existential target. The sharper `3√(2π)` in the catalog's historical resolution is not a requirement of the problem.

## Proof and wrapper

The bridge in `NLA/MD03/Proof.lean` applies the pinned theorem `Komlos.discrepancy_le_of_forall_sum_sq_le_one` at precisely the column square-sum hypothesis. `Komlos.discrepancy_le_iff` supplies a colouring. The proof uses symmetry of equality to express its values in the reviewed sign convention, and `Komlos.colouringDiscrepancy_le_iff` gives the absolute bound on each explicit matrix row sum. The final theorem introduces `36`, proves positivity, and quantifies over all positive `m,n`, matrices and rows; it does not use a restricted matrix class or extra premise.

`Challenge.lean` contains one deliberate `sorry` in the challenge fixture. `Solution.lean` does not import the challenge. The comparator selects the exact declaration `NLA.MD03.target` and permits only `propext`, `Classical.choice`, and `Quot.sound`. The proof and its imported pinned Komlós theorem were accepted by the default Lean kernel in the [isolated Linux job](LINUX_CI_RECEIPT.md). The review inspected the bridge and declaration boundary; it did not independently rederive every lemma in the external library.

## Source identity

The reviewed proof source `NLA/MD03/Proof.lean` has SHA-256 `3e38a245007e2b860adacd97b89046d49b90f0f8e681dd5db43cafef6e97e93c`. The live target has SHA-256 `2638d903c1ccc478da9941f76d1903d838e4f6c5434ec1792dc1fbf811446b05`; the frozen target has SHA-256 `b86ff4b7f6268713024a85e81dd87793a04e288925b683a91febeee842426516`. The CI-tested proof file at checkout `4b5be52826d24d0e640862cf1a5a5620cc8d0312` is byte-identical to the proof on the 16 October main branch. The external Komlós dependency is pinned to `fac7d8f71f08caac7f5fe67786abe387cfe18b10`.
