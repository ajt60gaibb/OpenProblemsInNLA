# IV-06 completed implementation: final-review handoff

**Complete local proof; two independent final proof reviews and actual Linux Comparator verification remain pending.** Implementation author: AI agent `/root/solved_statement_inventory`. Mathematical counterexample: Matthew J. Colbrook. AI-assisted formalization: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. No George email was added. Canonical status remains Solved.

The coordinator released the proof gate after independently approving both statement reports. Before creating any Proof or Solution source, `verification/proof-start.json` bound both approvals, all 32 frozen project inputs and all eight actual original Git source blobs. That gate has SHA-256 `c4769fd9d06b5e17589a223bad83e80ce60b8c6d5f05615e5059457adf2a38e9`. The final audit confirms all 32 + 8 original inputs remain unchanged, including the exact full mathematical boundary, pins and Comparator configuration. The two approved reports retain SHA-256 `68a4472868bd52e02e0d5ab70f4fb7d5131f3176cc0b8b8c1d1a74b78fd61d48` and `b4362f38f8dd4e92bdc24642c734b1ac514e2e39c07592096d5164a1ca601e2e`.

## Complete target and proof

All eight `Challenge.lean` declarations have complete exports in `Solution.lean`, with identical source headers and no definition exceptions. `Solution` imports only the complete proof; it does not import Challenge. The generic determinant bridge uses `Matrix.exists_mulVec_eq_zero_iff` and actual matrix/scalar algebra and includes dimension zero, without assuming a nonempty matrix index.

The full independent-entry box is proved equivalent to the two-parameter family, so no restricted-family premise replaces the original box. `family_characteristicDet` proves the actual unrestricted polynomial determinant identity. All four integer nonzero vectors satisfy their exact matrix equations and give actual attained-set memberships. Universal affine bounds prove that the determinants at the three separating real values lie in [−332,−32], [−318,−18] and [−3750,−150] for every admissible matrix.

`numerical_separator_margin` uses `interval_decide (trust := kernel)` to prove exactly `(-18 : ℝ) < 0`, with the singleton [0,0] domain. Every strict upper-margin bound consumes this certificate, hence every separator exclusion does as well. It does not compute approximate eigenvalues or certify topology. Exact affine algebra eliminates root isolation and interval subdivision.

The generic connected-component theorem uses the genuine preconnected component of the attained real subtype, its continuous inclusion into the real line, and Mathlib's interval-containment theorem. The four included values have an excluded separator between every ordered distinct pair. A genuine `Fin 4` injection into `ConnectedComponents` therefore proves the actual cardinal lower bound, without any finiteness hypothesis. The final theorem is the unconditional negation of the original all-positive-dimensions, all-real-independent-box conjecture. Exactly four components or component endpoints are not claimed and are not needed to settle that target.

## Fresh local validation and trust

`python3 verification/final/run_fresh.py` successfully elaborated Definitions, Proof, Solution, the actual proof-term inspector and the unchanged Challenge in a fresh separate prefix. `python3 verification/final/audit.py` passed all source, pin, signature and log checks. Definitions/Proof/Solution/inspection have no warnings or errors. Challenge has only its eight deliberate statement placeholders and was compiled in a separate Lean invocation; it establishes no result and is excluded from Solution's environment.

Seventeen explicit `#assert_trust kernel` checks passed: nine internal results including the retained numerical certificate, plus eight public exports. The corresponding seventeen transitive axiom reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`. Actual implementation sources contain no admissions, custom axioms, unsafe declarations, native execution trust or Challenge import.

The independent-prefix author inspector starts from the actual full-negation export, traverses **58 reachable project declarations**, and verifies **20 retained mathematical dependencies**. These include the matrix determinant equivalence, exact determinant formula, true connected-component and continuous-image/interval APIs, actual cardinal injection/counting APIs, every substantive local bridge and `LeanCert.Validity.verify_strict_upper_bound_dyadic_checked`. The scalar certificate is genuinely on the final theorem's dependency path. The checked cardinal simplification actually uses `Cardinal.mk_fintype` and `Fintype.card_fin`, equivalent to the `Cardinal.mk_fin` API named in the implementation plan; the inspector binds the actual proof constants.

All ten exact source repositories from MI-22's dependency cache were checked clean before and after and reused read-only. Both old MI-22 project objects and all previous IV-06 project objects were excluded. No dependency copy, Lake cache mutation or dependency rebuild occurred. This is local macOS Lean validation, **not** an actual Linux Comparator run; the manifest remains configured for independent clones in that later stage. Default target Challenge, registered Solution library, pinned Lean 4.33.1, Mathlib and LeanCert are unchanged.

Raw source snapshots and logs for development attempts are retained under `verification/development/`. One earlier final inspector expected the convenience theorem `Cardinal.mk_fin`, whereas simplification retained its equivalent cardinal/Fintype bridge; the failed inspection and complete raw proof-printing log remain under `verification/final/`. The corrected inspector checks those actual constants. A redundant tactic sequencing warning was fixed before the final clean build. No frozen statement or dependency pin changed for any implementation or audit correction.

## Frozen evidence and next gate

The final audit receipt has SHA-256 `d179328efe47e145cb0cc927f83e3d6294abebcc94681ca2fbbd3fbd4d387066`. The actual inspection log has SHA-256 `3847829f076d59b440c356e12df9136282cbe48418f619aead00b1c467c39ae8`. Its complete fresh result receipt has SHA-256 `c5dc36f1498ca2ee145c7330b45d35dbe288ad020f5ae9def919d353ed0e6cbc`. Source hashes are:

- Definitions: `283a31f8e9d100347e5403b8e5688feebd13968d865d487b4962eaa1f861b195`.
- Proof: `600311e699fecc178f921e8233a9c14d50774db5980ea63560040e578d896333`.
- Solution: `b4b9ab44b95accb5f4a0b677d417937cc0ca9ae6c9f08409b2c178ef0d8f699d`.
- Challenge: `77be095dc706c901714caa68d3393bf95004fc5f9fee2fa43f7460dafa342b90`.
- Numerical targets: `f51f4118af540fa4d3c8e16b40d859ee730c40c8417c4e45f86dc0e5c58a04d9`.

`verification/proof-freeze.json` binds every current project source and evidence file except its own exact path, plus all eight original source hashes and the exact Git source commit. It includes this report. All compiled objects remain outside the repository. Source-stage README and correspondence are preserved as frozen historical inputs; a reviewed candidate wrapper can be prepared only after final proof reviews. There was no canonical edit, commit, push, publication or user-worktree change.

Root should assign two independent final referees to the frozen actual implementation and evidence. A later successful Linux Comparator/default-kernel run with actual controls and an independent operational audit remain necessary before any Lean-verified promotion.
