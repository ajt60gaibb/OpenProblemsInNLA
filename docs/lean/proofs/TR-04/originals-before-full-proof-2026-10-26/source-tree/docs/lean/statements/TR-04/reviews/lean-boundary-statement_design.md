# TR-04: independent final Lean-boundary review

Reviewer: /root/statement_design (OpenAI Codex AI agent), 2026-09-28.
Verdict: **approve** for these bound bytes.

## Fidelity reasoning

1. The final live/frozen target, entire SVDMachine, entire TensorTrainApproximation, all SVDControls and final implementation notes were read against the approved specification and retained original. Author is /root/infra_audit; this reviewer authored neither the specification nor implementation.

2. Shape encodes precisely order>=3 and each mode>=2. Index is the actual finite dependent product. Every Cut is a prefix/suffix partition at j+1, RowIndex and ColIndex split complementary actual mode coordinates, join includes each mode once, and Unfold reads the corresponding actual tensor entry. Feasible applies real Matrix.rank, whose pinned definition is the dimension of the actual multiplication range, to every cut and every prescribed positive rank.

3. FrobeniusSq sums every tensor coordinate. Optimum is the actual real infimum of feasible squared errors, a nonempty set bounded below by zero because zero is feasible. Closed determinantal constraints and finite-dimensional bounded minimizing sequences justify its correspondence to the attained minimum; no arbitrary optimizer or optimal-error function is quantified. Target retains strict error<(order-1)*Optimum for positive optimum and exact X=A at zero.

4. Program has finite control, finite scratch/address registers and a finite real constant table, all fixed before every input. Each ordinary instruction has explicit scalar semantics from old operands, with no arbitrary evaluator, random draw, real-to-natural operation, rank oracle or free matrix product. Division by zero and negative-square-root arguments yield failed status; truncated natural decrement and every finite continuation are explicit.

5. ValidSVD specifies full square U,V column orthonormality, every nonnegative singular value in nonincreasing order and literal reconstruction across all min(m,l) indices. Square column orthonormality gives full orthogonal bases. This relation includes every sign, repeated-singular-value and zero-space basis choice and the exact empty-dimensional case; no answer-selecting spectral oracle is present.

6. readMatrix accesses base+i*l+j in the old store. OutputBlocksDisjoint tests all pairs of half-open U, sigma, V ranges, correctly exempting empty blocks. On disjoint blocks, writeSVD materializes every cell with ordinary quotient/remainder row-major lookup and preserves every outside old cell. The reconstruction uses the entire old input before writes, so overlapping input/output is legitimate, whereas overlapping output blocks fail. A valid SVD step changes only next label and these cells.

7. Step handles SVD opcodes through their explicit existential full-data relation and never invokes ordinaryStep's defensive SVD failure case. Every valid reply gives a permitted next state. Other constructors use the literal deterministic scalar step. Failed and halted states are distinct absorbing states, so a failed state cannot later return an output.

8. charge depends only on actual instruction and state: running scalar instructions including halt cost one, every SVD instruction costs (rows+columns+1)^3, and terminal continuation costs zero. Step equates trace.cost to this charge. LegalTrace fixes the exact starting state and every step; CostThrough sums precisely the t executed transitions preceding state t. Trace fields cannot manufacture a smaller runtime.

9. Target chooses one Program, positive natural C and natural exponent k before every shape, rank vector and real tensor. It conjoins existence of a legal infinite trajectory with successful bounded output and all mathematical requirements for every legal trajectory. No favorable SVD branch is selected. Full SVD existence and ordinary total stepping allow all legal finite choices to continue; positive running costs make the bound a genuine worst-case termination bound.

10. InputMemory contains mode sizes at 0..d-1, ranks at d..2d-2 and all N tensor entries starting at 2d-1, with zero elsewhere. The preceding branch guards ensure natural subtraction cannot alias earlier headers into tensor data. Initial label and natural register zero are fixed; only register zero contains d, and all scratch/other registers start zero. The input contains no optimizer, ranks of unfoldings, SVD data or error oracle.

11. SuffixSize multiplies exactly the modes strictly later than each index. Offset is the usual last-mode-fastest mixed-radix sum; Decode divides by these positive suffix products and reduces modulo the positive radix. These are mutually inverse on the N dense offsets, so every input coordinate and every returned output coordinate is represented exactly once. Quotient/remainder occur only in fixed placement/materialization, never as real-to-integer executable instructions.

12. Returns requires an actually halted address and reads every tensor coordinate from that pointer plus Offset in the original fixed shape. The complete entries must already exist in memory; no output oracle supplies them. Size=N+d+sum(r)+1 is the approved numerical arithmetic-size scale. Optional charging of N output-serialization operations changes only the polynomial coefficient/exponent, not the stated existence question.

13. The shared TensorTrainApproximation module preserves the previously inspected concrete definitions while ensuring live and frozen declarations use the same nominal Shape/index types. The final statement bodies match exactly apart from the standard frozen comment and namespace. Their actual rfl identity was executed in the author evidence; no textual comparison alone is substituted.

14. SVDControls was read in full: ten exact controls cover scalar reconstruction, negative sigma rejection, distinct tied bases, empty/overlap guards, all bulk writes, actual SVD cost 27, guard failure, separately charged halt, absorbing zero cost and stamped mixed-radix placement. Kernel trust assertions cover every control. These are useful operational checks, not proofs of general SVD existence, mixed-radix inversion, solver correctness or the TR-04 approximation theorem.

15. Author-final receipts bind the current model/helper/control/live/frozen sources and show exit zero for each, plus a genuine rfl identity. Live and frozen logs report only propext, Classical.choice and Quot.sound; controls select kernel trust and passed without a native decision axiom. This reviewer inspected these author-executed outputs but did not run a separate Lean or Linux Comparator check. The final report binds the complete local import closure and pins, with SVDControls included explicitly even though the target does not import it.

## Pinned external definitions inspected

- Mathlib/LinearAlgebra/Matrix/Rank.lean: 67b4fa7bee02c1806f29562718bfb34c0e1f40af5ec6a91ef91cc33610657491; Actual matrix rank as finrank of multiplication range.
- Mathlib/Order/ConditionallyCompleteLattice/Basic.lean: 4e4c9abe9993f2334c389d6cb4b75b31b44bb66bb87b65a95b3abac2dbd9fcc8; Conditional infimum characterization on nonempty bounded-below real sets.

## Author-local evidence inspected

- /private/tmp/nla-tr04-evidence/result.json: 8b8630930cef2c286c4b1242d4253d1e37341d7bd5f4f6e0a1886c61b8e7ed44
- /private/tmp/nla-tr04-evidence/final-inputs.json: 0192474b0c27d541440d8a44482b962cbb2d053923a958044853a059040ec53e
- /private/tmp/nla-tr04-evidence/Identity.lean: 09d3390d7f9acacfd48febf038da8719062de34d1afda894329471e668a859df
- /private/tmp/nla-tr04-evidence/identity.log: 2a3954627795f50423fd88b74045fed1aa6fcc709aa93aa4113bc4d4ac5d9a30
- /private/tmp/nla-tr04-evidence/NLA-Statements-Infrastructure.log: 2a3954627795f50423fd88b74045fed1aa6fcc709aa93aa4113bc4d4ac5d9a30
- /private/tmp/nla-tr04-evidence/NLA-Computation-SVDMachine.log: 2a3954627795f50423fd88b74045fed1aa6fcc709aa93aa4113bc4d4ac5d9a30
- /private/tmp/nla-tr04-evidence/NLA-Computation-TensorTrainApproximation.log: 2a3954627795f50423fd88b74045fed1aa6fcc709aa93aa4113bc4d4ac5d9a30
- /private/tmp/nla-tr04-evidence/NLA-Statements-TR04.log: aef21d9f7d50f4e1349a299362cbb47e0407d617538f08388c4de7fcc986186b
- /private/tmp/nla-tr04-evidence/NLA-Computation-SVDControls.log: 2a3954627795f50423fd88b74045fed1aa6fcc709aa93aa4113bc4d4ac5d9a30
- /private/tmp/nla-tr04-evidence/Reviewed-TR04.log: 8fca63d1d72af550d5b7c3ff5cf5edcc5f92f06a3ea0c6add16320e7fabaad72

## Bound inputs

- docs/lean/statements/TR-04/IMPLEMENTATION_NOTES.md: a661d83390918eef7ceb893f9e035bb569eb955f361b4f1df2f670e8e09f2390
- docs/lean/statements/TR-04/NUMERICAL_TARGETS.md: f1bfd6d4a73a326a5dec79c052dba4f5ae38cc2f4c9e40622492a7694c5074f4
- docs/lean/statements/TR-04/ORIGINAL.md: 614dfc1189a99b0c2de54a04b948c01d35301d468e0b723c7fcb34b9918957cf
- lean-statements/NLA/Computation/SVDControls.lean: 340bed2b81f7a74853d06847f8af4562600548801254a770de1a97e7fd6fac54
- lean-statements/NLA/Computation/SVDMachine.lean: 8ec5866326b5a311b334651600db5d7f3065f2059175823626319afef7cf7581
- lean-statements/NLA/Computation/TensorTrainApproximation.lean: 05038abcc6cf85d422cf580b3cc527e7aa7dad146802da5621911b6331494d2d
- lean-statements/NLA/Statements/Infrastructure.lean: 8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37
- lean-statements/NLA/Statements/TR04.lean: 6f595cd3fa4c5d317bc757628a3e7858ab4576c90cbe967ac5289c8b3fbd780c
- lean-statements/Reviewed/TR04.lean: 5b2260e25e8ce7dda5455a3cf11a5c16fc2493ce3d0cf1ab84a447d2fb1f54cd
- lean-statements/lake-manifest.json: a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8
- lean-statements/lakefile.toml: 1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40
- lean-statements/lean-toolchain: 3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71
- tensor-computations/TR-04/README.md: 614dfc1189a99b0c2de54a04b948c01d35301d468e0b723c7fcb34b9918957cf

## Limits

Independent AI-agent final source-level fidelity review of the complete TR-04 target and shared SVD/tensor/control implementation, independent of author /root/infra_audit. Approval concerns exact meanings and bound bytes, not the truth of Target, a solver, formal codec/SVD existence proofs or an independently executed kernel/CI run. Author-local build evidence is separately labelled and hash-recorded below; it is not misrepresented as reviewer execution.
