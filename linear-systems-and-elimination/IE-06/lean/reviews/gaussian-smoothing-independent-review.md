# Independent actual-code review: Gaussian smoothing

Reviewer: infrastructure/Gaussian agent, independent of root author. Verdict: APPROVED.

Reviewed exact source hashes:

- GaussianSmoothing.lean: `a2027c75d5609b9ff4d1e1b04a25cb1c3c6ee701b949fcfb8de8da4652987e0c`.
- EliminationSmoothing.lean: `388bad9258e5a2abc6f632c5d0de494749db7251db9e76dc9101ceea2f93b545`.

The reviewer read both entire modules and independently rebuilt their complete 18-module local dependency closure under pinned Lean 4.33.1. All kernel trust assertions passed, every printed axiom list contains only propext, Classical.choice, and Quot.sound, and no warning or error was emitted. The before/after source hashes and command output are recorded in `gaussian-smoothing-independent-compilation/receipt.json` and `compile.log`. This is local macOS verification, not an authoritative Linux Comparator run.

The deterministic proof uses the literal row Euclidean norm and row l1 norm, a genuine right inverse of QᴴG, and the exact cancellation JE=J(X-XGPQᴴ). The triangle and subordinate operator inequalities then give the claimed row estimate. No uncontrolled norm of Y survives. The spectral pseudoinverse is substituted only with explicit positive-definite row Gram and its proved right-inverse identity.

The Gaussian row proof uses the actual transposed iid law and a deterministic n by 1 column; its Frobenius square is exactly the original squared row norm. Bounding its true operator square by this same value is sufficient and does not introduce a dimension factor. Threshold enlargement is in the correct direction. The square-root conversion handles ζ=0 and all empty dimensions. The finite union count is exactly n.

The compression theorem is applied to the actual QᴴG, and the rectangular A2 bound has q≤r and 3r≤s as required. Its threshold is precisely 3 exp(2+x/r)/r. The full-row-rank exceptional set is removed almost everywhere via the same pushforward law; no additional probability is spent. On the intersection of the two good events, the deterministic argument works for every J satisfying the displayed algebraic and row-l1 premises. The arbitrary function J may depend on G without an independence hypothesis. The theorem correctly states an outer-measure bound for its exact bad set, and `Measure.le_map_apply` is used in the valid direction when no event measurability is needed. Final union factor is n+1.

No mathematical defect or requested source change was found. This approval is for these supporting lemmas; it does not assert completion of the overall IE-06 theorem.
