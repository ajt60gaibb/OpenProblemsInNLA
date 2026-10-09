# TR-04 independent lean-boundary review

Reviewer: OpenAI Codex AI agent `/root`; verdict: approve.

I read the concrete SVD machine, shared tensor helper, final live/frozen target and implementation notes against the approved full specification. Shape includes every order>=3 and every mode>=2. All order-minus-one cuts use complementary dependent product indices, their joined tensor entries and actual real matrix rank. Every positive prescribed rank is admitted without upper truncation or consistency restriction.

The Frobenius squared error sums every coordinate. The true feasible-error infimum is well-defined and attained by the usual finite-dimensional closedness/coercivity argument; no minimizer is supplied to the machine. Positive optimum requires the strict factor d-1 and zero optimum requires exact returned tensor equality. No genericity or conditioning restriction changes these cases.

The finite SVD instruction validates full orthogonal bases, all nonnegative ordered singular values and exact old-store reconstruction. It admits every valid tied basis. All three disjoint output blocks are written, overlapping outputs fail distinctly, and empty blocks and input overlap have explicit semantics. Scalar instructions have genuine old-state semantics and forbidden operations fail; no real-to-natural, optimization or free matrix-product oracle is added.

LegalTrace fixes each transition and its real charge: every running scalar/halt costs one and each SVD costs (rows+columns+1)^3. Terminal states absorb at zero cost. Target both requires a legal trace and quantifies every legal trace, precluding vacuous absence or a favorable selected SVD response. One finite program, positive coefficient and natural exponent precede all formats, ranks, inputs and responses.

Input placement includes all modes, ranks and dense entries with last-index-fastest offsets, and no optimizer or spectral advice. Positive radix sizes give the standard offset/decode bijection. Returns reads exactly all original-shaped dense entries from a genuinely halted pointer. Size includes dense entry count, order and numerical rank sum; this is the approved idealized arithmetic/SVD convention, not a binary complexity claim.

Independently rebuilt SVDMachine, TensorTrainApproximation, live/frozen TR04 and all ten SVDControls with pinned Lean 4.33.1. Every compilation and the actual rfl Target identity passed with only propext, Classical.choice and Quot.sound. Controls exercise tied bases, rejection, block writes, charged transitions, failure/halting and mixed-radix layout. These are operational/identity checks, not a proof of the tensor solver or Linux Comparator result.

Review is independent automated-agent source/statement review, not external peer review or a mathematical proof. The companion JSON binds the exact inspected bytes.
