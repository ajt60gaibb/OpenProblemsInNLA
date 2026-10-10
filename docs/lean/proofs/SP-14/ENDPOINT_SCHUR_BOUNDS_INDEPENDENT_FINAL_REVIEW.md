# SP-14 exact scalar Schur bounds: independent final review

**Source author:** `/root/sp14_base_proof`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the two exact scalar infinite-sum bounds for aggregate import. Finite Fourier-kernel Schur inequalities and the frozen SP-14 Target remain open.

The exact mathematical and numerical contract was independently approved before implementation in `ENDPOINT_WEIGHTED_SCHUR_INDEPENDENT_PRE_REVIEW.md`, against author contract SHA-256 `0433186b4e5af5637f31ebc752e13b4f545a5639a0fa4e4a547e9ff8ce205c21`. The frozen source `lean-statements/NLA/Proofs/SP14/EndpointSchurBounds.lean` has SHA-256 `cd466b5f516283210f0f58f70e1672abc009818fd89f609592b502d13d0e9db0`.

I read the complete source. The row proof splits the literal `k≥0` sum at `k=j`, applies the independently audited prefix bound to `k<j` and strict-tail bound to `k≥j`, and cancels the exact powers to obtain `1+1/r+1/(1−r)` for every `j≥1`. The column proof maps the literal `j=t+1≥1` sum to the same row theorem at exponent `1−r`, preserving denominator `t+1+k` and the symmetric constant. Both include `j=1` and `k=0`, with no zero-frequency column term, asymptotic estimate, or floating-point calculation. The source has no proof escapes or custom axioms.

The pinned Lean 4.33.1 direct build passed. A separate imported exact-signature audit `/private/tmp/sp14-endpoint-schur-bounds-independent-audit.lean` (SHA-256 `ef59fe9bf6e3db99f18206c0949966b2c74c6fda2a4608ce5bd421bd5249ee53`) checked both public `tsum≤C_r` theorems, two `#assert_trust kernel` directives and transitive axioms. Both `#print axioms` results were exactly `[propext, Classical.choice, Quot.sound]`. The aggregate build is recorded in PR verification after import.

The scalar sum bounds do not yet prove the finite Schur inequalities for `endpointKernelAbs`, the infinite-dimensional extension operator estimate, the inverse Hilbert–Schmidt bound, or the full negative Target.
