# SP-14 literal regularized factor Wiener size: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen source for aggregate import. It proves exact finiteness and value of the manuscript's bilateral `9/8`-weighted Fourier norm for the actual regularized exterior factor. It does not prove a background product estimate or the SP-14 Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/RegularizedFactorWiener.lean` | `0cae3d40e5b72928eb4df9a4dfbfe43a52766aebb78a993143411fa0f3432b83` |
| Exact pre-implementation contract | `0b4d81edae6e0e7c448b3a26559e5c81638a2f3c11b344aa8918d51a658c78cf` |
| Independent mathematical pre-review | `9a3ccf8cd08f74b70eb5cb268894a290430391b5c0b2ec4684393d96dddd8057` |
| Separate imported audit `/private/tmp/sp14-regularizedwiener-independent-audit.lean` | `55adb3f2f19d3461185a76db8222b81d3bd65771ccd39c71ddba4507f0c52f22` |

The definitions use the literal integer-frequency sum of `(1+|k|)^(9/8)‖F_k‖`, with `natAbs` representing `|k|` and real exponent `9/8`. The source reduces the frozen integral Fourier coefficients to one positive mode `k=1`, the single zero mode, and the negative tail. The positive mode contributes `2^(9/8)`. The negative and zero modes contribute exactly `Σ_{n≥0}(n+1)^(9/8)‖d_n‖`, with `n=0` counted once. The previously audited weighted coefficient summability supplies finiteness of that tail. No arbitrary-function Wiener finiteness is asserted.

The pinned Lean 4.33.1 direct module build passed 2,764 jobs. My separate imported LeanCert audit exited zero, checked the exact definitions and theorem signatures, reran both `#assert_trust kernel` checks, and printed only `[propext, Classical.choice, Quot.sound]` for both results. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

Endpoint division for finite Laurent corrections, convolution norms involving those corrections, background-dependent inverse estimates, the nonlinear counterexample and frozen SP-14 Target remain open.
