# SP-14 finite negative Laurent Wiener size: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen first finite-product module for aggregate import. It proves the exact Wiener size of a finite negative Laurent correction under the frozen interval integral; the generic multiplier and actual product bounds remain open.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/FiniteNegativeWiener.lean` | `987b861269f0ac1712b548c055447044f26d9fe6e509362a4a2647c5fcb81a33` |
| Exact finite-product contract | `96e380a841054940a4ac07ffbee67dcef4eac45efac75979fcf991e5c82bad9d` |
| Independent mathematical pre-review | `6a27de7fa30a4ad287568928efcb38870045816b66849b83b50042a9c45b20d4` |
| Separate imported audit `/private/tmp/sp14-finite-negative-wiener-independent-audit.lean` | `a89dca86decc86001656d60def0a2eda4ac59aadedf0ac657f8af582533d7a0f` |

The source defines the exact finite size `Σ_{j∈Fin u}w(−(j+1))‖q_j‖` with the literal previously audited `9/8` weight. It proves finite linearity under the actual `FourierCoefficient` real-interval integral and uses the audited pure-mode orthogonality. The map `j↦−(j+1)` is injective, so at each integer frequency the finite Fourier sum has either one coefficient or zero. Summing these finite-support values over all integers gives the exact `weightedWienerSize(negativeLaurent u q)` equality, including `u=0` and any vanishing coefficients. No formal coefficient surrogate or duplicated zero mode is introduced.

The pinned Lean 4.33.1 direct module build passed 2,766 jobs. My separate imported LeanCert audit exited zero, checked the literal finite size and equality signatures, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]`. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

Weighted convolution, generic multiplier summability and constant-one bound, the contact-derived `g₀P₋` bound, the other smallness estimates, background inverse and full SP-14 Target remain open.
