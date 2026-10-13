# SP-14 negative product Fourier support: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen source for aggregate import. It proves every nonnegative Fourier mode of the actual contact-corrected `g₀P₋` vanishes under the frozen interval integral. It does not prove a weighted norm bound or the SP-14 Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/NegativeProductFourierSupport.lean` | `a8bcd7a9c899d52f8a47634fd635a22e57a4643fc4272f00a694942b57aa6cc4` |
| Exact pre-implementation contract | `523cbf9b7b9b478367459a99b0cff7768a8f1df4ea6edaea6e046fe038269dc0` |
| Independent mathematical pre-review | `9fcb22345c612a8d47ed6dba5704ef38ba072748c736cd4a6465e2c6d33d051d` |
| Audited endpoint division source | `d4d6fddadfa9d2b306faf88ca03a4cda0391fc59130d89db9ab914c970ffb19b` |
| Separate imported audit `/private/tmp/sp14-negative-support-independent-audit.lean` | `6dd3194d0e06b4399f72ad2cc3443b969347f5f8813ec61d65b711e72b333955` |

The source uses the actual endpoint division `P₋=(1+s)Q₋` and hence the pointwise identity `g₀P₋=FQ₋` for the audited regularized factor `F`. It proves directly from the frozen real-interval integral that multiplication by the circle monomial `s^ell` shifts a Fourier coefficient from `k` to `k−ell`. For `Q₋`'s `j`th term, this shifted frequency is `k+j+1`. At `k≥0,j≥1` it is at least two, where `F` has no Fourier mode; at `j=0` the actual quotient coefficient is zero. Finite-sum linearity uses continuity of each term, with no infinite interchange.

The theorem includes `u=0` and `u=1` through empty or zero sums; for `u=2,p=(t,t)`, the quotient is `t s⁻²` and the highest product frequency is `−1`. The public signature retains the actual `baseExteriorFactor * negativeLaurent` function, the source's contact hypothesis, every integer `k≥0`, and the frozen `FourierCoefficient` definition. It introduces no formal coefficient surrogate.

The pinned Lean 4.33.1 direct module build passed 2,766 jobs. My separate imported LeanCert audit exited zero, checked the exact public source/integral signature, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]`. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The literal weighted Wiener norm of `g₀P₋`, its convolution bound, the other source smallness conditions, background inverse, counterexample and frozen SP-14 Target remain open.
