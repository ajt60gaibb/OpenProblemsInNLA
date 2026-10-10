# SP-14 base square-root coefficients: independent Lean source review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `BaseCoefficient.lean` as the exact **formal coefficient-convolution component** of the approved base odd-characteristic-polynomial route. It does not construct the boundary symbol, identify Fourier integrals, prove the odd Toeplitz characteristic polynomial, or prove the final SP-14 counterexample.

`baseCoeff k : ℂ` is `Ring.choose (1/2 : ℂ) k`, Mathlib's generalized binomial coefficient. The pinned `PowerSeries.binomialSeries` is defined with coefficient `Ring.choose r k`; thus these are exactly the formal coefficients of `(1+X)^(1/2)`, not an approximate sequence. The usual falling-factorial formula gives `c₀=1`, `c₁=1/2`, `c₂=(1/2)(−1/2)/2=−1/8`, and `c₃=1/16`. The negative `c₂` remains the required third-superdiagonal Fourier sign check for later work.

`baseSeries_square` uses the pinned binomial-series addition identity at `1/2+1/2=1` and the natural-exponent identity to prove the exact formal power-series equality `binomialSeries(1/2)^2=1+X`. `baseCoeff_convolution n` then takes coefficient `n` of that equality and expands the product over `Finset.antidiagonal n`. Its RHS is one for `n=0`, one for `n=1`, and zero for every `n≥2`; both endpoint cases are included in its universal natural-number theorem. This is the exact finite convolution needed for the later matrix identity `G²=I+U`. No analytic square-root branch or boundary convergence follows from a formal-series identity alone, and the module makes no such claim.

I ran pinned `lake build NLA.Proofs.SP14.BaseCoefficient` and a separate imported Lean audit that checked both elaborated theorem signatures, `#assert_trust kernel` for both theorems, and their transitive axioms. All passed under Lean 4.33.1; each axiom list is exactly `[propext, Classical.choice, Quot.sound]`. The source has no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseCoefficient.lean`** | **`63dcd98bb3a45e77b2b0fd2644d444f9cfe866fb9dae5535d1b7cd1f73081bf4`** |
| `BASE_ODD_CHARPOLY_PRE_REVIEW.md` | `2d065496f7d7a4e4abc84005b801ec3891c0089f57e28f849c79c858521c666a` |
| `BASE_ODD_CHARPOLY_INDEPENDENT_PRE_REVIEW.md` | `f7a63e4782b5c29f27fbdac58ffe1ee7e0d517827492a33a1816e37339d375c1` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Pinned Mathlib `RingTheory/PowerSeries/Binomial.lean` | `a6b92b59f164c0546bf4d2f332cf613103fde60b586d1476125ac3f8554e00f8` |
| Pinned Mathlib `RingTheory/Binomial.lean` | `13039239d985565fbf327c2d32db7498e02668334c8156d9ca75dc1de210d9bf` |
| Independent `/private/tmp/sp14-basecoefficient-independent-audit.lean` | `b679c45a416168133be3005d3ad9674b4daeec88b9c5b11a6229b0fec184573e` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed source or contract bytes reopen this review.
