# SP-14 exterior boundary square and zeros: independent pre-proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `BASE_EXTERIOR_BOUNDARY_SQUARE_PRE_REVIEW.md` for implementation as a separate boundary-series result. The proposed signatures are exact and do not claim the final SP-14 counterexample.

For `z:Circle`, the already defined symbol is the absolutely convergent series `Σ' c_n z^(1−2n)`, with `c_n=Ring.choose (1/2:ℂ) n`. Because `z≠0` and `q=z⁻²`, integer-power arithmetic gives `z^(1−2n)=z q^n`. The certified `Summable (fun n => ‖c_n‖)` and `‖q‖=1` prove absolute summability of `b_n=c_n q^n`; this is the needed hypothesis for a genuine complex Cauchy-product theorem at the boundary. The finite antidiagonal coefficient is `q^N ∑_{p+r=N}c_p c_r`, and the certified convolution is `1` for `N=0,1` and `0` thereafter. Thus the square of the `b_n` sum is `1+q`, and multiplying by `z²` gives **for every circle point** `baseExteriorSymbol z ^ 2=(z:ℂ)^2+1`, including points with `z²=-1`. At such a point the right side vanishes and the integral-domain property of `ℂ` yields `baseExteriorSymbol z=0`.

The separate endpoint cases `N=0,1` and the nonzero base `z` are correctly retained. The square equation by itself would leave a sign ambiguity; the frozen series has `c₀=1` and leading term `z`, so it fixes the normalized exterior branch before the square theorem is proved. The proposed proof does not invoke formal-power-series evaluation at a boundary point without convergence, and it adds no annular-extension or final-counterexample claim. The already certified all-odd-order base Toeplitz characteristic polynomial remains independent of these boundary-zero theorems.

| Reviewed input | SHA-256 |
| --- | --- |
| **`BASE_EXTERIOR_BOUNDARY_SQUARE_PRE_REVIEW.md`** | **`84daf3905d3625d2f561f3dae9c2e0883c3a2d7d8bbffc93cc38280e22d72576`** |
| `BASE_EXTERIOR_SERIES_FOURIER_PRE_REVIEW.md` | `aed55ffe098560355c0f7dbeecdd313d42bf53ecd93bc1633c7f8299d459b67d` |
| `BaseCoefficient.lean` | `63dcd98bb3a45e77b2b0fd2644d444f9cfe866fb9dae5535d1b7cd1f73081bf4` |
| `BaseCoeffSummable.lean` | `1da659ff573ddee8d598d32150fec45f7ae5d5eb023c2a9277a0500547ad9892` |
| `BaseExteriorSeries.lean` | `8e19c9af8809fc44414b90696a089d32417934475adc95f58aafa6db5b83dd0d` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |

Changed source bytes reopen this pre-review. No boundary-square Lean theorem has yet been audited here.
