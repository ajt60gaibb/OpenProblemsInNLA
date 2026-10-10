# SP-14 regularized factor Wiener size: independent pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen exact contract for implementation. It computes the literal weighted Wiener size of the actual regularized exterior factor, not the later background product bound or SP-14 Target.

| Reviewed input | SHA-256 |
| --- | --- |
| `REGULARIZED_FACTOR_WIENER_PRE_REVIEW.md` | `0b4d81edae6e0e7c448b3a26559e5c81638a2f3c11b344aa8918d51a658c78cf` |
| Frozen `NLA.Statements.SP14` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Audited Fourier factor source | `2afdee09ed97dbae6b64529c8a0af23c322ce57619e6b658e3355f52872b64fc` |
| Audited regularized coefficients | `09aac1a792bbfaf481c94ff2ff2f294bb2ea451afe87d2b3aa9199b34cac4aa6` |

The manuscript's norm is `Σ_{k∈ℤ}(1+|k|)^β|F_k|`, with real exponent `β=9/8`. Since integer `natAbs` is exactly `|k|`, the proposed `wienerWeight` matches the source weight and uses real exponentiation. The reviewed all-integer Fourier theorem applies to the frozen normalized interval integral: one positive mode `F₁=1`, nonpositive modes `F_{-n}=d_n`, and no modes `k≥2`. Thus the bilateral index partition has one contribution `2^(9/8)` at `k=1` and exactly one contribution `(n+1)^(9/8)||d_n||` for each `n≥0`. The `n=0` term is the unique zero-frequency term.

The existing public weighted summability theorem is precisely `Summable (fun n => ((n+1:ℝ)^(9/8:ℝ))*‖d_n‖)`. It supplies the negative and zero side without a finite-cutoff assumption; a singleton supplies the positive side. Consequently the proposed summability and exact `tsum` equality are valid. The checks `d₀=3/2`, `d₁=3/8`, `d₂=−1/16` agree with the frozen coefficient proofs; their weights at `k=0,-1,-2` are `1,2^(9/8),3^(9/8)`. No rounded computation is needed.

Implementation must preserve the literal `ℤ` sum, the real `9/8` exponent, the actual Fourier integral, and both `k=0` and `k=1` without duplication. Keep the source unimported until a separate source/signature/LeanCert kernel audit. The endpoint inverse, nonlinear estimates and final counterexample remain open.
