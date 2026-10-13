# SP-14 integer Fourier modes: independent Lean source review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `BaseFourierMode.lean` as an exact kernel-checked orthogonality theorem for **individual integer circle monomials** under the frozen SP-14 Fourier integral. It does not justify termwise integration of the infinite base-symbol series or identify the Fourier coefficients of that symbol, the actual Toeplitz blocks, or the final SP-14 `Target`.

The public theorem quantifies over **all** integer powers `ell` and Fourier frequencies `k`, including negative integers, and concludes

```text
FourierCoefficient (fun z : Circle => (z : ℂ)^ell) k
  = if ell=k then 1 else 0.
```

This uses the existing `NLA.Statements.SP14.FourierCoefficient`, whose sign is `exp(−ik t)` and normalization is `1/(2π)` over the genuine real interval `0..2π`. `Circle.exp t` has complex value `exp(it)`; the source's `Complex.exp_int_mul` rewrites the integer power to `exp(i ell t)`, so the integrand becomes `exp(i(ell−k)t)`. For `ell=k`, the integral of one is `2π` and the normalization returns one. For nonzero integer `ell−k`, the complex exponential has equal endpoint values over one full period; `integral_exp_mul_complex` and `Complex.exp_int_mul_two_pi_mul_I` give zero. This is the required Kronecker delta with no Fourier sign reversal or implicit normalized measure.

The theorem is a genuine step toward the reviewed base-symbol coefficient formula `a_(1−2r)=c_r`, but the base symbol is an infinite series. Its absolute/uniform convergence and legal interchange of the frozen interval integral with that series are not established by this module. Nor does the theorem itself prove exterior branch semantics or the all-order odd Toeplitz characteristic polynomial.

Pinned `lake build NLA.Proofs.SP14.BaseFourierMode` and a separate imported audit of the elaborated signature, `#assert_trust kernel`, and `#print axioms` passed under Lean 4.33.1. The theorem's transitive axioms are exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseFourierMode.lean`** | **`6744fba387ed60bbf05377478f20612f59a47fc5503f553e400dbce1d88cbbfe`** |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BASE_ACTUAL_TOEPLITZ_PRE_REVIEW.md` | `0760870797779a198c7fd16e4b1af8d06a398d9384ede2dc20c058a2881674e9` |
| `BASE_ACTUAL_TOEPLITZ_INDEPENDENT_PRE_REVIEW.md` | `19a06a06d0046bc9d7c333c84f5a115b91f798540d7e160633b973891cee9c21` |
| Independent `/private/tmp/sp14-basefouriermode-independent-audit.lean` | `bdc5b1ee77c22aac265fa83f1cce47613c2a182121cfe54c37608cd09e6acccb` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed source or approved contract bytes reopen this review.
