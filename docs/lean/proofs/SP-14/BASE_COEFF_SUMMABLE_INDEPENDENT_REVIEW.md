# SP-14 exterior half-binomial absolute summability: independent Lean review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `BaseCoeffSummable.lean` for the unconditional theorem `Summable (fun n : ℕ => ‖baseCoeff n‖)`. This is the exact coefficient-norm convergence needed by the approved exterior-series Fourier contract; it does not define the circle symbol, interchange an infinite series with the frozen Fourier integral, prove its Fourier pattern, or prove the SP-14 counterexample.

The source starts from the exact complex recurrence `(n+1)c_(n+1)=(1/2−n)c_n` for `c_n=Ring.choose (1/2:ℂ) n`. For `n≥1`, taking complex norms yields `(n+1)a_(n+1)=(n−1/2)a_n`, where `a_n=‖c_n‖≥0`. It establishes the separate endpoint values `a₀=1`, `a₁=1/2`; applying the `n≥1` norm recurrence at zero would be invalid. The induction proves

```text
Σ_{n=0}^{N−1} a_(n+1) = 1 − 2(N+1)a_(N+1) ≤ 1
```

for every `N`, including `N=0`. Adding `a₀` bounds every nonnegative partial sum by `2`, and `summable_of_sum_range_le` gives the exported conclusion. The finite telescope is exact and does not rely on an unproved decay asymptotic or a circular boundary-series value.

Pinned `lake build NLA.Proofs.SP14.BaseCoeffSummable` and a separate imported LeanCert audit of the elaborated signature, `#assert_trust kernel`, and transitive axioms exited successfully under Lean 4.33.1. The axiom list is exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseCoeffSummable.lean`** | **`1da659ff573ddee8d598d32150fec45f7ae5d5eb023c2a9277a0500547ad9892`** |
| Imported `lean-statements/NLA/Proofs/SP14/BaseCoefficient.lean` | `63dcd98bb3a45e77b2b0fd2644d444f9cfe866fb9dae5535d1b7cd1f73081bf4` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BASE_EXTERIOR_SERIES_FOURIER_PRE_REVIEW.md` | `aed55ffe098560355c0f7dbeecdd313d42bf53ecd93bc1633c7f8299d459b67d` |
| `BASE_EXTERIOR_SERIES_FOURIER_INDEPENDENT_PRE_REVIEW.md` | `b552251955b3030f59e7de5444504fd60bae4ec15bbdecf368da8273b533a800` |
| Independent `/private/tmp/sp14-basecoeffsummable-independent-audit.lean` | `9151038b03a99b307cfe5013d3a66ba437a04d79fd116c33a0054e338ade4589` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed source or contract bytes reopen this review. The next analytic obligation is the actual all-integer termwise Fourier-integral theorem for the normalized exterior series.
