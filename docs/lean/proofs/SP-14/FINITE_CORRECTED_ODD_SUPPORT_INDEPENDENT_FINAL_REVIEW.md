# SP-14 finite corrected symbols: independent odd-support Lean review

**Reviewer:** `/root` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `FiniteCorrectedOddSupport.lean` for continuity, exact odd Fourier support, and the resulting finite Toeplitz polynomial shape. It does not prove the frozen negative `SP14.Target`.

I read the complete source and compared all public declarations with the [approved mathematical contract](FINITE_CORRECTED_ODD_SUPPORT_INDEPENDENT_PRE_REVIEW.md). The base exterior symbol's even frozen integral coefficients vanish by the reviewed pattern theorem. `positivePacket τ m` has the two exact odd modes `2m+1` and `2m+3`. The restored negative packet is rewritten using the source's `negativeL`, `restoringK`, and `restoredD`: its raw modes are `1+2(d−m)` for `d<q`, and its restoring modes are `1−2(m+1+r)` for `0≤r≤m`. The proof applies the genuine `FourierCoefficient_circle_mode` identity to these finite sums, so every even frozen coefficient is zero for all parameters, including `m=0` and `q=0`.

The source proves continuity of the restored negative packet and checks the frozen integral's finite-sum additivity only with continuous summands, supplying interval-integrability before using `integral_add` or `integral_sub`. `finiteCorrectedSymbol` is precisely the base exterior symbol plus arbitrary dependent Fin-indexed finite families of the source positive and negative packets. It is continuous and has odd Fourier support; its `u=vCount=0` case is definitionally the base symbol, and the `q=0` negative packet is zero. The final theorem applies the separately reviewed generic odd-frequency result to the **actual** Toeplitz sections, yielding `X · oddJetPolynomial.comp(X²−1)` for every `m`. It does not assert any jet vanishing, select correction vectors, or construct the infinite final symbol.

I independently ran a separate **imported** LeanCert audit under pinned Lean 4.33.1. It elaborated the finite-symbol definition and all nine public theorem signatures, ran `#assert_trust kernel` on every theorem, and printed their transitive axioms. The audit exited 0; every theorem uses only `[propext, Classical.choice, Quot.sound]`. The source contains no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/FiniteCorrectedOddSupport.lean`** | **`4c0a61680ccabe1acab795701f9c248dc1060193ffea6a64a0c9e451391ee664`** |
| Approved `FINITE_CORRECTED_ODD_SUPPORT_PRE_REVIEW.md` | `2c2e5bce752864ca69d1ff9d29935131c86750a0c610e85b72df0fe234004b5d` |
| Independent mathematical pre-review | `7e9485af253a8167e0557dad1551caee8320eaeb584522cb46ee96bf398d693e` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Imported `/private/tmp/sp14-finiteodd-independent-audit.lean` | `144361a2e40b36e9d81fd1b300063652f39b6d7453ee61e28b5d1e2957fa9ea7` |

Changed source or contract bytes reopen this review.
