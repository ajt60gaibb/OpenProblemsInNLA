# SP-14 exterior Fourier pattern and actual Toeplitz charpoly: independent Lean review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `BaseExteriorPattern.lean` for the unconditional Fourier pattern of the **normalized exterior base series** and the exact all-odd-order characteristic polynomial of its **frozen integral-defined Toeplitz sections**. This base symbol has an outer annular extension and is not the final counterexample; the full negative `SP14.Target` remains unproved.

The imported Fourier theorem already identifies every frozen coefficient with a `tsum` supported at frequencies `1−2n`, `n:ℕ`. The source proves all even coefficients vanish because an odd integer cannot equal `2p`. For an odd frequency `1−2p`, it splits **all** `p:ℤ`: when `p≥0`, exactly `n=p.toNat` contributes and the coefficient is `baseCoeff p.toNat`; when `p<0`, no natural `n` contributes and the coefficient is zero. This is exactly the previously reviewed `BaseFourierPattern`, including modes above `1` and all negative modes, with the frozen row-minus-column/Fourier sign convention. It does not replace the actual integral with a discrete transform.

The second theorem instantiates the independently reviewed conditional characteristic-polynomial bridge with this now-proved pattern. Its elaborated conclusion is

```lean
NLA.Proofs.SP14.baseExteriorSymbol_toeplitz_charpoly (m : ℕ) :
  (NLA.Statements.SP14.Toeplitz baseExteriorSymbol (2 * m + 1)).charpoly =
    Polynomial.X * (Polynomial.X ^ 2 - 1) ^ m
```

There is no Fourier hypothesis left on this base-symbol theorem, and it covers `m=0` as well as every larger odd section. It preserves characteristic-root algebraic multiplicity through the earlier polynomial identity. This theorem concerns the exterior **base** symbol alone; the packet modifications, two-sided nonextension, compactly supported test, and empirical subsequence gap required by the canonical negative answer remain separate.

Pinned `lake build NLA.Proofs.SP14.BaseExteriorPattern` and a separate imported LeanCert audit of both elaborated signatures, `#assert_trust kernel`, and transitive axioms exited successfully under Lean 4.33.1. Each theorem lists exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseExteriorPattern.lean`** | **`daf64cfcc02a7dd2aeab59403d1216046006daef2c7c7a987ac79ef22c40cdf4`** |
| `BaseExteriorFourier.lean` | `837c00dc8cd034ddb8d7bc9672ada2d3f5f5a454a6e864ddfa42cf140b0332fd` |
| `BaseToeplitzCharpolyConditional.lean` | `1d3f3c01161ad3ba6aaadcd2603ee6b042978f43a48e88a4962292df3e96476c` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BASE_EXTERIOR_SERIES_FOURIER_PRE_REVIEW.md` | `aed55ffe098560355c0f7dbeecdd313d42bf53ecd93bc1633c7f8299d459b67d` |
| Independent `/private/tmp/sp14-baseexteriorpattern-independent-audit.lean` | `9876ee7a4964925c118784a10f31865367c6456da47126dc10397fd38e90fb90` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed source or approved contract bytes reopen this review.
