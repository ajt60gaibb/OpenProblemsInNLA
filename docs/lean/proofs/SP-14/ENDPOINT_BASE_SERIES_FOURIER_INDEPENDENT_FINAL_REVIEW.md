# SP-14 endpoint base series and Fourier integral: independent final review

**Independent mathematical/source/kernel reviewer:** `/root`, 10 October 2026. **Proof author:** `/root/sp14_base_proof`. **Verdict:** APPROVE the frozen endpoint-series and all-integer Fourier integral modules for aggregate import. The finite inverse monomial and endpoint-extension kernel remain separate.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/EndpointBaseSeries.lean` | `69ecc4eb22321a753dbc4dd69a358734ff12ee79a9ac4a2a04cd63da2bc562cd` |
| `lean-statements/NLA/Proofs/SP14/EndpointBaseFourier.lean` | `2799b3964d3f5173b7d9e2babffde3e8e46ccfb9f0ba14894e7b08864cdb62c5` |
| Exact mathematical/numerical contract `ENDPOINT_EXTENSION_KERNEL_PRE_REVIEW.md` | `02c6e68d49e4ec2fefed5a58dd81ae1a1f48ad388c0ec5025df6090cb06b8c03` |
| Independent pre-review `ENDPOINT_EXTENSION_KERNEL_INDEPENDENT_PRE_REVIEW.md` | `8277cfa7aeaf1f94a6d3576e890f6baed2307a951ca73afdd6891b14c4b87a03` |
| Separate imported audit `/private/tmp/sp14-endpoint-base-series-fourier-independent-audit.lean` | `37ab2f7ab8d9805fbd0a2548ba2087b1d928c65b3cb476a2aa28170e831c62a4` |

The definition is the **actual endpoint** `g₀(z)=∑'_{n≥0} baseCoeff(n) z^{-n}` on `Circle`, distinct from the previously proved odd-frequency exterior symbol. The reviewed absolute coefficient summability gives absolute convergence at every circle point and uniform continuity, including `z=-1`. The second module applies the frozen `FourierCoefficient` interval integral with its `1/(2π)` normalization. Its compact-interval uniform norm bound justifies termwise integration, and the previously reviewed circle-mode theorem yields, for **every** integer `k`,

```text
FourierCoefficient endpointBaseSymbol k
  = ∑' n:ℕ, baseCoeff n * (if -(n:ℤ)=k then 1 else 0).
```

The exact exponent `−n`, sign, and all-integer index were reconstructed in a separate imported audit, which also checked the public series/summability/continuity signatures. Direct pinned Lean 4.33.1 builds passed; the imported LeanCert audit passed and printed only `[propext, Classical.choice, Quot.sound]`. A source scan found no proof escape. The finite `V_k`, its Fourier convolution, the signed negative-frequency kernel, analytic operator estimates, and the frozen SP-14 Target remain open. Changed source bytes require a new review.
