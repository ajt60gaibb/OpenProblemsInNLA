# SP-14 endpoint extension negative-frequency kernel: independent final review

**Independent mathematical/source/kernel reviewer:** `/root`, 10 October 2026. **Proof author:** `/root/sp14_base_proof`. **Verdict:** APPROVE the frozen all-index negative-frequency endpoint extension theorem for aggregate import. The nonnegative projection and operator estimates remain separate.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/EndpointExtensionKernel.lean` | `2dd8c29d8d8ac936344e86ef37dcd794443113b3c4bf7c3f72268a8d8a59e83c` |
| Exact mathematical/numerical contract `ENDPOINT_EXTENSION_KERNEL_PRE_REVIEW.md` | `02c6e68d49e4ec2fefed5a58dd81ae1a1f48ad388c0ec5025df6090cb06b8c03` |
| Separate imported audit `/private/tmp/sp14-endpoint-extension-negative-kernel-independent-audit.lean` | `30de0e523d3d026224fb876f5c6d6699fc8f372925936220375269b0f68983c1` |

The source defines the exact finite triangular inverse monomial `V_k(z)=Σ_{l=0}^k b_l z^{k-l}` on the circle. It proves frozen-interval Fourier linearity, finite-sum interchange, and the mode-shift identity from `Circle.coe_exp`. The already reviewed endpoint-base Fourier theorem gives the mode `−(j+k−l)` coefficient `a_{j+k−l}`. Reversing the finite index with `Finset.sum_range_reflect` produces the exact scalar sum `Σ_{d=0}^k a_{d+j}b_{k-d}`. The reviewed all-index partial-convolution theorem then gives, for every `k≥0`, `j≥1`,

```text
FourierCoefficient (fun z => endpointBaseSymbol z * endpointInverseMonomial k z) (−j)
  = ((k+1/2)/(k+j)) baseInverseCoeff(k) baseInverseCoeff(j−1),
```

with the right side coerced from real to complex. The Fourier integral and `1/(2π)` normalization are the frozen statement's definitions; the endpoint symbol is the actual `g₀`, distinct from the odd-frequency exterior base. Direct pinned Lean 4.33.1 build passed. My separate imported audit reconstructed the exact public signature, ran LeanCert `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]`. The source scan found no proof escape. It does not yet prove the nonnegative Fourier projection, weighted Schur or Hilbert–Schmidt bounds, bounded extension, or frozen SP-14 Target. Changed source bytes require a new review.
