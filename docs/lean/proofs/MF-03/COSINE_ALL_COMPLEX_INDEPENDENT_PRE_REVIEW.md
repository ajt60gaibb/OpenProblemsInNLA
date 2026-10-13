# MF-03 all-complex cosine product: independent pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen exact contract for implementation. It removes the dense-set hypothesis from the product value identity but does not prove the all-order Padé target.

| Reviewed input | SHA-256 |
| --- | --- |
| `COSINE_ALL_COMPLEX_PRE_REVIEW.md` | `18e82a78f3c77a1cbc6c7d55f0c437cb44832cdd04698c287d402cf942695fcc` |
| Canonical `MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| Frozen `NLA.Statements.MF03` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| Audited dense-set source | `0190869c463e7b06c1ced4beec8fdfd1b68481e60a688ff472b27a368e20be28` |

The proposed infinite product has exactly the frozen factors `1+a_kz` for `k≥0`, with `a_k=1/[π²(k+1/2)²]` and no zero-index denominator factor. At `z=−(πw)²` each factor is `1−4w²/(2k+1)²`; the first is `1−4w²`. The reviewed coefficient summability gives `Σ a_k<∞`. For fixed `z₀`, the exact neighborhood bound `‖z‖≤‖z₀‖+1` majorizes every perturbation by the summable sequence `(‖z₀‖+1)a_k`. The pinned dominated-convergence theorem for `tprod (1+f)` therefore proves continuity of the product even at product zeros. This uses no division by vanishing factors.

The complex sine zero set of `sin(πw)` is exactly the integer casts, since `π≠0`; its complement is dense because this countable set has empty interior in `ℂ`. On that complement, the audited dense-set limit and the pinned `HasProd.tendsto_prod_nat` are limits of the same finite product, hence equal. Both sides of `T(−(πw)²)=waveSeries(−(πw)²)` are continuous in `w`, so equality extends to every integer point as well. The quadratic map `w↦−(πw)²` is surjective over `ℂ`: choose `y²=−z` and divide by nonzero `π`. This yields both proposed all-complex statements. At `z=0`, the empty and infinite products and `waveSeries` have value one; no rounded constant enters the proof.

Implementation must show the pointwise majorant uniformly for all factor indices, establish the exact dense set, use Hausdorff uniqueness and continuity, and preserve the all-complex quantifier with no sine premise. The resulting value identity does not supply elementary-symmetric coefficient transfer, normalized Padé existence, or the frozen Target. Keep source unimported until a separate source/signature/LeanCert audit.
