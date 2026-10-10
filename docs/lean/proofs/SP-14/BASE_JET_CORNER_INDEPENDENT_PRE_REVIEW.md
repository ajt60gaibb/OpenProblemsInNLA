# SP-14 selected-block cofactor: independent mathematical pre-review

**Verdict: approved as a generic finite-matrix identity.** This is a mathematical review of the frozen contract, before root's separate source and LeanCert audit. It does not approve a proof of the actual Toeplitz jet formula or SP-14 Target.

## Source lock

| Source | SHA-256 |
| --- | --- |
| Reviewed `BASE_JET_CORNER_PRE_REVIEW.md` | `959d50629c5f5d4e99bae58972f28d7db5da9f3810627cf0afdb3e959b4ac561` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Frozen candidate `BaseJetCorner.lean` (identified only; not audited here) | `4e9d3861ed43fe36db4065dc91370635a1a26c1faa99a52a8b84b5511c659f6c` |
| Frozen `BaseProductBlock.lean` / `BaseCB.lean` definitions | `dcf88c97cc5fc28466a12220c8849352d4f996ace066a7b98afc1aa502a361b8` / `4d08f355b18258aaee4a2a2a7c7546ffee8b13c81d746a8582aea105c7509e79` |

## Identity check

For `L=m+1`, `B=G.submatrix id Fin.succ` has entry `Bₖⱼ=Gₖ,ⱼ₊₁`, while `C=G.submatrix Fin.castSucc id` has entry `Cᵢₖ=Gᵢₖ`. Therefore `(CB)ᵢⱼ=∑_{k=0}^{m}GᵢₖGₖ,ⱼ₊₁=(G²)ᵢ,ⱼ₊₁`. The frozen `baseUpperShift` is one precisely at `(i,i+1)`, so deleting the **last row and first column** of `G²−(t+1)U` gives `CB−(t+1)I_m` exactly. This agrees with the source's `G²−w²U` when `t=w²−1`.

Adjugate entry `(0,m)` is the cofactor with row `m` and column `0` deleted. Its sign is `(-1)^m`; changing `CB−(t+1)I_m` to `(t+1)I_m−CB` contributes another `(-1)^m`. Their product is `+1`, giving precisely `charpoly(CB).eval(t+1)` with no invertibility or triangularity premise. At `m=0` both sides are `1`, including singular `G`; at `m=1` both sides are `t+1−(G²)₀₁`. I also checked five rational `t` evaluations for arbitrary rational `G` at each of `m=0,1,2`; all 15 match.

The contract keeps the actual Fourier coefficient and Toeplitz identification for a later theorem. The generic identity does not imply `det(H(t))=1`, the base jet polynomial, the real right inverse, perturbed-background persistence, or the frozen negative Target. The candidate Lean source was **not** inspected or kernel-audited in this review; root's final review remains the integration gate.
