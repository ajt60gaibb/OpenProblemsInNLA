# SP-14 conditional actual Toeplitz characteristic polynomial: independent pre-proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE the frozen `BASE_TOEPLITZ_CHARPOLY_CONDITIONAL_PRE_REVIEW.md` contract for Lean implementation. Its public theorem has the exact all-`m` polynomial conclusion for the **frozen integral-defined** Toeplitz section, under the explicit `BaseFourierPattern a` hypothesis. This is conditional and does not establish the analytic pattern for the base symbol or the final counterexample.

The proposed signature retains `a : Circle → ℂ`, every `m : ℕ` including zero, and the same exact Fourier-pattern hypothesis used by the reviewed parity-block theorem. The conclusion is `(Toeplitz a (2*m+1)).charpoly = X*(X²−1)^m`; it is not a statement about an auxiliary matrix or merely nonzero eigenvalues. The parity equivalence is bijective, so characteristic-polynomial invariance transfers the actual matrix to the reviewed `[[0,B],[C,0]]` block matrix without a multiplicity assumption. The generic block theorem gives `X·(charpoly(CB)).comp(X²)` with the correct `C*B` orientation. The certified `CB=baseBlock` and `charpoly(baseBlock)=(X−1)^m` imply, by composition preserving multiplication and constants, `((X−1)^m).comp(X²)=(X²−1)^m`. No division by `X` occurs.

At `m=0`, the Fourier-pattern hypothesis makes the sole Toeplitz entry `a₀` zero and the formula becomes `X`. At `m=1`, `CB=[1]`, yielding `X(X²−1)=X³−X`. These endpoint checks match the original base-symbol identity. The cited finite and Toeplitz sources are already independently reviewed and kernel checked, but this pre-review is not a Lean proof of their composition.

The condition `BaseFourierPattern a` is substantive: proving it for the exact exterior-branch circle series still requires the analytic Fourier integral and termwise convergence argument. The base symbol itself has an outer annular extension. This assembly theorem cannot supply the two-sided nonextension, compactly supported test, or subsequence gap required by the frozen negative `SP14.Target`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`BASE_TOEPLITZ_CHARPOLY_CONDITIONAL_PRE_REVIEW.md`** | **`34e2e4cc1699748eabf86589b8ad6de09434d8c8a28fb00fb8c038cd234e5d2c`** |
| `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BaseParityBlocks.lean` | `06ef7ef23d4ea068188c011c680c2c4a43ee8ef6d8a0a8c23dfbac943dc4c5f2` |
| `BaseOffdiagonalCharpoly.lean` | `c503becdb5f9c1cae1da8724c744ebbdf3937316e5536702eaac865de3b88e33` |
| `BaseCB.lean` | `4d08f355b18258aaee4a2a2a7c7546ffee8b13c81d746a8582aea105c7509e79` |
| `BaseBlockCharpoly.lean` | `603dcc3f95f21c6d3c7646b47f1d280996a81ff95e813d82c31541ef9d10db7f` |
| Cited `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |

Changed contract or source bytes reopen this review.
