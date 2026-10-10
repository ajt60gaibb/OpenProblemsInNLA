# SP-14 base odd Toeplitz characteristic polynomial: independent pre-proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE the frozen `BASE_ODD_CHARPOLY_PRE_REVIEW.md` as an exact specification and valid all-order finite-algebra route. This precedes Lean implementation and is not a proof of the final SP-14 counterexample or `Target`.

The source defines `g₀(s)=√(1+s⁻¹)` on the **exterior** of the unit circle, with the branch analytic there, equal to one at infinity, and continuous on the circle. Its binomial series `Σ_{k≥0} binom(1/2,k)s⁻ᵏ` has that branch and absolutely summable coefficients on the boundary. The recurrence gives `c₀=1`, `c₁=1/2`, **`c₂=−1/8`**, and `c₃=1/16`. The square identity alone would leave a sign ambiguity, so the exterior normalization and the boundary series are necessary. The resulting circle symbol is `a₀(z)=z g₀(z²)=Σ_{k≥0}cₖz^(1−2k)`; it is continuous and has an outer annular extension. The proposed Lean `BaseSymbol` must be this actual function, including its branch value at the boundary points above `s=−1`.

With the frozen real-interval coefficient `(1/(2π))∫₀²π a₀(e^{it})e^(−iℓt)dt`, uniform absolute convergence and orthogonality give `a_(1−2k)=cₖ` and every other integer coefficient zero. The sign yields `a₁=1` below the diagonal, `a₋₁=1/2` above it, and `a₋₃=−1/8` on the third superdiagonal. For the row-minus-column `Toeplitz` definition, independently deriving the even/odd blocks gives exactly `Bᵢⱼ=c_(j+1−i)` and `Cᵢⱼ=c_(j−i)` with negative subscripts zero. The displayed order-three matrix is correct. Independent exact rational determinant calculations at `m=0,1,2,3` give respectively `w`, `w³−w`, `w⁵−2w³+w`, and `w⁷−3w⁵+3w³−w`; these support the signs but are not used in place of the general argument.

For all `m`, the upper triangular Toeplitz matrix `Gᵢⱼ=c_(j−i)` satisfies `G²=I+U` by the binomial coefficient convolution. Selecting `G`'s columns `1,…,m` for `B` and its rows `0,…,m−1` for `C` gives `CB=P(I+U)E`, whose entries are one on the diagonal and first **subdiagonal** and zero elsewhere. Hence `CB` is unit lower triangular. The odd block matrix's characteristic polynomial is the polynomial identity `w det(w²I_m−CB)=w(w²−1)^m`; this includes `w=0` and needs no eigenbasis or diagonalizability. At `m=0`, the empty determinant is one and the actual section is `[0]`. The final Lean theorem must use the frozen integral-defined `SP14.Toeplitz BaseSymbol`, not only an auxiliary coefficient matrix.

This base identity is consistent with the source manuscript's `G=√(I+U)`, `H=G²−U=I`, `M(t)=t^m` computation and with the canonical README's exact base characteristic polynomial. Since `a₀` has an outer extension, it does not meet the hypothesis of the original conjecture. The final symbol's packets, corrections, extension failures, and persistent multiplicities remain separate obligations.

| Reviewed input | SHA-256 |
| --- | --- |
| **`docs/lean/proofs/SP-14/BASE_ODD_CHARPOLY_PRE_REVIEW.md`** | **`2d065496f7d7a4e4abc84005b801ec3891c0089f57e28f849c79c858521c666a`** |
| Source `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Canonical `eigenvalues-and-inverse-problems/SP-14/README.md` | `9d0c6376080838ea50e8736cb4249276c06a528479fb9c9f565cc7747a485075` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |

This verdict covers the proposed exact target and route before proof source exists. Any change to that contract or the cited mathematical source reopens review.
