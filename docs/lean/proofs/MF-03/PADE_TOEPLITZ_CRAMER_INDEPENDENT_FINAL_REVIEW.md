# MF-03 Toeplitz/Cramer system: independent final review

**Source author:** `/root`. **Independent source reviewer:** `/root/tr14_frob_review`, 10 October 2026. **Verdict:** APPROVE the exact conditional algebra gate. It does not assert a Padé pair or the frozen MF-03 Target.

The exact mathematical and numerical formulas were independently approved before implementation in `SCHUR_PADE_ALL_ORDER_INDEPENDENT_PRE_REVIEW.md` against the source contract SHA-256 `122a73c48b82f4468875045eb22ebb3383af682b915da2d7af83246f80ed0eed`. The frozen Lean source `lean-statements/NLA/Proofs/MF03/PadeToeplitzCramer.lean` has SHA-256 `059f68a79245756e5bb662dfb8cf373630c07a291396f1782d66d999f1f0f50f`.

The independent agent read the complete source and confirmed `T(r,c)=e_(m+r−c)` and `b(r)=−e_(m+r+1)` for zero-based `r,c:Fin m`, with natural subtraction genuine because `c≤m−1`. The imported `cosineRectDet` is exactly `det(Tᵀ)`; transposition has no sign. `Matrix.mulVec_cramer` gives `T·cramer(T,b)=det(T)·b` without assuming a nonzero determinant. The edge `m=0` is vacuous and `m=1` gives `T=e₁`, `b=−e₂`. The source has no proof escapes, custom axioms, unsafe code, or target alias.

The pinned Lean 4.33.1 direct module build passed 8,716 jobs. A separate imported exact-signature audit `/private/tmp/mf03-pade-toeplitz-cramer-independent-audit.lean` (SHA-256 `0bf50478b88f8ca2ca8d2b7b6a17d01f988f3e52baeec8519f10874b45a6938e`) checked both definitions, the determinant equality and the full Cramer vector equation, with `#assert_trust kernel` on both exports. `#print axioms` returned only `[propext, Classical.choice, Quot.sound]`. The aggregate build is recorded in PR verification after import.

This gate does not supply determinant positivity, individual signed Cramer coordinate ratios, a normalized Padé representation, coefficient bounds, or the full Target. Those remain separate obligations.
