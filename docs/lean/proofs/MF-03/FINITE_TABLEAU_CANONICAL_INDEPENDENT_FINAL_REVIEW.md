# MF-03 canonical finite tableaux: independent final review

**Independent mathematical/source reviewer:** `/root/sp14_base_proof`, 10 October 2026. **Imported signature/kernel auditor:** `/root`. **Verdict:** APPROVE the frozen finite tableau positivity lemmas for aggregate import. This is the canonical witness described in the independently reviewed all-order Schur–Padé contract, not a determinant identity or the full target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauCanonical.lean` | `0049d1f97e3e5d25962cafd667ca4e35137aa8ef6239bf08a9730ddc59aa33cb` |
| All-order exact mathematical contract `SCHUR_PADE_ALL_ORDER_PRE_REVIEW.md` | `122a73c48b82f4468875045eb22ebb3383af682b915da2d7af83246f80ed0eed` |
| Separate imported audit `/private/tmp/mf03-finite-tableau-canonical-independent-audit.lean` | `b0a4d833a0d50c5fbecfce7d3b866deba4d86c46e56e91518e1eb503ce70d0fd` |

The reviewer checked the original source and Lean definitions. The row-constant tableau labels row `r` by `r`, which is weakly increasing across rows and strictly increasing down columns. Rectangle shape `(m^m)` has rows `r<m`, so its entries are `<N` when `m≤N`. Augmented shape `(m^m,j)` has rows `r≤m`, so its entries are `<N` when `m<N`; the hypothesis `j≤m` retains the intended Young diagram. Every cell factor `cosineFactor(k+1)` is strictly positive, hence both canonical tableau weights are positive. The finite sums over all bounded tableaux are therefore strictly positive, including the empty rectangle when `m=N=0` and the `j=0` augmented case.

The exact public conclusions are `0 < finiteRectTableauSum N m` under `m≤N` and `0 < finiteAugTableauSum N m j` under `j≤m` and `m<N`. They are statements about **finite weighted tableau sums**. Their transfer to the elementary-coefficient determinants awaits the dual Jacobi–Trudi identity. The independently checked source changes no frozen MF-03 Target, canonical README, or permanent ID.

The direct pinned Lean 4.33.1 module build passed 8,718 jobs. A separate imported audit checked the four public declarations, reran LeanCert kernel trust on both positivity theorems, and printed only `[propext, Classical.choice, Quot.sound]`. The source scan found no proof escape. Changed source bytes require a new review.
