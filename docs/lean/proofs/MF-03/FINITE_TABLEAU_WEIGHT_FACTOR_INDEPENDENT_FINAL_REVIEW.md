# MF-03 finite tableau weight factorization: independent final review

**Independent mathematical/source reviewer:** `/root/sp14_base_proof`, 10 October 2026. **Imported signature/kernel auditor:** `/root`. **Verdict:** APPROVE the frozen finite factorization gate for aggregate import. It does not prove the weighted tail inequality or determinant/tableau identity.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauWeightFactor.lean` | `289d246e4772b1f67b76cd0db15f91ab3d4326636b73224baf306102913a2740` |
| Exact all-order Schur/Padé contract | `122a73c48b82f4468875045eb22ebb3383af682b915da2d7af83246f80ed0eed` |
| Separate imported audit `/private/tmp/mf03-finite-tableau-weight-factor-independent-audit.lean` | `fc519e383ee94e0992d7cb85f2874295834d67037253f296408a7dda0925e64b` |

The actual bottom tuple weight is `∏_{c:Fin j}cosineFactor(b_c+1)`, exactly matching the zero-based source label. Rectangular restriction preserves each cell `r,c<m`; the bottom tuple preserves each `c<j` under `j≤m`. Therefore the augmented tableau's existing product weight factors exactly through its injective rectangular-restriction/bottom-tuple map. The identities include `j=0`, `m=0`, empty products, and `N=0` without an implicit nonempty assumption.

The direct pinned Lean 4.33.1 build passed 8,716 jobs. A separate imported audit checked the exact weight definition and all three public theorem signatures, reran LeanCert kernel trust, and printed only `[propext, Classical.choice, Quot.sound]`. The source scan found no proof escape. Changed source bytes require a new review. The finite sum inequality and dual Jacobi–Trudi determinant bridge remain open.
