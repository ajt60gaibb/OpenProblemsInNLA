# MF-03 finite tableau restriction pair: independent final review

**Independent mathematical/source reviewer:** `/root/sp14_base_proof`, 10 October 2026. **Imported signature/kernel auditor:** `/root`. **Verdict:** APPROVE the frozen injectivity gate for aggregate import. It does not claim a weighted tail or determinant identity.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauPair.lean` | `6e667d781e7d218921771369b4fac7125fae3878875290bd79f4e282a7152d52` |
| Exact all-order Schur/Padé contract | `122a73c48b82f4468875045eb22ebb3383af682b915da2d7af83246f80ed0eed` |
| Separate imported audit `/private/tmp/mf03-finite-tableau-pair-independent-audit.lean` | `13e0f07a65d18ee7b1fdbebc8b342413af3e48d65fb2aac93e8d32ffdcc88bee` |

The actual augmented shape is the `m×m` rectangle plus row `m`, columns `c<min j m`; under `j≤m`, every bottom cell appears in the extracted `Fin j→Fin N` tuple. Equality of rectangular restrictions gives each rectangular cell entry, equality of bottom tuples gives every added-row entry, and the semistandard tableau zero-outside law gives all other entries. Thus the restriction-pair map is injective for all `N,m,j` with `j≤m`, including empty shapes. The source has no weak-row counting or weight assertion.

The pinned Lean 4.33.1 direct build passed 8,715 jobs. The separate imported audit checked the exact map and injectivity theorem signatures, reran LeanCert kernel trust, and printed only `[propext, Classical.choice, Quot.sound]`. The reviewer saw no proof escape; the auditor's source scan concurred. Changed source bytes require a new review. The finite weighted tableau inequality and dual Jacobi–Trudi determinant identity remain open.
