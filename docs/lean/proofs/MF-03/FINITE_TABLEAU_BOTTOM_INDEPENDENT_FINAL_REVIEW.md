# MF-03 finite tableau bottom entry: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this narrow combinatorial gate for aggregate import. It does not prove the weighted tableau tail inequality, determinant identity, Padé denominator bounds, or all-order MF-03 Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauTail.lean` | `245226b8e05f0aaa15d41a491ec74825a624db02a68a68e6f0741321ef49307d` |
| Exact all-order Schur/Padé contract | `122a73c48b82f4468875045eb22ebb3383af682b915da2d7af83246f80ed0eed` |
| Separate imported audit `/private/tmp/mf03-finite-tableau-tail-independent-audit.lean` | `bf777d026ba7e46822978687ea4b42abd5b6e6bcb5d8c432555e5e7242cc7336` |

The finite shapes are exactly the `m×m` rectangle and that rectangle with one bottom row of length `min j m`. The subtype `FiniteTableau μ N` bounds **every cell label** by `N`, and the source constructs a finite instance by embedding its cell entries into `μ.cells→Fin N`. The rectangular restriction preserves semistandard row, column, zero-outside, and label-bound conditions. For `j≤m`, the extracted extra row is an actual `Fin j→Fin N` tuple.

The mathematical lower bound is exact: strict increase down each column from row zero forces a label in row `r` to be at least `r`. Hence each added bottom-row label is at least `m`, matching the approved zero-based tail start `k=m`. The proof handles empty shapes and `j=0`; it makes no positivity or determinant claim.

The direct pinned Lean 4.33.1 build passed 8,714 jobs. A separate imported audit checked the shape, finite subtype, restriction, tuple, and bottom bound signatures and reran LeanCert kernel trust. It reported only `[propext, Classical.choice, Quot.sound]`. Source scans found no proof escape. Changed source bytes require a new review.
