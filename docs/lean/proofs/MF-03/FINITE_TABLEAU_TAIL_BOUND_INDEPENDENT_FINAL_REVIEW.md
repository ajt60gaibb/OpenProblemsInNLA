# MF-03 finite tableau tail bound: independent final review

**Independent mathematical/source reviewer:** `/root/sp14_base_proof`, 10 October 2026. **Imported signature/kernel auditor:** `/root`. **Verdict:** APPROVE the frozen finite weighted-tableau upper bound for aggregate import. It remains a tableau-sum theorem until the dual Jacobi–Trudi determinant identity is proved.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/MF03/FiniteTableauTailBound.lean` | `957fc6c69e5c778900a49fdae04d61f9a99dd5ef28fdadd48b75a2b01749a2a3` |
| Exact finite-tail contract | `f48f745928a55c8421f11c80d714ba3ee6430825215da09a49fc3543b8dbed7f` |
| Independent mathematical pre-review `FINITE_TABLEAU_TAIL_PAIR_INDEPENDENT_PRE_REVIEW.md` | `5d4fe39ad042e9e3bdfd22184dffc3a60ae3727f87ac1acc88800b3eba1dc229` |
| Separate imported audit `/private/tmp/mf03-finite-tableau-tail-bound-independent-audit.lean` | `6a9e7460b5f96da708da9c261181d5e45eca338e7460578baffc213481a81229` |

The source defines `FiniteTailLabel N m={k:Fin N // m≤k.val}` and the exact zero-based finite factor tail `finiteCosineTail N m=Σ_{m≤k<N}cosineFactor(k+1)`. The bottom-label theorem refines the reviewed injective restriction-plus-bottom map to a rectangular tableau paired with an ordered tuple of tail labels. Forgetting the label-bound subtype recovers the prior injective map. The reviewed weight factorization identifies each augmented tableau's exact product weight with its pair weight.

Every factor `cosineFactor(k+1)` is positive. Thus each pair weight is nonnegative, allowing the source to enlarge the finite sum from the injective image to every rectangular tableau and every ordered tail tuple. The product-type sum separates, and `Fintype.sum_pow` evaluates the tuple sum exactly as `finiteCosineTail N m ^ j`. The public theorem is precisely `finiteAugTableauSum N m j ≤ finiteRectTableauSum N m * finiteCosineTail N m ^ j` for every `j≤m`, including zero and empty cases. It uses no finite-order numerical certificate.

The direct pinned Lean 4.33.1 module build passed 8,717 jobs. A separate imported audit checked the public tail definitions and exact theorem signature, reran LeanCert kernel trust, and printed only `[propext, Classical.choice, Quot.sound]`. The source scan found no proof escape. Changed source bytes require a new review. The finite tail-to-infinite tail inequality, positivity of canonical tableau sums, determinant/tableau identities, all-order Padé pair existence, and full MF-03 Target remain open.
