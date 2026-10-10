# MF-03 finite bidiagonal minor: independent final review

**Source author:** `/root/mf03_jt_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the exact finite minor gate for aggregate import. The determinant/tableau identity and frozen MF-03 Target remain open.

The exact mathematics and indices were independently approved before implementation in `FINITE_BIDIAGONAL_MINOR_INDEPENDENT_PRE_REVIEW.md`, against the author contract SHA-256 `afc21ffbc1fe1f02af76aafa0fbd5f9edf5c47a297eb44f26707b572bd6c0fbe`. The frozen source `lean-statements/NLA/Proofs/MF03/FiniteBidiagonalMinor.lean` is SHA-256 `8f97605566f879da87fb06c634ecc3b151c61f97cdb79c568d8f9ca6f295e44a`.

I read the complete source. `finiteBidiagonal m k` has literal diagonal `1`, superdiagonal `cosineFactor(k+1)`, and zero elsewhere. The recursive product is `B_(N−1)⋯B_0`. The source proves the finite elementary coefficient recurrence by splitting powerset-card subsets on membership of `N`, including degree zero. The public entry theorem retains the essential zero below the diagonal and exact finite elementary coefficient above it. `finiteMinorRow` omits index `j` and `finiteMinorCol` occupies `m+1,…,2m`; the augmented determinant is exactly that product minor for all `j≤m`, including `m=0`, and the rectangular specialization is at `j=0`. The source has no proof escapes or new axioms.

The pinned Lean 4.33.1 direct module build passed 8,716 jobs. I independently imported the frozen module in `/private/tmp/mf03-finite-bidiagonal-minor-independent-audit.lean` (SHA-256 `279a2dcbc78d8906f43fd4d3507b617fd413c2a9e2cd51ace125535c4589f892`) and checked exact definitions, entry theorem, both determinant identities and three `#assert_trust kernel` directives. `#print axioms` returned only `[propext, Classical.choice, Quot.sound]`. The aggregate build is recorded in PR verification after import.

Cauchy–Binet expansion, a weight-preserving path/tableau bijection, determinant positivity, all-order Padé pair existence and the full Target remain separate obligations.
