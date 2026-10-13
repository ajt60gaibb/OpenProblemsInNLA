# MF-03 finite augmented determinant/tableau identity: independent final review

**Verdict:** APPROVED as the exact original finite determinant/tableau
identity. The frozen source
`lean-statements/NLA/Proofs/MF03/FiniteAugDetTableau.lean` has SHA-256
`0f39a4f2d091ceee4b3e2f9b3a90aa9217d5bf530202dbb65952f91d1dc60466`.
The independent mathematical pre-review of
`FINITE_WEIGHTED_TABLEAU_TRANSPORT_PRE_REVIEW.md` approved this exact final
finite identity at contract SHA-256
`8aa1a84c3925ebd46e4bcbd9c8bad0a2ff961f3fa8543a111b1c6a24a8600241`.

The public theorem directly composes the separately audited original
`finiteCosineAugDet_eq_validPathSum` and
`finiteValidPathSum_eq_augTableauSum`. Its left side is the original finite
augmented determinant with the first `j` rows shifted, and its right side is
the original bounded augmented-tableau sum with exactly the existing upper
and bottom weights. It quantifies all `N,m,j : ℕ` with only `j≤m`; no size,
nonempty, positivity, or nonzero assumption has been added. Thus empty
determinants, empty tableau domains, `j=0`, and `j=m` remain in scope.

The independent imported exact-signature audit is
`/private/tmp/mf03-finite-aug-det-tableau-independent-audit.lean`, SHA-256
`a163714474a4248aa4449eec0e195dfa974b85ce89854cc09468d3d025dbcd05`.
Pinned Lean 4.33.1 `lake build NLA.Proofs.MF03.FiniteAugDetTableau` passed
8,752 jobs; separate `lake env lean` passed the original exact signature and
`#assert_trust kernel`. The theorem's axioms are precisely `[propext,
Classical.choice, Quot.sound]`. No `sorry`, `admit`, `native_decide`, unsafe
declaration, or new axiom appears in the frozen source.

The finite equality is now proved. Positivity, the infinite determinant
limit, and the full MF-03 Target remain separate obligations.
