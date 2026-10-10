# MF-03 finite rectangular determinant/tableau: independent pre-review

**Verdict:** APPROVED for the displayed exact signature in
`FINITE_RECT_DETERMINANT_TABLEAU_PRE_REVIEW.md`, SHA-256
`215bef93c0daf9bc5f2709e2a1cb88ff5ec1b129d3dde04d72beb6e5816f7e43`.

I independently verified every source hash in the precontract. The original
finite rectangular determinant is the `j=0` augmented determinant by the
kernel-proved `finiteCosineAugDet_zero`. At `j=0`, the augmented Young
diagram has `rectCells m ∪ ∅`, so it is the original `finiteRectShape m`.
The original `finiteBottomWeight 0 m T` is the empty product `1`. Thus the
original augmented-tableau sum at `j=0` is the original
`finiteRectTableauSum N m`, with exactly the original `m×m` cell factors
`cosineFactor(T(r,c)+1)`.

The already audited all-size determinant/tableau theorem at `j=0` therefore
proves `finiteCosineRectDet N m = finiteRectTableauSum N m` for all `N,m`,
including empty tableaux and `m=0`. No extra positivity or nonzero premise,
new weight, auxiliary determinant, factor, or normalization is introduced.

This approves the mathematical/indexing contract before Lean
implementation. The frozen source still needs a separate imported exact
signature, LeanCert kernel, and axiom audit. Infinite limits and the full
MF-03 Target remain separate.
