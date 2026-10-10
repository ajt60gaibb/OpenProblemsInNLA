# MF-03 rectangular determinant positivity: independent pre-review

**Verdict:** APPROVED for the displayed fixed canonical-weight lower bound
and strict original determinant positivity in
`RECT_DETERMINANT_POSITIVITY_PRE_REVIEW.md`, SHA-256
`9d509faa59652af32f4440984583e6faa0ed675f7ec9caf6ea3250c78c4ab66c`.

I independently verified every source lock and the original definitions.
The audited `canonicalRectTableau N m (m≤N)` has label `r` in every actual
cell `(r,c)` of the `m×m` rectangle. Its original weight is therefore the
displayed product of `cosineFactor(r+1)`, independent of `N`. Each factor is
strictly positive, and for `m=0` the empty product is `1`.

The independently audited original finite determinant/tableau identity
turns `finiteCosineRectDet N m` into the sum of original nonnegative
tableau weights. The canonical tableau appears once when `m≤N`, proving
the proposed fixed lower bound for every such `N`, without numerical
enumeration or a new determinant. The existing fixed-size determinant
limit takes `N→∞`; since `m≤N` eventually, closedness of `≤` yields
`canonicalRectWeight m ≤ cosineRectDet m`. Combining this with the
strictly positive fixed product gives the strict original infinite
rectangular determinant positivity. Positivity of finite determinants
alone would be insufficient, and the proposed uniform bound supplies
the needed limit margin.

The proposed signatures preserve all `m`, including `m=0`, and add no
nonzero denominator assumption. A frozen Lean implementation still needs
independent imported exact-signature, LeanCert kernel, and axiom audits.
Coefficient ratios and the full MF-03 Target remain separate obligations.
