# Independent source review of the two character-bound supports

23 October 2026. Reviewer: campaign recovery/geometry agent. The reviewer did
not author either reviewed source. This is a mathematical source review bound
to the hashes below; it does not claim a separate fresh kernel build, Linux CI,
Comparator approval, or completion of the full intrinsic target.

| Source | SHA-256 |
| --- | --- |
| GraphProjectionCharacterBound.lean | 60a155829ea4c83cfd4d76c6a952c8e4aa8c7344a191e9b63e0151ea8cd4bfc5 |
| GraphProjectionOrderedBound.lean | 9cb27bec5644f321dfa890907c0179fc933edb9545e619aa7626eb5f3cada531 |

The review included both complete source bodies, the retained actual
`UniformQuasiFiniteCharacterBoundStatement`, and its implementation in
`NLA/TR06/QuasiFiniteCharacters.lean`. No mathematical blocker was found in
these two new supports.

The scalar actions are explicit and faithful to the intended projection. The
source action of the coordinate polynomial ring is induced by the actual
`MvPolynomial.aeval f`. For each projected value x, the target field action is
induced by evaluation at that same x. Equality on the coordinate generators
therefore proves equality of the two base actions on every polynomial. Each
original complex character lifts to a character over this actual base action.
The lift is injective by pointwise equality of the original characters, and
the finite image has exactly the original finite-set cardinality.

The source's finite type over the coordinate ring and its Noetherianity are
derived from finite type over the field of complex numbers. The retained
uniform quasi-finite character theorem chooses B before the varying target
base action; the new supports preserve that quantifier order. They do not
assume that a complete fiber is already finite. The indexed-family version
uses an explicitly finite index type and an injective family, avoiding any
infinite-set cardinality convention.

The row specialization uses the genuine linear combinations of the actual
algebraic graph coordinates. It preserves actual quasi-finiteness at the
actual kernel of each character. The ordered specialization uses the proved
actual graph-coordinate evaluation identities. Equality of characters implies
equality of every real input and normalized-output coordinate, since the real
embedding into the complex numbers is injective. Those coordinates separate
the genuine Hilbert product ambient. Distinct graph points thus yield distinct
characters even if their pivot parameters or decomposition representatives
are not intrinsically unique.

The ordered theorem retains the exact genuine projected derivative
injectivity premise. It derives quasi-finiteness through the already proved
point-derivation argument; it does not replace that premise with real setwise
local injectivity. All complex extraneous points and radius branches remain
in the algebraic source, which is valid for an upper bound on actual graph
points. The finite union over pivot patterns and the actual controlled atlas
remain separate geometric obligations.

The reviewer excludes all of their authored Model, AlgebraicLocus,
NormalizedGraphCharts, NormalizedGraphArea, selected-row/control bridges, and
retained boundary additions from this independent approval scope. A separate
independent verifier's fresh source replay supplies execution evidence for
the full assembled closure.
