# PF-05 signed-quartic supporting source review

Reviewed by `/root`, a Codex AI agent independent of the four module author,
18 October 2026. This is complete source inspection and mathematical review
of the four exact frozen files below. Fresh kernel/axiom evidence is supplied
separately by the independent verifier; this report does not claim an additional
fresh build. These supporting statements do not yet prove the full PF-05 Target.

The signed-polynomial lemma repairs precisely the finite nodes where the actual
nonzero weakly signed polynomial vanishes. Injectivity makes their number at
most the actual degree. Actual Lagrange interpolation at those nodes has degree
within the same bound. A common positive perturbation preserves every already
strict inequality by continuity and changes each zero-node signed value to a
positive multiple of the square of its nonzero sign. The empty index case is
handled separately; the nonempty case proves the resulting polynomial nonzero.
No polynomial-root or interpolation oracle is assumed.

The contact formulas use the actual (a,c,b) row and (d,f,2e) dual coordinates.
The first determinant derivative on the primal chart is the displayed quartic;
the derivative of the NEGATIVE dual action on its trace-orthogonal chart is its
negative. This sign and the off-diagonal factor two are essential and correct.
The explicit coefficient matrix realizes every polynomial of degree at most
four. Actual first-order trace cancellation and factor rescaling are proved.
A symmetric matrix orthogonal to a nonzero PSD matrix has nonpositive determinant:
if positive, its nonzero trace selects either it or its negative as PSD; zero
trace pairing forces a singular product, contradicting its determinant.

StrictPSD derives genuine straight PSD segments, including t=0, from strict
inward determinant derivatives at actual singular nonzero factors. Positive
trace persists by continuity; at singular factors the exact determinant
polynomial is t times a function positive near zero. Nonsingular factors have
positive determinant near zero. Finite intersection yields one interval for
both actual families, and the actual coordinate identity gives first-order
trace equations. Actual rank-three row spans force every common scalar primal
action to have zero contact polynomial; no extra operator-injectivity premise
is supplied.

The homogeneous bridge retains the projective point omitted by the affine
chart. Its image determinant is the fourth coefficient, which vanishes when
the actual polynomial is zero. For v0 nonzero, the exact outer-product scaling
by v0 squared proves the result in the affine chart. Thus no direction at
infinity, singular factor, or boundary contact is discarded.

Approved scope: the exact supporting statements in these files. Actual contact
selection, distinctness after ray compression, finite common chart, full positive
forward assembly, canonical proof package and Linux evidence remain separate
obligations. No source changes were made during this review.

| File | SHA-256 |
|---|---|
| `PolynomialStrictification.lean` | `fe432727f9faeb504b66bfa3fa141e4f49b6e5d3341c9a9185aeac01c351b305` |
| `ContactQuartic.lean` | `f1b6fdf69cbd305fe5f75716cf08e5771e6ac8945db10d952f947467d687f968` |
| `StrictPSD.lean` | `e6d6bc3057e55eb83cd97c8adaa109bab5c5e9b8f7a84fd2ebaeea862631a750` |
| `HomogeneousQuartic.lean` | `939be750d6d85381b55ca480534745e07a5d1aeb59f137f2fb7a26e5678acdad` |
