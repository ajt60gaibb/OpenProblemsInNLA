# Implementation of the exact deterministic stacking bound

Author: `/root/independent_math_review`. The contract was independently approved
before implementation in `../spectral-stacking-specification.md`.

The final theorem is `NLA.IE06.SpectralStacking.spectral_stacking`. It uses the
actual Euclidean maps and true CFC pseudoinverse from `Spectral.lean`. All source
one-based singular indices are translated by subtracting one under the explicit
index guards; the positive denominator is retained. No source estimate or
additional good-subspace/right-inverse hypothesis remains in the final theorem.

The proof constructs the image of the leading forward Gram subspace of BQ,
then intersects it with the orthogonal complement of the image under BM† of
the complementary trailing Gram subspace. Finite-dimensional intersection
counting retains at least k−2j dimensions. Cauchy–Schwarz converts the forward
subspace estimates to the required adjoint lower and upper bounds. This avoids
assuming equality of forward and adjoint singular-value sequences.

A positive adjoint lower bound constructs a genuine linear right inverse via
the inverse of TT†, and proves its reciprocal norm estimate. Correcting M†a
by a kernel-basis contribution solves the reduced stacked system. The image
of this correction map has the required dimension. Its norm bound uses the
actual two row-block norms, each bounded by the full Euclidean stacked norm.
Forward Courant–Fischer then proves exactly the original stacking inequality.

`receipt.json` binds the final module hash and `compile.log` records all 14
explicit kernel trust checks and printed axiom closures. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. Compilation has no warnings. This
receipt uses the pinned local dependency caches; it does not claim a fresh
kernel reconstruction of those caches. The two adopted min–max dependencies
have separate provenance, full declaration audits and independent rebuilds.
