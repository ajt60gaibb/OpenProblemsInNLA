# Independent exact-code review: spectral measurability

Reviewer: /root/independent_math_review. Approved the entire frozen
NLA/IE06/SpectralMeasurability.lean, SHA-256
`9bd335100a99efec4050c6dec606c03839562c2caacf33b4814db486a43302b1`.
The statements match the intrinsic-event requirements in the independently
approved selected-block-extension contract. No mathematical issue was found.

The singular-value Lipschitz proof intersects A's leading (i+1)-dimensional
Gram eigenspace with B's trailing (dimension-i)-dimensional eigenspace. Their
sum of dimensions exceeds the common input dimension, so the nonzero vector
has both required norm bounds. The operator-norm difference and triangle
inequality then give sigma_i(A)<=sigma_i(B)+norm(A-B), and reversing A,B
proves Lipschitz constant one. Indices outside the input dimension use the
actual zero extension. The same intersection argument proves monotonicity
under pointwise norm domination, with arbitrary finite-dimensional codomains.
These are genuine min-max consequences rather than assumed continuity.

The coordinate-to-Euclidean-map conversion is a linear map on a finite-dimensional
matrix space, hence continuous. Composition proves intrinsic singular-value
continuity and measurability, with the canonical finite product Borel space;
operator and Frobenius measurability are likewise literal. gramInverse is the
total rational formula A^T(AA^T)^-1, and its equality to the genuine spectral
pseudoinverse is asserted only for surjective A. This distinction is correct
on singular row Grams. Surjectivity is exactly nonvanishing row-Gram determinant;
the reverse implication uses the proved actual pseudoinverse right inverse.
The row-bijection singular-value equality uses exact Euclidean norm equality,
not an unproved SVD-basis transformation. All empty-dimensional cases retain
literal meanings. No measurable singular-vector or frame choice is asserted.

Independently recompiled the unchanged source with pinned Lean 4.33.1 in a
private build using existing pinned dependency caches. All 18 local kernel
assertions, including both local measurable/Borel instances, passed. Every
printed declaration has only propext, Classical.choice and Quot.sound, and
there were no warnings. Source hash was checked before and after compilation.
Receipt and log are in reviews/spectral-measurability-independent/. This is
not a fresh dependency rebuild or replay of cached dependency proofs. The
reviewer made no source edits.
