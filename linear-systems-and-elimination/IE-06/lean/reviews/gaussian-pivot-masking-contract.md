# Zero-masked pivot candidate: exact F5 contract

Fix n,m with m <= n-|S|, where S is a fixed finite set of original row labels in Fin n. Let zeroMasked(S,A) replace every original row in S by zero and retain every other entry exactly. All statements use the existing square, padded, totalized firstTrajectory and firstPath; no rectangular GEPP or altered pivot rule is introduced.

The first bounded deterministic claims are:

1. For any current-to-original label permutation L, masking the rows labeled in S commutes with one literal Schur step whenever the prescribed pivot's original label lies outside S. No nonzero-pivot premise is needed for this algebraic identity because ordinary real division is totalized.
2. If the actual first m selected original labels of A avoid S and each of those actual pivots is nonzero, the first m canonical pivot positions of zeroMasked(S,A) and A agree exactly. Their original-label embeddings therefore agree. Prove this by maintaining the exact state identity: the masked trajectory equals the original trajectory with rows whose current original labels belong to S set to zero. The positive original pivot magnitude prevents a zeroed row from tying or exceeding it; the frozen least-current-index tie rule is preserved among surviving rows.
3. The mask is Borel measurable and depends only on the outside-S rows. The original-label pivot embedding on the masked matrix inherits both properties. No nonsingularity claim is made for this masked square matrix.

For a total candidate that always lies outside S, fix a deterministic injection pi0:Fin m into the subtype of labels outside S; the cardinality hypothesis supplies one, independent of A. If all first m masked selected labels avoid S, use that embedding restricted to the outside-S subtype; otherwise use pi0. This fallback candidate is always an injection into S-complement, is measurable coordinate by coordinate, and depends only on outside-S input entries. On the event in item 2 the fallback is not used and its original labels equal the original actual pivot prefix.

Zero m and empty S are included. On arbitrary degenerate outside data the raw masked prefix may select a zeroed row after a zero pivot; the fallback explicitly handles this. The task does not assume independent random pivots, Gaussian conditional laws, random rank, or square nonsingularity of a masked matrix. These deterministic selector facts will support a later Gaussian conditioning step in B4, which is separate.

Preimplementation review: root proposed the masking consistency route; source_statement_author independently approved it and identified the zero-pivot guard. Root then explicitly approved the stated deterministic fallback variant before implementation. The implementation author is source_statement_author; the final exact source will receive separate review.
