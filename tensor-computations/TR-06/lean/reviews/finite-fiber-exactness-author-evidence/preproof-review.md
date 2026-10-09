# Independent finite-fiber exactness pre-proof approval

Reviewer: root, nonauthor of implementation. APPROVE all six proposition definitions and concrete families at SHA256 `96b4045af8b02e01d235849609f523437ee84f30cfb0e2dc5f6614b2b5babc51` after complete source and plan review.

The split family allocates the first two entries to t*a0 and (1-t)*a0, shifts exactly the other m-1 entries, and pads all other positions with zero. Under m>0 and m<r this preserves the original sum for every scalar, including0 and1. First-entry equality identifies the scalar because a0 is genuinely nonzero. d>0 legitimately absorbs scalar multiples into one mode. The cancellation family supplies the missing zero-tensor case with two positions, and positive mode sizes make the actual all-ones pure tensor nonzero.

The first rank-bound lemma correctly removes all zero entries of an arbitrary nonempty closed fiber without positivity premises. The infinite-family statements concern actual tuple equality and Set.Infinite, never Nat.card conventions or factor-rescaling orbits. The final finiteness contradiction gives both clauses of frozen ExactRank and keeps explicit nonemptiness. The d>0, positive mode sizes, r>=2 restrictions correctly exclude the listed counterexamples and are implied by the original final format restrictions.

No identifiability, source genericity, regularity, or finite-fiber premise is derived by these statements alone. Their intended use is a later application of the actual algebraic localization result, whose finiteness and nonemptiness still need to be established at each good tensor. This is pre-proof approval, not a complete-problem verification.
