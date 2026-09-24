# Elementary complexification and closed-fiber boundary

Author/implementer: /root/tr06_statement_referee_1 (AI agent). Date: 2026-09-24.
Root explicitly approved this bounded implementation before proofs. Frozen Definitions SHA256: e5fe5314f4c17df41b5bec54f2c407b2d1eba8ba59be5d85525de13e262f8898.

No changes to the frozen Definitions or Challenge. Complexification maps a real tensor coordinatewise into C. It preserves pureTensor, zero, addition, finite sums, nonzero rank-one status in the forward direction, and decompositions, and is injective. A supplied real length-r decomposition together with complex ExactRank r implies real ExactRank r; complex Identifiable r implies real Identifiable r. These do not assert a universal rank equality.

New definitions in ClosedFibers:

    rankAtMostOne (A : Tensor k d n) := A = 0 or RankOne A
    closedRankOneProduct k d n r :=
      {a : Fin r -> Tensor k d n | forall i, rankAtMostOne (a i)}
    closedAdditionFiber r A :=
      {a : Fin r -> Tensor k d n |
        a belongs to closedRankOneProduct k d n r and sum_i a_i = A}

For every RCLike field k, every d,n,r (including r=0), and A:

    ExactRank r A -> Identifiable r A ->
      (closedAdditionFiber r A).Finite and
      (closedAdditionFiber r A).Nonempty.

The supporting zero-removal lemma states that any closed rank-one length-r tuple a has a genuine nonzero rank-one decomposition of its sum of length m<=r, with m<r if some a_i=0. Construct it by indexing exactly the nonzero positions. Exact rank r therefore forces every tuple in the full closed fiber to have no zero summands. Fix one actual decomposition, use identifiability to place every closed-fiber tuple in its finite permutation orbit, and obtain nonemptiness from that fixed decomposition. Empty index types and zero sums remain covered by the definitions.

The final finite-fiber theorem concerns the FULL actual tuple fiber, not an already nonzero-restricted fiber, quotient by permutations, factor-vector gauge fiber, or chosen local chart. Nothing here proves the cone closedness, polynomial minors, an infinite shorter-rank fiber, generic finiteness, a regular locus, or full TR-06.

Before implementation, no boundary changes are needed. The supporting zero-removal signature uses an existential m instead of exposing a subtype-cardinal implementation, avoiding irrelevant decidability assumptions on tensors.
