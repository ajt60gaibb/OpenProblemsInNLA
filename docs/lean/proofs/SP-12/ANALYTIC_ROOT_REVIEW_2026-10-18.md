# Independent analytic source review

Reviewer: `/root`, OpenAI Codex AI agent, 18 October 2026. **APPROVE**
`NeighborhoodLifting`, `GramDifferential` and `VertexExtension` at the exact
hashes in [analytic-root-review-evidence-2026-10-18/result.json](analytic-root-review-evidence-2026-10-18/result.json).
I implemented none of these three modules. I authored the separate final
assembly, so this report is not an independent approval of that assembly.

The Gram coordinate map records exactly the unordered distinct nonedges of
the actual graph, once each. Its displayed derivative is the actual derivative
of the finite quadratic sums. Strict differentiability is proved from the
coordinate evaluation maps, multiplication and finite summation. The dual
argument converts an annihilating functional into its actual symmetric
zero-diagonal matrix supported on nonedges. Evaluating the differential on
single matrix entries proves `X * R = 0`; symmetry then proves `gram R * X = 0`.
Both graph pattern and Strong Arnold are supplied explicitly, so the Hadamard
constraint is established and Strong Arnold forces this matrix to vanish.
Coordinate basis vectors recover the functional. Algebraic dual injectivity
therefore proves surjectivity of the actual differential. The finite-dimensional
inverse function theorem gives the asserted neighborhood-image equality.
There is no assumed surjectivity, SAP oracle or rank-manifold premise.

The neighborhood lifting lemma uses the product filter of that map and the
identity on new coordinates. The image of any supplied good neighborhood is a
neighborhood of zero. Continuity of the requested target curve then supplies
a real ball, and the positive half-radius gives an actual nonzero parameter
and preimage. Neither a continuous choice of preimages nor a limit choice is
assumed.

The vertex extension keeps the graph's test space fixed at the larger graph.
The block-diagonal base is injective on this space by the previously reviewed
`ExtendedRows` lemma even though it need not yet realize all new edges.
Openness retains that injectivity; finitely many open nonzero conditions retain
all old edges. The local Gram image supplies precisely the negative products
needed to cancel the added coordinate's contribution on every old nonedge.
The single small nonzero parameter is used exactly on required new edges,
and zero elsewhere. Both orderings of old nonedges are covered by the explicit
symmetric coordinate argument. The actual extended rows consequently realize
the complete pattern; only then is injectivity converted to the exact frozen
Strong Arnold predicate. Empty old graphs and zero ambient dimensions are
allowed throughout. Positivity follows from the unchanged Gram identity in
the final induction, and rank is bounded by the actual number of columns.

I read the complete sources and freshly recompiled these three unchanged files
with the pinned Lean runtime. The retained compiler logs show kernel trust and
the standard three axioms. These are local direct source checks with existing
pinned import objects; the independent fresh full-closure build and actual
Linux Comparator are separate gates. The final exact theorem compiled locally,
but its independent assembly review is assigned to other agents. Canonical
pages, original documents, frozen statements and permanent IDs are unchanged.
