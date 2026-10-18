# SP-11 noncancellation: implementation route and pitfalls

Researcher: `/root/lean_verification`, Codex AI agent, 17 October 2026. This is
a proposed proof decomposition, not a proof of the remaining SP-11 theorem.

I read the exact [Hall v1, Sections 5.4–5.6](https://arxiv.org/html/2601.01211v1#S5.SS5).
Lemma 5.14 selects a unique maximal nonzero coloring for an edge/diagonal
double-root garden in a greedy order. Vertex classes take priority before later
classes, then smaller coordinate tuples take priority. Greedy child/insertion
bounds make the prescribed colors admissible. Repeated occurrences use the
same tensor variables; distinct occurrence variables would change the proof.
The same-root cap is a separate case. The source's unused weak-success
parenthetical is not a substitute for noncancellation. Proposition 5.12 needs
the earlier-root restriction already present in Corollary 5.13. These source
observations motivate the following implementation design.

## Proposed formal decomposition

1. Expand the actual determinant-minor `polynomialLSS` recursion into a finite
   signed sum indexed by conduit colorings. Each term should be expressed as
   `MvPolynomial.monomial exponent coefficient`, where `exponent` is a sum of
   single-variable exponents over **node occurrences**, and variable keys are
   the existing shared `Sigma vertex CoordinateSubset` values. Zero terms can
   be retained with coefficient zero. Establish this equality for the actual
   recursive polynomial; a separately defined garden cannot be assumed equal.
2. Define a canonical coloring on the finite double-root tree. Use the actual
   sorted predecessor list position on ordinary child conduits, and the sorted
   augmented list position for an earlier adjacent root. The equal-root case
   uses the first free cap color. Prove every node's incident colors distinct
   using `OrderedGreedy.prior_length_lt_insertionPosition` and the dimension
   bound. This supplies a nonzero signed coefficient.
3. Induct over vertex classes in increasing order. The invariant must recover
   **individual conduit choices** from equality of earlier-class exponent
   histograms, rather than merely assume that equal products have equal factors.
   With those earlier choices fixed, an occurrence of the next class has fixed
   lower colors and a lower bound on its upward color from the earlier siblings.
   Each occurrence's variable weakly worsens from its canonical choice.
4. Apply `occurrenceExponent_eq_iff` in the new `MonomialProducts.lean` to
   recover all those choices. If any strictly worsens, `occurrenceExponent_lt`
   makes the entire same-class exponent histogram strictly worse. The lemmas
   require no distinctness of variable names, so they address the repeated-label
   compensation problem. Later classes cannot repair the first class mismatch
   under a vertex-first lexicographic order.
5. This gives uniqueness of the full exponent among nonzero summands. Apply
   `coeff_sum_monomial_of_unique`, then
   `sum_monomial_ne_zero_of_unique`. This coefficient argument avoids a separate
   leading-coefficient development for the full polynomial.

For an earlier/later root pair, the exceptional later root has no unresolved
choice after all earlier classes are fixed. For equal roots, both cap-adjacent
factors must be treated together. Track the determinant permutation signs in
the expansion; nonzero is sufficient, so a convention-induced global sign is
harmless once proved consistently.

## Pinned Mathlib APIs checked locally

- `Finsupp.Lex.single_strictAnti`, `single_le_iff`, and `single_lt_iff`:
  smaller variable indices give greater single-variable monomials.
- `MonomialOrder.lex` and its additive `toSyn`; `Finset.sum_lt_sum` makes a
  pointwise weak exponent comparison strict when at least one occurrence is
  strict. These are the implementation of the new product-order helpers.
- `MvPolynomial.monomial_sum_prod` combines products of signed monomials.
  `coeff_sum`, `coeff_monomial`, and `Finset.sum_eq_single` isolate a unique
  contribution. The new helpers also allow zero-coefficient duplicate exponents.
- If a leading-term API is preferred, the pinned
  `Mathlib.RingTheory.MvPolynomial.MonomialOrder` supplies `degree_sum_le`,
  `coeff_eq_zero_of_lt`, `leadingCoeff_add_of_lt`, `degree_prod`,
  `coeff_prod_sum_degree`, and `leadingCoeff_ne_zero_iff`. The zero polynomial's
  ordinary degree is zero, so `withBotDegree` or explicit nonzero conditions are
  needed in proofs relying on degree strictness.
- `Mathlib.Data.Sigma.Order` supplies a lexicographic order on `Lex (Sigma ...)`.
  Coordinate-subset fibres need a lexicographic order on their increasing tuple,
  not the default pointwise order on functions. Finite variable types satisfy
  the reverse-well-foundedness condition needed by `MonomialOrder.lex` once an
  appropriate linear order has been installed or transported.

The still-missing work is the exact expansion, admissibility and classwise
rigidity induction. The generic product/unique-coefficient helpers do not
establish any of those graph-specific hypotheses and must not be described as
the unique-monomial theorem itself.

## Simpler selected route: canonical-exponent equality only

The coefficient-isolation conclusion needs only that no other nonzero coloring
has the **same exponent** as the canonical coloring. It does not need a proof
that the canonical exponent is greatest. This removes the need to construct a
global lexicographic order on the dependent variable type.

Assume an arbitrary nonzero coloring has that same full exponent. Induct over
vertex classes. Equality of full exponents implies equality after applying any
natural-number weight to the variables. Choose a weight supported only on the
current vertex class, equal there to the sum of the coordinate subset's entries.
All lower conduits have already been recovered by the induction, so the weight
of each occurrence equals a fixed lower-coordinate sum plus its upward color.
The earlier-sibling restrictions give the canonical upward color as a lower
bound for every occurrence. Equal total weights and these pointwise lower
bounds force equality at every occurrence; repeated names cannot compensate.
The same-root cap case uses both occurrences together. At the exceptional later
root in the distinct-root case, all incident choices have already been fixed.

`Finsupp.linearCombination ℕ weight` and its `map_sum` /
`linearCombination_single` API turn exponent equality into weighted-sum equality
directly. A finite-sum strict-monotonicity argument supplies pointwise equality.
The coordinator owns the separate `HistogramRigidity.lean` helper for this
route. The above generic lexicographic helpers remain valid, but are not needed
for the proposed equality-only class induction. The exact tree expansion and
its induction invariants remain mathematical proof obligations.
