# TR-27 rank-three and square-nine proof: author evidence

Date: 2026-09-22. Authoring agent: `/root/canonical_inventory`. This is author evidence, not independent proof review or full-problem verification. The exact canonical statements were frozen after two independent reviews. Root separately scrutinized and approved the finite-set dual/contraction derivation before this implementation.

`NLA/TR27/RankWitness.lean` implements all three assigned frozen Challenge signatures: `witness_three_terms`, `square_nine_terms`, and `square_not_eight`. Its SHA256 is `bd7d4644ca96c951aaac781ed8c448d21bb20a49c26638079163c0c08e3db4da`. It contains 18 proved theorems and four linear-map definitions. There are no placeholders, custom axioms, native shortcuts or Challenge imports. Its dependencies are stable Independence, Geometry, their imported modules, and Mathlib; none was edited in this task. Frozen Definitions, Challenge and NUMERICAL_TARGETS hashes remain unchanged.

## Rank three

`cone_vector_parameter` treats every vector of the entire cone, including zero: it writes it as an unrestricted complex scalar times a curve vector, selecting an arbitrary parameter with scalar zero when needed. `curve_linearIndepOn` reindexes an arbitrary parameter finset of cardinality at most eight through the previously proved uniform independence. `independent_dual` extends a coordinate of `LinearIndependent.repr` from the finite span to the whole vector space, yielding exact delta values on all selected curve vectors.

The three-term expression follows from exact Algebra identities and proved whole-cone membership. For a hypothetical expression with at most two cone vectors, normalize each factor and combine its scalar with the expression coefficient. At least one of the three fixed parameters 1,2,3 is absent from those at most two parameters. Their union has at most five elements. Its delta functional at the missing fixed parameter evaluates the displayed three-term sum to one and the putative short expression to zero. Thus the cone rank is exactly three, with arbitrary complex coefficients and repetitions allowed.

## Nine-term upper expression

`square_nine_identity` expands the exact three-term expression using actual `TensorProduct.sum_tmul` and `TensorProduct.tmul_sum`. `square_nine_terms` reindexes the pair `(Fin 3 × Fin 3)` by the standard equivalence with `Fin 9` and proves cone membership for each factor. It has exactly the frozen double-sum formula and the unrestricted separate-factor `TensorRankAtMost` conclusion.

## Lower bound against every eight-term expression

`cone_square_parameters` independently normalizes both factors of every putative summand. A zero factor is retained with scalar zero, so no nonzero-factor premise is introduced. The coefficient becomes the product of the original coefficient and the two factor scalars. Repeated parameters remain allowed.

The left and right parameter sets are the images of the summand index set, each of cardinality at most eight. The explicit functional `witnessDual = (-1/3) • coordinate_0` has value one on the target vector. `contractRight` and `contractLeft` are actual tensor-product linear maps composed with the standard unit isomorphisms. Applying them to the putative equality puts the target vector into both parameter spans separately.

Choose finite expansions in those spans. `witness_expansion_support` proves at least three nonzero coefficients in each: fewer would directly construct the already-excluded rank-at-most-two cone expression by enumerating its support. Extend each independent coordinate to an ambient dual as above. `pairDual` uses `TensorProduct.map` and the ordinary scalar tensor unit isomorphism, so on `x⊗y` its value is exactly `f(x)g(y)`.

For each pair of nonzero expansion coefficients, its dual product evaluates the target square nontrivially. If that parameter pair were absent from the original summand-pair image, every proposed summand would evaluate to zero. Therefore the Cartesian product of the two nonzero supports is contained in the image of the original summand pairs. That image has cardinality at most the number of summands, even with repetitions and zero coefficients. Its cardinality is thus at most eight, whereas the support product has at least `3*3=9` elements. This contradiction proves the frozen `square_not_eight` with independent left and right factors; no symmetric or merged-mode restriction occurs.

## Local checks and remaining gates

Run `python3 reviews/rank-author-evidence/typecheck.py` to reproduce the recorded macOS development check. It compiles six source modules and the all-declaration axiom audit into `/private/tmp/nla-tr27-rank-build`; all seven runs exit zero without warnings. All 22 new declarations have transitive axiom closures contained in `propext`, `Classical.choice`, and `Quot.sound`, including every imported geometry and independence dependency used by the final results.

No approximate numerical computation or interval certificate is used, and LeanCert was not invoked for these algebraic proofs. Independent proof review, authoritative Linux/kernel-trust checks, and Comparator remain outstanding. This module proves the assigned cone-rank and actual tensor-rank statements; the full canonical projective correspondence and border-rank statements remain separate campaign obligations. No canonical page, shared metadata, shared build driver, or stable source module was edited.
