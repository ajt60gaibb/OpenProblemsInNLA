# MI-19 statement and numerical obligations

Statement draft prepared before proof implementation, 12 September 2026.
Formalization author: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. The counterexample and informal proof are due to Matthew J. Colbrook; their attribution remains in the canonical entry and source manuscript. AI assistance is used for the formalization. No human review or completed Lean verification is asserted at this stage.

The source of truth is the original Problem statement in `../README.md`, pinned at upstream commit `5adea969c17391693978ada2674d25bb5c3daeb1`. The mathematical source is Theorem 1.1 and its proof in `matrix-inequalities-and-norms/MI-19/solution.tex` at that same commit. Source hashes will be frozen with the statement-review request.

## Exact formal target

`NLA.MI19.SubsetConjecture` quantifies over every natural dimension n≥2, every complex Hermitian positive semidefinite n×n matrix A, every real q with 0≤q≤1, and every nonempty proper subset S of the ordered index set. `Matrix.PosSemidef` includes the Hermitian condition and nonnegativity of the quadratic form on all complex vectors; there is no replacement by entrywise nonnegativity or by a real-only input class.

`inversionCount σ` is the cardinality of the set of pairs `(i,j)` in the full original ordering with i<j and σ(i)>σ(j). `qPermanentTerm q A σ` is `(q:ℂ)^inversionCount σ * ∏ᵢ A(i,σ(i))`. The exponent is a natural number, hence the convention 0^0=1 is retained. `qPermanent` sums over all permutations of Fin n. `restrictedQPermanent` sums the identical terms over permutations satisfying `S.image σ = S`; this is setwise preservation. It is not pointwise fixation except for a singleton, and it is not a product of q-permanents on smaller blocks. The inversion count is not recomputed after restriction.

Complex order is mathlib's `ComplexOrder`: z≤w iff z.re≤w.re and z.im=w.im, and similarly for strict order. Thus it agrees with ordinary real order on real-valued expressions. The counterexample export explicitly includes zero imaginary parts of both sums, in addition to its complex rational gap and strict inequality. The negative resolution therefore cannot result merely from incomparable nonreal values. No extra assumption that these expressions are real is added to the conjecture's premises.

Paper indices 1,2,3,4 correspond to Lean's Fin 4 indices 0,1,2,3. In particular, the interior singleton S={2} is `witnessSubset={1}`, not the first index. No row or column is reordered.

The Comparator exports are (1) a fully admissible exact counterexample including the Gram identity, Hermitian/PSD hypotheses, allowed q, nonempty proper subset, reality of both sums, exact gap, and strict reverse inequality; and (2) the negation of the full universal conjecture. Proving the latter settles the original target negatively. The manuscript's rank-two assertion and positive-definite perturbation extension are optional stronger results and are not claimed formalized by this project.

## Numerical objects fixed before proof

All entries below are exact integers or rationals interpreted in ℂ or ℝ as indicated. There are no floating-point inputs.

The complex matrix `witness` is the real matrix

```
A = [[170,  1, 167, 170],
     [  1,  1,  -2,   1],
     [167, -2, 173, 167],
     [170,  1, 167, 170]].
```

The complex 2×4 matrix `gramFactor` is

```
X = [[13, 0, 13, 13],
     [ 1, 1, -2,  1]].
```

The real scalar `witnessQ=7/8`. The finite set `witnessSubset={1 : Fin 4}`.

## Numerical and mathematical obligations

1. Verify `Xᴴ X=A` exactly and derive that A is Hermitian positive semidefinite over complex vectors. This is a Gram argument, not numerical eigenvalue sampling.
2. Verify 0≤7/8≤1, and that the designated interior singleton is nonempty and proper. The full canonical dimension condition 2≤4 is proved when the universal conjecture is instantiated.
3. Evaluate the full q-permanent at this fixed witness and the subset-preserving sum using the full ordering. There are exactly 24 permutations and six preserve this singleton. Prove both expressions are real, so the final comparison is the ordinary scalar comparison intended by the canonical statement.
4. Prove the exact complex rational identity

   `qPermanent witnessQ witness - restrictedQPermanent witnessQ witness witnessSubset = (-3235575/16384 : ℂ)`.

5. With LeanCert in explicit kernel mode, certify the scalar real inequality `(-3235575:ℝ)/16384 < 0` (or an equivalent positive-gap expression obtained by exact algebra). Transfer it through the proved equality and zero imaginary parts to the strict complex-order inequality required in `counterexample`.
6. Specialize `SubsetConjecture` at n=4, A=witness, q=witnessQ and S=witnessSubset. Its asserted reverse weak inequality contradicts the strict counterexample; derive `not_subsetConjecture` with no additional mathematical assumptions.

For an optional compact computation route, the informal source supplies exact polynomial identities before q is specialized. The full polynomial has coefficients

`115600q^6 + 4886140q^5 + 9568969q^4 + 4712758q^3 - 199231q^2 + 4886140q + 4999700`,

and the restricted polynomial is

`4999700q^5 + 9482260q^4 + 4741130q^3 + 4741130q + 4999700`.

Their difference factors as

`q(q+1)(115600q^4 - 229160q^3 + 315869q^2 - 344241q + 145010)`.

These are proposed exact arithmetic reductions, not imported axioms. The implementation may instead evaluate only q=7/8 if that gives a smaller kernel proof. Either route must establish the actual permutation sums, not merely assume the polynomial certificate or prove the scalar gap in isolation.

## Computation minimization and trust boundary

This is a finite rational counterexample. First use exact permutation enumeration, matrix multiplication, and scalar simplification. LeanCert then handles one scalar inequality. There is no need to approximate eigenvalues, explore q in an interval, cover a matrix domain, or subdivide any interval. A point witness suffices to disprove a universal conjecture.

Use a proof-producing finite-permutation enumeration or a checked enumeration equivalence. Ordinary native execution or an external enumeration script may help discover a certificate but must not support the target through an additional axiom. Only a subset of `propext`, `Classical.choice`, and `Quot.sound` may occur transitively in the final exports. No `sorryAx`, custom unproved lemma, or additional trust in native execution is accepted.

`Challenge.lean` deliberately contains statement placeholders for independent review and Comparator. The future solution must never import that module. There is no solution implementation at this stage. Definition and Challenge changes after statement review require re-review; a later build alone cannot certify correspondence to the original target.
