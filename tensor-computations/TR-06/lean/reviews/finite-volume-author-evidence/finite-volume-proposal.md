# TR-06 bounded graph finite-volume: proposed next statements

Prepared 2026-09-24 after completion of the rectangular immersion area proof. This is a statement/proof-route proposal for independent review, not a claim that semialgebraic foundations have been implemented.

Pinned API basis: Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. New proved area artifacts are in `/private/tmp/tr06-proof-area/FINAL-EVIDENCE.json`. Their exact `induced_volume_chart` declaration is complete; whole TR-06 remains incomplete.

## What is actually now available

`NLA.TR06.Area.immersion_area` proves the exact Euclidean Hausdorff area formula for any injective map with an injective within-derivative at every point of a measurable domain. It covers rectangular maps and infinite-volume domains. The new `euclidean_image_le_of_lipschitzOn` already supplies the inequality needed for finite-volume estimates. These two facts remove the previous nonlinear area gap, but do not prove the needed uniform tameness of a bounded graph.

The source manuscript's normalized graph lives over a smooth regular locus and already has smooth local branches. Therefore **the next finite-volume theorem can be restricted to bounded smooth semialgebraic embedded manifolds**. Finite smooth stratification of every semialgebraic set is not needed for this one graph-volume step, provided the full-measure regular-locus theorem has separately discharged the singular/exceptional part. This is a dependency reduction, not an extra final-target hypothesis.

## Proposed analytic statement A: bounded overlap of Lipschitz parametrizations

Let E and F be finite-dimensional real inner-product spaces with their Borel measurable structures, m = finrank R E, K : NNReal, B : Nat, V : Set E, t : Nat → Set E, and f : Nat → E → F. Assume:

1. `volume V < ∞`;
2. every `t j` is measurable and `t j ⊆ V`;
3. every `f j` is `LipschitzOnWith K` on `t j`;
4. for every `x : E`, the ENNReal multiplicity `∑' j, (t j).indicator (fun _ => 1) x` is at most `B`.

Then prove the exact quantitative inequality

```
(μHE[m] : Measure F) (⋃ j, f j '' t j)
  ≤ (K : ENNReal)^m * (B : ENNReal) * volume V
```

and hence finite measure. No measurability of the images is required for the upper bound. This is a useful theorem independent of semialgebraic geometry; its hypotheses must be constructed, never supplied in `finite_angular_mean` or hidden in a replacement problem definition.

Pinned tools: `measure_iUnion_le`, new `euclidean_image_le_of_lipschitzOn`, equality of μHE[m] to domain volume, `MeasureTheory.lintegral_tsum` (`Integral/Lebesgue/Add.lean:360`), `lintegral_indicator`, and ENNReal multiplication of finite factors. This proof appears small and directly implementable.

Statement A has no injectivity assumption. The application will derive its multiplicity hypothesis from injectivity and a uniform projection-fiber bound.

## Proposed analytic statement B: translate a projection-fiber bound

Let π : F → E, t j and f j be as above, and suppose:

- `π (f j x) = x` for x ∈ t j;
- the image sets `f j '' t j` are pairwise disjoint;
- all those images are contained in S;
- every finite set of distinct elements of `{z ∈ S | π z = x}` has cardinality at most B, uniformly in x.

Then the indicator multiplicity in A is at most B. Prove it first for finite index sums: assign to every j with x∈t j the point f j x; disjointness makes this assignment injective into the fiber. Pass from finite sums to `tsum` by `ENNReal.tsum_eq_iSup_sum`. The formulation by finite-subset cardinality avoids silently using `Nat.card`, which is zero on infinite types.

A/B together yield a coordinate-projection finite-volume theorem once the graph is covered by finitely many projection families. Summing a finite number of finite bounds is immediate. No full coarea or Crofton formula is needed.

## Proposed geometric statement C: uniform projection charts

Let S ⊆ R^N be a smooth embedded m-dimensional manifold, with m≤N, and let the finite family π_I consist of coordinate projections onto m coordinates. There exists K<∞ depending only on N,m and a partition of S into finitely many measurable sets S_I such that each S_I admits a countable disjoint measurable partition P_I,j with:

- π_I is injective on P_I,j;
- its inverse f_I,j : π_I(P_I,j) → P_I,j is K-Lipschitz;
- π_I(P_I,j) is measurable.

One must state this using actual embedding charts and their injective derivatives, rather than a tangent field with assumed finite volume. At each point, select a coordinate projection whose restriction to the tangent space has a uniformly bounded inverse. Obtain this finite-dimensional bound by compactness of orthonormal m-frames and the fact that an injective N×m matrix has a nonsingular m-row minor. No optimal constant or Cauchy–Binet identity is necessary. The inverse-function theorem and continuity then give a convex projection-coordinate ball with inverse derivative bound at most twice the selected bound. The mean-value Lipschitz theorem applies there. A countable open cover and disjoint source refinement give the required P_I,j.

This is implementable from the pinned calculus/topology infrastructure but appreciably larger than A/B. The matrix-minor existence and compact orthonormal-frame uniform bound still need Lean proofs. Existing `Matrix.rank_eq_finrank_span_row`, basis extraction, determinant/inverse, compactness and mean-value APIs are relevant; there is no completed packaged C theorem at the audited pin.

If S is bounded, its projections fit in one finite-volume ball or box V. If each selected regular-projection locus S_I also has uniformly finite projection fibers, A/B prove μHE[m](S)<∞.

## Precise remaining tame-geometry statement D

For a set S ⊆ R^N defined by a first-order formula over real polynomial equalities and strict inequalities, and a linear map π : R^N → R^m, let R be the subset of S where S is a smooth m-manifold and π restricts locally to a diffeomorphism. Prove:

```
∃ B : Nat, ∀ y : R^m,
  every finite subset of {x ∈ R | π x = y} has cardinality ≤ B.
```

The formulas defining S may quantify over auxiliary real variables. For the normalized tensor graph these include positive summand-norm variables and eliminated unnormalized summands. The regular locus can be expressed by the first-order derivative/locally-injective criterion, but proving the definability of its tangent/local differential data must be done; it cannot simply be asserted.

D follows mathematically from real quantifier elimination plus semialgebraic uniform finiteness: the displayed fibers are discrete definable sets. The key word is uniform. A finite fiber at each y is not enough; the number can diverge with y for a nontame bounded smooth set. Infinite discrete nonclosed fibers are also possible without tameness.

There is no audited implementation of D in pinned Mathlib or the pinned Schiffer/Forsythe reusable sources. The further exact searches in `Mathlib/ModelTheory`, `AlgebraicGeometry`, `Algebra/Polynomial`, `LinearAlgebra` found no real-closed-field quantifier-elimination, multivariate geometric Bezout, or semialgebraic uniform-finiteness API. `Presburger/Basic.lean` mentions future quantifier-elimination work, which is unrelated. Therefore D is a new foundational task; I cannot present the complete semialgebraic finite-volume route as already closed.

## Smallest honest endpoint

The smallest immediately implementable next component is A plus B. C is the next purely geometric component. D remains the serious algebraic/model-theoretic blocker; proving full cell decomposition would close it but is not a short addition. A specialized algebraic alternative could replace D with a degree bound on regular isolated solutions of the normalized tensor-graph equations, but this still requires elimination and a genuine uniform multivariate intersection bound. A univariate root bound, pointwise generic identifiability, or the newly proved polynomial-null lemma alone does not establish that bound.

The suggested next review boundary is A/B first. Their assumptions are legitimate intermediate lemmas and must never be promoted to assumptions of the frozen TR-06 theorems. To claim complete graph finite volume, the actual graph must be shown to satisfy C/D from its polynomial tensor relations and the original generic-identifiability hypothesis.

Primary source confirmation: Hardt–Lambrechts–Turchin–Volić, *Real homotopy theory of semi-algebraic sets*, [Theorem 2.4, page 2482](https://msp.org/agt/2011/11-5/agt-v11-n5-p01-s.pdf), states bounded semialgebraic sets of dimension at most k have finite k-Hausdorff measure, and refers to Federer and van den Dries for its proof. The theorem's citation is not a formal axiom or a Lean implementation. All proposed proof decomposition above is our own planning inference.
