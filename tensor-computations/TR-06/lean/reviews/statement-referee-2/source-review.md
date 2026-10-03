# TR-06 independent pre-statement review, referee 2

Date: 24 September 2026. Reviewer: independent AI agent `/root/tr06_statement_referee_2`. Phase: mathematical source, exact-target requirements, and pinned-library feasibility. This review did not consult or rely on existing PASS reports. Reviewed-byte hashes are in `source-hashes.json`. No Lean Challenge, Solution, numerical target inventory, Comparator execution, or kernel run was available to this reviewer at this phase. Thus this is **not approval of a formal statement or formal verification**.

## Verdict

The source proof strategy is mathematically credible, with no counterexample or fatal argument gap found on this independent reconstruction. The complete TR-06 target is substantially larger than its one-dimensional Gaussian integral. A Lean theorem that assumes the finite graph volume, finite angular link integral, or a package of cone/polar hypotheses without deriving them for the actual identifiable-tensor model does **not** verify TR-06. Do not promote status on that basis. Await exact Challenge signatures and the definitions they transitively use before statement approval.

## Reconstruction and sensitive bridges

1. Work in the real Frobenius tensor space of dimension the product of the mode sizes. The complex generic-identifiability hypothesis concerns actual complex rank-one decompositions modulo permutation, on a nonempty relative Zariski-open subset of the rank-r secant image/closure. It must not be represented by an arbitrary predicate that already implies analytic regularity or integrability.
2. The nonzero rank-one cone has dimension `1 + sum_j (n_j - 1)`. The ordered addition map on its r-fold product has generically finite fibers under the assumed identifiability, so the image has dimension `k = r * (1 + sum_j (n_j - 1))`. A real regular full-dimensional point exists because real factor parameters are Zariski dense in the complex parameter space: a nonzero polynomial Jacobian minor and the pullback of the exceptional locus cannot vanish on every real parameter. This gives a real open regular locus. A proof must additionally show that removing the exceptional image has zero k-dimensional induced volume in the canonical real locus. Restricting a complex dense-open result to real points without the density/dimension argument is insufficient in general.
3. On the regular identifiable cone, the ordered map has r! local smooth branches. It is not globally one-to-one. The external preprint's Proposition 2.2(4) incorrectly calls the ordered map a global diffeomorphism, contradicted by its own permutation-fiber statement; do not import that assertion. The TR-06 manuscript correctly uses local branches and is not damaged by that source typo.
4. The unit link is a smooth bounded semialgebraic manifold of dimension k-1, since the radial direction gives transversality. Its normalized-decomposition graph is semialgebraic via polynomial relations and existential projection with strictly positive normalization variables. This requires real quantifier elimination / Tarski-Seidenberg or a proved substitute, not merely the notation `∃` in the set definition.
5. Minimality prevents proportional summands: two proportional terms can be replaced by one term or canceled. Hence normalized summands are distinct and permutations remain distinct. Strictly speaking r! is more than is needed: finite nonempty local fibers suffice for the graph inequality.
6. Boundedness of the normalized graph, semialgebraicity, and graph dimension k-1 give finite (k-1)-Hausdorff measure. This is the central imported geometric theorem, not an elementary compactness argument. The graph need not be closed. Boundedness alone does not prove finite volume.
7. For each branch, with Euclidean metrics on both factors, the graph derivative has Gram matrix `I + Dg* Dg`. The graph Jacobian dominates the operator norm of `Dg`. A countable local cover and disjoint measurable partition give the integrated inequality without counting overlaps. A finite semialgebraic stratification is an alternate route. Lower-dimensional discarded strata need proved measure zero.
8. Positive radial scaling leaves normalized summands unchanged. The intrinsic derivative vanishes in the radial direction; orthogonal radial/tangential splitting gives exact operator-norm agreement with the link derivative, and scaling contributes t^(-1). The cone polar Jacobian is t^(k-1). Tonelli gives the unnormalized expectation numerator as the finite angular integral times `integral_0^infinity t^(k-2) exp(-t^2/2) dt`.
9. Positivity and finiteness of the normalizing constant require nonempty positive-volume smooth link plus its finite volume. Division by an arbitrary assumed Z, or a default zero normalizer from an empty locus, would make a spurious probability law. Restore the removed null set explicitly.

The external theorem citation was checked directly: Hardt, Lambrechts, Turchin, and Volic, *Real homotopy theory of semi-algebraic sets*, Theorem 2.4, states bounded semialgebraic sets of dimension at most k have finite k-dimensional Hausdorff measure. Primary PDF: https://msp.org/agt/2011/11-5/agt-v11-n5-p01-s.pdf . The tensor-model source was checked directly at https://arxiv.org/pdf/1903.05527 , Definition 1.3, Conjecture 1.10, and Proposition 2.2. These are informal external references, not permissible new Lean axioms.

## Formal-statement traps to reject

- Plain Lean function spaces `ι → ℝ` have the supremum norm; plain product spaces also do not automatically have the Euclidean product norm. Use `EuclideanSpace ℝ` / `PiLp 2` or prove explicit isometries for the tensor Frobenius and ordered-product Frobenius norms.
- `fderivWithin` in the ambient tensor space is not an automatic intrinsic derivative on a lower-dimensional submanifold. Such sets need not have `UniqueDiffWithinAt` in the ambient model, and default derivatives can erase the target. Use intrinsic tangent derivatives with the induced norm, or prove an equivalent derivative construction.
- Lean's real-valued Bochner integral is defined even for nonintegrable functions (with a default value). A real statement merely comparing that integral to some finite real quantity does not prove finite expectation. Use `Integrable` / `HasFiniteIntegral`, or a nonnegative extended integral `< ∞` with all measurability and density correspondence proved.
- Use Euclidean Hausdorff measure `μHE[k]` or track the normalization factor. Raw `μH[k]` is defined by diameter powers and does not have the source's Euclidean normalization in every dimension. Normalizer cancellation permits a consistent fixed-dimensional rescaling, but the polar formula relates different dimensions and cannot silently drop relative constants.
- An `IsProbabilityMeasure` premise on an arbitrary supplied measure does not identify the volume-Gaussian law.
- A global arbitrary choice of ordering is not globally smooth in general. Its derivative norm must be proved independent of choices and locally agrees with legitimate branches; a locally constant permutation isometry is the relevant argument.
- Do not replace the derivative of individually normalized summands by ordinary conditioning divided by a scalar, and do not replace volume sampling by Gaussian factors.

## Exact numerical content

No numerical approximation, interval covering, or computed transcendental constant is needed in the manuscript. Both radial exponents are symbolic natural dimensions and satisfy the convergence threshold exactly. LeanCert may be installed with kernel trust as requested, but performing an irrelevant numerical certificate does not certify any of the geometric bridges. A numerical target inventory should say this plainly.

## Pinned Mathlib audit

Located the existing local Mathlib checkout at `/Users/ajt253/Documents/ConvergenceOfAAA_chatgpt6/lean/.lake/packages/mathlib`, git `0df444a360eaa60ab8c11dca51a86af692955474`, Lean 4.33.1. This matches the Mathlib pin in the repository's MI-23 lock file. Read-only searches and source inspection found:

- `Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`, `integrableOn_rpow_mul_exp_neg_mul_sq` at line 92: the radial convergence theorem already exists for any exponent greater than -1 and positive Gaussian coefficient. Reuse it.
- `Analysis/InnerProductSpace/PiL2.lean`: correct Euclidean-space representation and norm identities.
- `MeasureTheory/Measure/Hausdorff.lean`: raw Hausdorff measure and scaling/isometry facts.
- `Geometry/Euclidean/Volume/Measure.lean`: `MeasureTheory.Measure.euclideanHausdorffMeasure` and normalization to Euclidean volume. This is a better volume target than raw Hausdorff measure.
- `Analysis/InnerProductSpace/NormDet.lean`: norm determinant, singular-value product, and **linear-map** Euclidean-Hausdorff volume change. Useful algebraic scaffolding, but not a nonlinear submanifold area formula.
- `MeasureTheory/Function/Jacobian.lean`: change of variables for differentiable injective `E → E` on equal-dimensional Euclidean spaces. This alone does not provide an area formula for `E → F` graph embeddings or induced manifold volume.
- Available manifold / inverse function / tangent / sphere APIs supply calculus pieces.

A full-source case-insensitive search for `semialgebraic`, `semi-algebraic`, `semi_algebraic`, `Tarski.Seidenberg`, `area formula`, and `coarea` returned no matches. Additional source search did not locate a nonlinear Euclidean-Hausdorff graph area formula. This is evidence of a major missing library development, not a proof that no alternate derivation exists. At least semialgebraic projection/dimension/finite-volume foundations, the tensor regular-locus bridge, and intrinsic area/polar integration need real proofs before full-target certification. Treating these as parameters or axioms cannot meet the user's complete-target and permitted-axiom requirements.

## Remaining review requirements

Review the actual definitions, exact Challenge theorem, numeric inventory, and source hashes before approving statement correspondence. After implementation, independently inspect the proof path and imports and inspect actual Comparator/kernel/axiom logs. None of those approvals or runs is claimed here.
