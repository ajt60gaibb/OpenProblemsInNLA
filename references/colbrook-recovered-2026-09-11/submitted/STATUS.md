# Review status

## What PASS means

The new verification run uses exact rational arithmetic and checks concrete algebra, certificates, and matrix constructions. A PASS does not establish the novelty of a result, verify that an upstream problem was transcribed correctly, formally certify an all-orders proof, or constitute peer review.

| Result | New finite check | Remaining review |
|---|---|---|
| Unequal-bandwidth growth | PASS: 60 attaining matrices, support, admissible pivots, nonsingularity, recurrence identities | General front argument; definition of the supremum; source mapping |
| Cyclic-tridiagonal growth | PASS: 27 orders, structural zeros, corners, complete pivot paths, all intermediate growth | Universal upper bound; allowed ties and column-order conventions; source mapping |
| LSMR | PASS: Krylov iterates, rational feasible perturbation, all positive principal minors, approximation increase | Backward-error model and exact source match; independent proof review |
| Four-step Anderson bound | PASS: two rational counterexamples and a separate recurrence calculation | Source formula and exponent convention; analytic unbounded-ratio family; no asymptotic-rate conclusion |
| Entrywise inverse norm | PASS: class assumptions, exact inverses, parameterized identities | Entrywise order versus dominance-margin order; analytic infimum argument; source match |
| Random row deletion | No finite proof certificate | Entire concentration proof and normalization; original quantifiers; independent review |
| Universal row deletion | No finite proof certificate | Entire projection/existence argument and sharpness; source mapping; independent review |
| Right-inverse nonuniqueness | PASS: right inverses, Gram and kernel identities | Continuous p range, complete minimizer sets, distinction from a product objective, prior attribution |
| Rook-pivoting supplement | PASS: one order-five rational example | Partial lower bound only; no claimed optimality or matching upper bound |

## Most consequential scope limits

The LSMR proof uses the **spectral norm** and changes only the matrix, not the right-hand side. Its corrected certificate states

$$\mu(x_1)^2\le\frac{1979}{2000}<\frac{99}{100}<\mu(x_2)^2.$$

The Anderson result is a **four-step** counterexample. A single finite-step amplification does not settle the associated asymptotic convergence question.

The inverse-norm correction uses **entrywise ordering** of positive symmetric diagonally dominant matrices. It is not a counterexample to an unspecified stronger ordering of diagonal-dominance margins.

The row-deletion notes use the exact retention convention, variational singular value, normalization, and limits defined in their first section. They must not be reinterpreted using a different convention without proof.

The induced-norm result minimizes the norm of a **right inverse itself**. It is not a claim about minimizing the norm of its product with the original matrix.

## Current submission status

Prepared for independent review. Not peer reviewed, not formally proof-assistant certified, and not confirmed novel. The live repository and exact current identifiers were not retrieved during reconstruction. No GitHub issue or pull request, email, or paper has been submitted.
