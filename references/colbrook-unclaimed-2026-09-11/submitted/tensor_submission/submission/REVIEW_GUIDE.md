# Reviewer guide

Each manuscript should be assessed against the exact linked repository statement. The following points are the main scope and verification checks, not a substitute for a line-by-line proof review.

## TR06

Finiteness of average angular CP-decomposition conditioning under the hypotheses stated in the manuscript.

A bounded normalized semialgebraic decomposition graph and an area/volume argument.

Check generic identifiability, scaling and permutation quotients, the input probability measure, and the comparison of the derivative norm with the graph Jacobian.

Manuscript: `proofs/TR06.md`. Source: https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/tensor-computations/problem6.md.

## TR15

A counterexample to the stated Hankel-tensor eigenvalue-inclusion conjecture.

An exact construction in which the smaller tensor has positive eigenvalues and the larger tensor has eigenvalue -1.

Check the original indexing convention, tensor orders and dimensions, the precise eigenvalue definition, and the exact eigenvector substitution.

Manuscript: `proofs/TR15.md`. Source: https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/tensor-computations/problem15.md.

## TR17

The generic-rank target for odd-order Hankel tensors, as formulated in the manuscript.

Mode grouping, a commutator rank lower bound, and an exact nonzero minor, matched with the upper bound.

The claim is generic, not an assertion for every Hankel tensor. Check the base field, exceptional parameter cases, and the passage from the exhibited minor to a nonempty Zariski-open set.

Manuscript: `proofs/TR17.md`. Source: https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/tensor-computations/problem17.md.

## TR19

The discriminant-degree target stated in the manuscript.

A critical-point/discriminant calculation with boundary and multiplicity accounting.

Check incidence irreducibility, degree of the projection, boundary components, multiplicities, and all low-dimensional exceptions.

Manuscript: `proofs/TR19.md`. Source: https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/tensor-computations/problem19.md.

## TR20

Both discriminant-degree formulas stated in the manuscript.

Discriminant and intersection-theoretic calculations with boundary corrections.

Check that the computed divisor is the requested reduced discriminant, rather than a resultant with extra factors, and check multiplicities and exceptional dimensions.

Manuscript: `proofs/TR20.md`. Source: https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/tensor-computations/problem20.md.

## TR04

A tie-aware TT-SVD construction meeting the displayed pointwise strict inequality, with the qualifications in the manuscript.

An equality-case analysis and choices within tied singular subspaces.

This does not give a dimension-only constant uniformly below the existing worst-case factor. The ratio may approach that factor. Check zero-error and low-order cases and whether the intended problem demands a uniform improvement.

Manuscript: `proofs/TR04.md`. Source: https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/tensor-computations/problem4.md.

