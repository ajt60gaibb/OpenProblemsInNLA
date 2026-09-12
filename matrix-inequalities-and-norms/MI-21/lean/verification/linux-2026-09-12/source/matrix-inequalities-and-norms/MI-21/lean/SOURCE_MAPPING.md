# MI-21 source mapping and candidate choice

Authoritative upstream source revision: `e7252e5307781a7c897bca6cb124f6ab838f6809` (`nla-upstream/main` when this worktree was created). Source hashes are in [source-inputs.json](verification/source-inputs.json).

| Source clause | Formal definition or export | Exact scope |
|---|---|---|
| Canonical complex positive definite families and all dimensions | `Mat`, `Matrix.PosDef`, `GeometricMeanNormConjecture` | All positive `m,n`, all `Fin m` families; no reality or commutativity restriction |
| Canonical spectral real powers and weighted mean | `spectralPower`, `geometricMean` | Actual `CFC.rpow`, including the two negative half powers |
| Canonical sums and noncommuting right-hand product | `leftMatrix`, `rightMatrix` | Original factor order and real exponent arithmetic |
| Every unitarily invariant norm | `IsUnitaryInvariantNorm`, `operatorNorm_isUnitaryInvariant` | Full complex norm axioms, both independent unitary factors; actual Euclidean operator norm is a proved admissible witness |
| Colbrook Theorem 1.1 and its proof | `witnessC`, `witnessE`, `witnessS`, `witnessA`, `witnessB` | Exact rational order-two matrices |
| Source displayed exact left matrix and eigenvector | `witnessL`, `witnessVector`, `witnessEigenvalue`, `counterexample` | Actual CFC equality and genuine operator norm, not a substituted candidate expression |
| Negative answer to original universal question | `not_geometricMeanNormConjecture` | Full negation, including all original parameters and norms |

The complete source manuscript and canonical target were read. All of its counterexample can be checked using finite order-two algebra, CFC root uniqueness, and one rational norm gap. No published analytical result is taken as an axiom.

The three initially requested alternatives were also read in full at this upstream revision:

- **SF-01:** an affirmative result requiring rational Bernstein-class closure, resolvent comparison, the M-matrix/positive-weight criterion and induction over genuine Newton iterates. Its proof is not a small finite certificate.
- **MF-16:** a negative Jacobian alone cannot refute uniqueness without formalizing the degree theorem; the independent alternative requires proving existence of an additional root from a two-dimensional contraction/interval certificate. This is viable later, but has a larger initial analytic obligation.
- **MI-13:** its short repository reduction depends on the full complex refined commutator inequality. Formalizing only the reduction would not settle the canonical target.

MI-21 was selected as the more economical complete next target. Additional candidates MI-23, MI-24, MI-28, SP-04, RA-07, RA-09 and RE-05 were inspected for scope; none replaces or changes its existing canonical target. No new solution or status change is asserted by this stage-one project.

Mathlib APIs used for the statement boundary come from the pinned local primary sources: `Analysis.Matrix.Order`, `Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic`, and `Analysis.CStarAlgebra.Matrix`. The operator norm is explicitly `Matrix.toEuclideanCLM`; matrix powers are explicitly `CFC.rpow`. The earlier MI-29 statement boundary was consulted as a compatible CFC API example, and RA-03's package configuration was copied with an MI-21 package name. No mathematical proof code from either project is copied or assumed.
