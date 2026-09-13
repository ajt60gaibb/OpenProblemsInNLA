# RA-08 source correspondence at the statement boundary

The canonical original target is retained at
`randomized-and-low-rank-approximation/RA-08/README.md`, upstream commit
`5830ed4fb06da0659414a3deb2a40ad327aca052`. Read its complete statement and
Matthew J. Colbrook's complete authored manuscript
`references/colbrook-transfer-2026-09-11/manuscripts/03_concave_transfer_counterexamples.tex`,
especially Theorem 3.1 and its preceding derivative lemma. The complete
independent informal source review is also retained in that reference bundle.
All exact source byte hashes and Git blob identities are in `source-inputs.json`.

Colbrook retains authorship of the mathematical counterexample and its original
contour proof. Persson, Meyer and Musco retain the original matrix-function
transfer question and source attribution. George Stepaniants, Department of
Computing and Mathematical Sciences, California Institute of Technology,
Pasadena, California, USA, is the formalization author, with AI-agent assistance.
No George contact email is added. Source manuscripts keep their existing
licenses; the new code's Apache 2.0 license does not relicense those manuscripts.

| Complete source requirement | Exact formal boundary / pending proof |
| --- | --- |
| Every real symmetric ordered PSD pair, every n≥2 and 1≤k<n | `RealMatrix`, scoped actual Matrix PSD order, full `ConcaveSpectralTransferConjecture` quantifiers |
| Every continuous nonnegative nondecreasing scalar-concave function on the half-line | `AdmissibleFunction`, with no generic value-zero or operator-monotonicity premise |
| Every allowed ordered orthonormal eigendecomposition, including ties | Arbitrary `OrderedSpectralData`; `orderedSpectral_exists` and `orderedSpectral_semantics` are required proved bridges |
| Same eigenvectors for original and function truncations | `truncation` and `functionTruncation` use the same selected orthogonal matrix and zero omitted coefficients |
| Genuine spectral function and Euclidean operator norm | `functionalCalculus_spectral`, `spectral_tail_norms`, `operator_rayleigh_bound` |
| Source n=6, k=3, t=1/65536 rational witness | Exact `witnessU`, `witnessF`, `witnessApproximation`, `witnessMatrix`; `witness_data` proves admissibility |
| Exact fourth eigenvalue and both optimal tails | `witness_tail_data`, universally quantified over the actual allowed witness decompositions |
| Strict transformed error exceeding t | New finite polynomial route: `witness_spectral_location`, `minorant_scalar`, `minorant_functional_calculus`, `witness_rational_certificate`, `numerical_gap_positive` |
| Negative answer to the entire canonical implication | `counterexample` at epsilon zero, then unconditional `not_concaveSpectralTransferConjecture` |

The source witness is unchanged. The proof plan replaces its contour-remainder
lower bound with an exact degree-six scalar minorant and only three
matrix-vector products. The new rational gap is weaker than the manuscript's
published-in-repository bound but strictly positive. Neither that stronger
ratio, the ancillary Nyström identity, the nuclear-norm construction nor the
strictly-increasing extension is advertised among the fourteen exports. None
is required to negate the canonical all-pair, all-function implication.

The author agent `/root/formal_review_standards` drafted this boundary and the
polynomial route. The root coordinator supplied the complementary-compression
spectral-gap argument. Root and `/root/solved_statement_inventory` are assigned
to independently inspect the exact formal statements before implementation;
that does not erase the root coordinator's mathematical route contribution.
Final proof referee assignments must exclude the author and any eventual
mathematical coauthor. No approvals have been claimed at the statement freeze.

The campaign inspected Schiffer at `2938e277969c329caf154e48a3d8823f3635c7f1`
for statement/proof separation and Forsythe at
`8d1b0c0545a77b40245e84705aa7d273e6c81e62` for the numerical-target,
explicit-kernel LeanCert and Comparator workflow. No mathematical theorem
from either is an unproved premise. MI-26's real-function CFC interface and
MI-23's explicit Euclidean CLM norm provide repository API examples; their
proofs are not imported. The local statement runner is adapted from the
campaign's IS-03 statement runner and preserves fresh-prefix and pin checks.
Shared infrastructure and external source licenses retain their attribution.

Review follows all ten Tau Ceti angles as adapted by `docs/lean/REVIEW.md`,
with TauCetiReview pinned to `afb424eda89e8ac96d9eb69f6a88972055a4cd1b`.
The real v0.4 schema is pinned to formalization.yaml commit
`99c678e569c7c4c0772db297c5ddd5e4c9b6322e`. These are AI-agent reviews and
metadata, not official Tau Ceti execution, external human peer review, source
author endorsement, numerical oracle acceptance or historical priority claims.
