# SP-12 independent preimplementation specification review

Reviewer: `/root/infra_audit`, an OpenAI Codex AI agent independent of the target specification author. Phase: specification. Verdict: **approve**.

I read the complete canonical README and exact specification and independently checked the mathematical representation before target Lean implementation. Infrastructure authorship does not make this reviewer an author of these problem specifications.

The proposed witness is a real symmetric PSD matrix in the exact off-diagonal sparsity class. Its diagonal remains unrestricted subject to PSD and SAP, and the specification keeps singleton, isolated, disconnected, and rank-zero cases.

The SAP clause exactly quantifies over real symmetric X, imposes ordinary AX=0, all scalar Aij*Xij=0, and diagonal Xii=0, then concludes X=0. It correctly distinguishes the two Hadamard constraints from ordinary matrix products.

The proper-coloring function definition gives the minimum number of colors concretely. A finite graph admits the injective n-coloring; a nonempty vertex set admits no zero-coloring. Consequently natural chi-1 is the intended subtraction, not an accidental truncation.

The witness formulation matches the source maximum-nullity inequality. Feasible nullities lie in the finite set 0,...,n. Feasibility is nonempty: a symmetric strictly diagonally dominant realization with nonzero edge weights can be chosen positive definite; invertibility then forces X=0 from AX=0, giving SAP. Therefore the maximum is attained, so the witness bound and maximum bound are equivalent.

No stronger graph family restriction or chromatic-minor statement replaces the target. The complete canonical README is retained byte for byte; actual matrix-rank, PSD and coloring definitions still require Lean boundary review.

This approval is specific to the following bytes and establishes specification fidelity only. It does not certify the cited resolution, a Lean proof, human peer review, or Linux Comparator execution. The implemented boundary still requires independent review.

- `eigenvalues-and-inverse-problems/SP-12/README.md`: `cdc8003bc5160604408ce6b95c344a4ea1b9bfbf8af0f99ae1e8e016648d53e1`
- `docs/lean/statements/SP-12/NUMERICAL_TARGETS.md`: `6dae7d486ecaeab1903b31e816e34f57fef417ef15627574f4c4a307b902cae7`
- `docs/lean/statements/SP-12/ORIGINAL.md`: `cdc8003bc5160604408ce6b95c344a4ea1b9bfbf8af0f99ae1e8e016648d53e1`
